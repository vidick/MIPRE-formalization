/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ValueStability
import MIPRE.Foundations.POVMMix

/-! # Game-value bounds for actual question-indexed replacements

Acceptance is compared before relabelling the outcomes. This permits a common
answer alphabet without assuming that same-party squared distance contracts
under coarse-graining.
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {X Y A B C H K : Type*}
  [Fintype X] [Fintype Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Relabelling a measurement pulls the acceptance predicate back exactly. -/
theorem testAcceptance_map_left (ψ : H × K → ℂ) (D : A → B → Bool)
    (M : POVM C H) (N : POVM B K) (f : C → A) :
    testAcceptance ψ D (fun a => ((M.map f).mats a).val) (fun b => (N.mats b).val) =
      testAcceptance ψ (fun c b => D (f c) b)
        (fun c => (M.mats c).val) (fun b => (N.mats b).val) := by
  unfold testAcceptance
  rw [Finset.sum_comm]
  simp_rw [sum_bornProb_mapA M f]
  exact Finset.sum_comm

/-- A projective replacement may be relabelled into a larger answer alphabet
without an answer-cardinality cost in the acceptance estimate. -/
theorem testAcceptance_stability_map_left (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (D : A → B → Bool) (M R : POVM C H) (N : POVM B K) (f : C → A)
    (hM : IsPVM fun c => (M.mats c).val) (hR : IsPVM fun c => (R.mats c).val)
    (hN : IsPVM fun b => (N.mats b).val) {δ : ℝ}
    (hd : ∑ c, stateSqNorm ψ ((M.mats c).val - (R.mats c).val) ≤ δ) :
    |testAcceptance ψ D (fun a => ((M.map f).mats a).val) (fun b => (N.mats b).val) -
      testAcceptance ψ D (fun a => ((R.map f).mats a).val) (fun b => (N.mats b).val)| ≤
      2*Real.sqrt δ := by
  rw [testAcceptance_map_left, testAcceptance_map_left]
  exact testAcceptance_stability_left ψ hψ (fun c b => D (f c) b)
    _ _ _ hM hR hN hd

/-- Averaging conditional acceptance changes costs no question-count factor. -/
theorem povmValue_stability_of_condWin (G : Game X Y A B) (ψ : H × K → ℂ)
    (MA RA : X → POVM A H) (MB : Y → POVM B K)
    (err : X → ℝ) (herr : ∀ x, 0 ≤ err x)
    (hpoint : ∀ x y, |condWin G ψ MA MB x y - condWin G ψ RA MB x y| ≤
      2*Real.sqrt (err x)) {δ : ℝ}
    (hd : ∑ x, ∑ y, G.μ x y * err x ≤ δ) :
    |povmValue G ψ MA MB - povmValue G ψ RA MB| ≤ 2*Real.sqrt δ := by
  have heq : povmValue G ψ MA MB - povmValue G ψ RA MB =
      ∑ p : X × Y, G.μ p.1 p.2 *
        (condWin G ψ MA MB p.1 p.2 - condWin G ψ RA MB p.1 p.2) := by
    simp only [povmValue, Fintype.sum_prod_type, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ p : X × Y, |G.μ p.1 p.2 *
        (condWin G ψ MA MB p.1 p.2 - condWin G ψ RA MB p.1 p.2)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : X × Y, G.μ p.1 p.2 * (2*Real.sqrt (err p.1)) := by
      refine Finset.sum_le_sum fun p _ => ?_
      rw [abs_mul, abs_of_nonneg (G.μ_nonneg _ _)]
      exact mul_le_mul_of_nonneg_left (hpoint p.1 p.2) (G.μ_nonneg _ _)
    _ = 2*∑ p : X × Y, G.μ p.1 p.2 * Real.sqrt (err p.1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ 2*Real.sqrt δ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (sum_weighted_sqrt_le (fun p : X × Y => G.μ p.1 p.2)
        (fun p => err p.1) (fun p => G.μ_nonneg _ _)
        (by simpa only [Fintype.sum_prod_type] using G.μ_sum_one)
        (fun p => herr p.1)).trans
      exact Real.sqrt_le_sqrt (by simpa only [Fintype.sum_prod_type] using hd)

/-- A single changed question, with an arbitrary outcome relabelling. All
other questions are literally unchanged, and the error pays at most its
conditional bound since the question's marginal probability is at most one. -/
theorem povmValue_stability_at [DecidableEq X]
    (G : Game X Y A B) (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (MA RA : X → POVM A H) (MB : Y → POVM B K)
    (q : X) (M R : POVM C H) (f : C → A)
    (hMA : MA q = M.map f) (hRA : RA q = R.map f)
    (hsame : ∀ x, x ≠ q → MA x = RA x)
    (hM : IsPVM fun c => (M.mats c).val) (hR : IsPVM fun c => (R.mats c).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val) {δ : ℝ}
    (hd : ∑ c, stateSqNorm ψ ((M.mats c).val - (R.mats c).val) ≤ δ) :
    |povmValue G ψ MA MB - povmValue G ψ RA MB| ≤ 2*Real.sqrt δ := by
  have hδ : 0 ≤ δ := (Finset.sum_nonneg fun _ _ => stateSqNorm_nonneg _ _).trans hd
  apply povmValue_stability_of_condWin G ψ MA RA MB (fun x => if x = q then δ else 0)
    (fun x => by split_ifs <;> positivity)
  · intro x y
    by_cases hx : x = q
    · subst x
      change |testAcceptance ψ (G.D q y) (fun a => ((MA q).mats a).val)
        (fun b => ((MB y).mats b).val) -
        testAcceptance ψ (G.D q y) (fun a => ((RA q).mats a).val)
        (fun b => ((MB y).mats b).val)| ≤ _
      rw [hMA, hRA]
      simpa only [if_pos rfl, ite_true] using
        testAcceptance_stability_map_left ψ hψ (G.D q y) M R (MB y) f hM hR (hMB y) hd
    · simp only [condWin, hsame x hx, sub_self, abs_zero, if_neg hx, Real.sqrt_zero, mul_zero]
      exact le_rfl
  · calc
      _ ≤ ∑ x, ∑ y, G.μ x y * δ := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        apply mul_le_mul_of_nonneg_left _ (G.μ_nonneg _ _)
        split_ifs <;> simp_all
      _ = δ := by simp only [← Finset.sum_mul, G.μ_sum_one, one_mul]

end MIPRE.Introspection
end
