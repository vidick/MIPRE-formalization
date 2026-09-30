/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ValueStability
public import MIPRE.Foundations.POVMMix

@[expose] public section

/-! # Game-value bounds for actual question-indexed replacements

Acceptance is compared before relabelling the outcomes. This permits a common
answer alphabet without assuming that same-party squared distance contracts
under coarse-graining.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`).
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Classical
set_option linter.unusedSectionVars false

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {X Y A B C : Type*}
  [Fintype X] [Fintype Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- Relabelling a measurement pulls the acceptance predicate back exactly. -/
theorem testAcceptance_map_left (D : A → B → Bool) (M : POVMIn C 𝒜) (N : POVMIn B ℬ)
    (f : C → A) :
    testAcceptance Ψ D (M.map f).op N.op = testAcceptance Ψ (fun c b => D (f c) b) M.op N.op := by
  unfold testAcceptance
  rw [Finset.sum_comm]
  simp_rw [Ψ.sum_bornProb_mapA M f]
  exact Finset.sum_comm

/-- A projective replacement may be relabelled into a larger answer alphabet
without an answer-cardinality cost in the acceptance estimate. -/
theorem testAcceptance_stability_map_left (hΨ : ‖Ψ.ψ‖ = 1)
    (D : A → B → Bool) (M R : POVMIn C 𝒜) (N : POVMIn B ℬ) (f : C → A)
    (hM : IsPVMIn M.op) (hR : IsPVMIn R.op) (hN : IsPVMIn N.op) {δ : ℝ}
    (hd : ∑ c, Ψ.stateSqNorm (M.op c - R.op c) ≤ δ) :
    |testAcceptance Ψ D (M.map f).op N.op - testAcceptance Ψ D (R.map f).op N.op| ≤
      2*Real.sqrt δ := by
  rw [testAcceptance_map_left, testAcceptance_map_left]
  exact testAcceptance_stability_left Ψ hΨ (fun c b => D (f c) b) _ _ _ hM hR hN hd

/-- Averaging conditional acceptance changes costs no question-count factor. -/
theorem povmValue_stability_of_condWin (G : Game X Y A B)
    (MA RA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ)
    (err : X → ℝ) (herr : ∀ x, 0 ≤ err x)
    (hpoint : ∀ x y, |Ψ.condWin G MA MB x y - Ψ.condWin G RA MB x y| ≤
      2*Real.sqrt (err x)) {δ : ℝ}
    (hd : ∑ x, ∑ y, G.μ x y * err x ≤ δ) :
    |Ψ.povmValue G MA MB - Ψ.povmValue G RA MB| ≤ 2*Real.sqrt δ := by
  have heq : Ψ.povmValue G MA MB - Ψ.povmValue G RA MB =
      ∑ p : X × Y, G.μ p.1 p.2 *
        (Ψ.condWin G MA MB p.1 p.2 - Ψ.condWin G RA MB p.1 p.2) := by
    simp only [BipartiteModel.povmValue, Fintype.sum_prod_type, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ p : X × Y, |G.μ p.1 p.2 *
        (Ψ.condWin G MA MB p.1 p.2 - Ψ.condWin G RA MB p.1 p.2)| :=
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
    (G : Game X Y A B) (hΨ : ‖Ψ.ψ‖ = 1)
    (MA RA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ)
    (q : X) (M R : POVMIn C 𝒜) (f : C → A)
    (hMA : MA q = M.map f) (hRA : RA q = R.map f)
    (hsame : ∀ x, x ≠ q → MA x = RA x)
    (hM : IsPVMIn M.op) (hR : IsPVMIn R.op)
    (hMB : ∀ y, IsPVMIn (MB y).op) {δ : ℝ}
    (hd : ∑ c, Ψ.stateSqNorm (M.op c - R.op c) ≤ δ) :
    |Ψ.povmValue G MA MB - Ψ.povmValue G RA MB| ≤ 2*Real.sqrt δ := by
  have hδ : 0 ≤ δ := (Finset.sum_nonneg fun _ _ => Ψ.stateSqNorm_nonneg _).trans hd
  apply povmValue_stability_of_condWin Ψ G MA RA MB (fun x => if x = q then δ else 0)
    (fun x => by split_ifs <;> positivity)
  · intro x y
    by_cases hx : x = q
    · subst x
      change |testAcceptance Ψ (G.D q y) (MA q).op (MB y).op -
        testAcceptance Ψ (G.D q y) (RA q).op (MB y).op| ≤ _
      rw [hMA, hRA]
      simpa only [↓reduceIte] using
        testAcceptance_stability_map_left Ψ hΨ (G.D q y) M R (MB y) f hM hR (hMB y) hd
    · simp only [BipartiteModel.condWin, hsame x hx, sub_self, abs_zero, hx, ↓reduceIte,
        Real.sqrt_zero, mul_zero]
      exact le_rfl
  · calc
      _ ≤ ∑ x, ∑ y, G.μ x y * δ := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        apply mul_le_mul_of_nonneg_left _ (G.μ_nonneg _ _)
        split_ifs <;> simp_all
      _ = δ := by simp only [← Finset.sum_mul, G.μ_sum_one, one_mul]

end MIPRE.Introspection
end

end
