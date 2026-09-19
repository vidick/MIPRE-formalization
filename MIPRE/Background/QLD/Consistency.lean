/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Ortho
import MIPRE.Foundations.POVMValue

/-!
# From bipartite consistency to near-projectivity

The second half of blueprint `cor:ortho-from-consistency`. `Ortho.lean` turns *near-projectivity*
of a POVM on Alice's factor into a projective measurement close to it; what the appendix has is
*consistency* of Alice's POVM with one of Bob's. The bridge is a Cauchy--Schwarz step: writing
`γ = ∑_{a ≠ b} ⟨ψ| Q_a ⊗ R_b |ψ⟩`, so that `∑_a ⟨ψ| Q_a ⊗ R_a |ψ⟩ = 1 - γ`,

`1 - γ = ∑_a ⟨(Q_a ⊗ Id)ψ, (Id ⊗ R_a)ψ⟩ ≤ (∑_a ‖(Q_a ⊗ Id)ψ‖²)^{1/2} (∑_a ‖(Id ⊗ R_a)ψ‖²)^{1/2}`

and the second factor is at most one because `∑_a R_a² ≤ ∑_a R_a = Id`.

## A repair to the blueprint's proof

The blueprint and the paper close with a compactness step: the theorem gives a projective family
only for `ε > 2γ` strictly, and a limit along `ε ↓ 2γ` is taken inside the compact set of
projective measurements to reach the bound `18γ` itself. That step is not formalized, and it is
not needed. `(1 - γ)² = 1 - 2γ + γ²` has slack `γ²` over `1 - 2γ`, so the hypothesis of
`exists_projective_of_nearProjective` already holds *strictly* at `ε = 2δ` whenever `γ ≤ δ` and
`δ > 0`, whether or not `γ = 0`:

* if `γ ≥ 1` the conclusion is vacuous, `1 - 2δ ≤ -1 < 0 ≤ ∑_a ‖(Q_a ⊗ Id)ψ‖²`;
* otherwise `∑_a ‖(Q_a ⊗ Id)ψ‖² ≥ (1 - γ)² = 1 - 2γ + γ² > 1 - 2δ`, since `2γ - γ² < 2δ` holds
  for every `γ ≤ δ` with `δ > 0` --- at `γ = δ` because `γ² > 0`, and at `γ < δ` because
  `γ² ≥ 0`.

So `exists_projective_of_consistent` below is stated for a *bound* `δ > 0` on the inconsistency
rather than for the inconsistency itself, and concludes the strict `< 18 δ`. It is what every
application needs, `η_ortho(δ) = 18 δ` being linear as the paper requires, and it costs no
compactness. The one thing it does not give is the exact `δ = 0` case, where the paper's limit
yields a projective measurement agreeing with `Q` on `ψ` exactly; no application uses it.
-/

namespace MIPRE.QLD

open Finset Matrix Kronecker MIPRE
open scoped ComplexOrder MatrixOrder

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-! ## The inconsistency of a single pair of POVMs -/

/-- The inconsistency of one pair of POVMs on a bipartite state: `MIPRE.inconsistency` for a
single question. The question-averaged form is the weighted sum of these
(`inconsistency_eq_sum_pairInconsistency`). -/
noncomputable def pairInconsistency (ψ : dA × dB → ℂ) (Q : POVM A dA) (R : POVM A dB) : ℝ :=
  ∑ a, ∑ b, if a = b then 0 else
    (star ψ ⬝ᵥ ((((Q.mats a).val ⊗ₖ ((R.mats b).val))) *ᵥ ψ)).re

theorem inconsistency_eq_sum_pairInconsistency {X : Type*} [Fintype X] (μ : X → ℝ)
    (ψ : dA × dB → ℂ) (M : X → POVM A dA) (N : X → POVM A dB) :
    inconsistency μ ψ M N = ∑ x, μ x * pairInconsistency ψ (M x) (N x) := rfl

/-- **The diagonal terms sum to `1 - γ`**, because `∑_{a,b} Q_a ⊗ R_b = Id`. -/
theorem sum_diag_eq_one_sub {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (Q : POVM A dA)
    (R : POVM A dB) :
    ∑ a, (star ψ ⬝ᵥ ((((Q.mats a).val ⊗ₖ ((R.mats a).val))) *ᵥ ψ)).re
      = 1 - pairInconsistency ψ Q R := by
  classical
  set f : A → A → ℝ := fun a b =>
    (star ψ ⬝ᵥ ((((Q.mats a).val ⊗ₖ ((R.mats b).val))) *ᵥ ψ)).re with hf
  -- the full double sum is `⟨ψ| Id |ψ⟩ = 1`
  have htot : ∑ a, ∑ b, f a b = 1 := by
    have hker : ∑ a, ∑ b, ((Q.mats a).val ⊗ₖ ((R.mats b).val))
        = (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
      have hb : ∀ a, ∑ b, ((Q.mats a).val ⊗ₖ ((R.mats b).val))
          = ((Q.mats a).val ⊗ₖ (1 : Matrix dB dB ℂ)) := by
        intro a
        rw [← kronecker_sum_right, POVM.sum_val]
      rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hb a, ← sum_kronecker_left,
        POVM.sum_val, Matrix.one_kronecker_one]
    have := sum_quadForm ψ (Finset.univ : Finset A)
      fun a => ∑ b, ((Q.mats a).val ⊗ₖ ((R.mats b).val))
    rw [hker, Matrix.one_mulVec, hψ] at this
    have h2 : ∀ a, (star ψ ⬝ᵥ ((∑ b, ((Q.mats a).val ⊗ₖ ((R.mats b).val))) *ᵥ ψ))
        = ∑ b, star ψ ⬝ᵥ ((((Q.mats a).val ⊗ₖ ((R.mats b).val))) *ᵥ ψ) :=
      fun a => sum_quadForm ψ _ _
    rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => h2 a] at this
    have h3 := congrArg Complex.re this
    rw [Complex.re_sum, Complex.one_re] at h3
    rw [h3]
    exact Finset.sum_congr rfl fun a _ => (Complex.re_sum _ _).symm
  -- split off the diagonal
  have hdiag : ∀ a, (∑ b, if a = b then f a b else 0) = f a a := by
    intro a
    rw [Finset.sum_ite_eq]
    simp
  have hper : ∀ a, ∑ b, f a b = f a a + ∑ b, if a = b then 0 else f a b := by
    intro a
    rw [← hdiag a, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : a = b <;> simp [h]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hper a,
    Finset.sum_add_distrib] at htot
  have hγ : pairInconsistency ψ Q R = ∑ a, ∑ b, if a = b then 0 else f a b := rfl
  rw [hγ]
  linarith [htot]

/-! ## Bob's side contributes at most one -/

omit [DecidableEq A] in
/-- **`∑_a ‖(Id ⊗ R_a)|ψ⟩‖² ≤ 1`**, because `∑_a R_a² ≤ ∑_a R_a = Id` and the reduced state of
Bob's factor is a positive unital functional. `swapVec` is what lets `Ortho.lean`'s Alice-side
reduced state serve on Bob's factor. -/
theorem sum_normSq_stateVecB_le_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (R : POVM A dB) :
    ∑ a, ‖stateVecB ψ (((R.mats a).val))‖ ^ 2 ≤ 1 := by
  classical
  set φ := redState (swapVec ψ) with hφ
  have hφ1 : φ 1 = 1 := redState_one (by rw [swapVec_dotProduct]; exact hψ)
  have ha0 : ∀ a, 0 ≤ toCLM ((R.mats a).val) := fun a =>
    toCLM_nonneg (Subtype.coe_le_coe.mpr (R.nonneg a))
  have ha1 : ∑ a, toCLM ((R.mats a).val) = 1 := by
    rw [← toCLM_sum, POVM.sum_val, toCLM_one]
  have hle : ∑ a, toCLM ((R.mats a).val) * toCLM ((R.mats a).val) ≤ 1 := by
    refine le_trans (Finset.sum_le_sum fun a _ => ?_) (le_of_eq ha1)
    refine Orthogonalization.sq_le_self_of_le_one (ha0 a) ?_
    rw [← ha1]
    exact Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ a)
  have hterm : ∀ a, ‖stateVecB ψ (((R.mats a).val))‖ ^ 2
      = (φ (toCLM ((R.mats a).val) * toCLM ((R.mats a).val))).re := by
    intro a
    rw [norm_stateVecB, hφ,
      redState_mul_self (swapVec ψ) ((R.mats a).2 : ((R.mats a).val)ᴴ = ((R.mats a).val)),
      Complex.ofReal_re]
    rfl
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hterm a,
    ← Complex.re_sum, ← map_sum]
  refine le_trans (Orthogonalization.re_le_re_of_le (redState_nonneg (swapVec ψ)) hle) ?_
  rw [hφ1, Complex.one_re]

/-! ## The Cauchy--Schwarz bridge -/

/-- **Consistency implies near-projectivity**, strictly, at any positive bound `δ` on the
inconsistency. This is the step the blueprint's proof calls a Cauchy--Schwarz step; the strictness
is the `γ²` slack in `(1 - γ)² = 1 - 2γ + γ²`, and it is what removes the compactness argument. -/
theorem one_sub_two_mul_lt_sum_stateSqNorm {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (Q : POVM A dA) (R : POVM A dB) (δ : ℝ) (hδ : 0 < δ)
    (hcons : pairInconsistency ψ Q R ≤ δ) :
    1 - 2 * δ < ∑ a, stateSqNorm ψ (((Q.mats a).val)) := by
  classical
  set γ := pairInconsistency ψ Q R with hγ
  set S := ∑ a, stateSqNorm ψ (((Q.mats a).val)) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => stateSqNorm_nonneg ψ _
  by_cases hone : 1 - γ ≤ 0
  · -- vacuous: the inconsistency already exceeds one
    have : (1 : ℝ) ≤ δ := le_trans (by linarith) hcons
    linarith
  · rw [not_le] at hone
    -- each diagonal term is an inner product, hence at most the product of the norms
    set T := ∑ a, stateNorm ψ (((Q.mats a).val)) * ‖stateVecB ψ (((R.mats a).val))‖ with hT
    have hdiag : ∑ a, (star ψ ⬝ᵥ ((((Q.mats a).val ⊗ₖ ((R.mats a).val))) *ᵥ ψ)).re ≤ T := by
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← inner_stateVec_stateVecB ψ
        ((Q.mats a).2 : ((Q.mats a).val)ᴴ = ((Q.mats a).val)) (((R.mats a).val))]
      simpa [stateNorm] using
        re_inner_le_norm (𝕜 := ℂ) (stateVec ψ (((Q.mats a).val)))
          (stateVecB ψ (((R.mats a).val)))
    have hle : 1 - γ ≤ T := by
      rw [← sum_diag_eq_one_sub hψ Q R]; exact hdiag
    -- Cauchy--Schwarz over the outcomes, and Bob's side is at most one
    have hCS : T ^ 2 ≤ S * ∑ a, ‖stateVecB ψ (((R.mats a).val))‖ ^ 2 := by
      refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _) (le_of_eq ?_)
      rw [hS]
      rfl
    have hB : ∑ a, ‖stateVecB ψ (((R.mats a).val))‖ ^ 2 ≤ 1 :=
      sum_normSq_stateVecB_le_one hψ R
    have hTS : T ^ 2 ≤ S := by
      refine le_trans hCS ?_
      calc S * ∑ a, ‖stateVecB ψ (((R.mats a).val))‖ ^ 2 ≤ S * 1 :=
            mul_le_mul_of_nonneg_left hB hS0
        _ = S := mul_one S
    have hsq : (1 - γ) ^ 2 ≤ S := le_trans (pow_le_pow_left₀ hone.le hle 2) hTS
    nlinarith [sq_nonneg γ, sq_nonneg (1 - γ)]

/-! ## The corollary -/

/-- **Orthonormalization from consistency**, blueprint `cor:ortho-from-consistency`, with
`η_ortho(δ) = 18 δ`. The hypothesis is a positive bound on the inconsistency of `Q` with a POVM
`R` on the other factor; the file's docstring records why that is the right form and what the
paper's compactness step would add. -/
theorem exists_projective_of_consistent {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (Q : POVM A dA) (R : POVM A dB) (δ : ℝ) (hδ : 0 < δ)
    (hcons : pairInconsistency ψ Q R ≤ δ) :
    ∃ P : A → Matrix dA dA ℂ,
      (∀ a, (P a)ᴴ = P a) ∧ (∀ a, P a * P a = P a) ∧ (∑ a, P a = 1) ∧
        ∑ a, stateSqNorm ψ (((Q.mats a).val) - P a) < 18 * δ := by
  obtain ⟨P, hsa, hidem, hsum, hbound⟩ :=
    exists_projective_of_nearProjective hψ Q (2 * δ)
      (by simpa using one_sub_two_mul_lt_sum_stateSqNorm hψ Q R δ hδ hcons)
  exact ⟨P, hsa, hidem, hsum, by linarith⟩

end MIPRE.QLD
