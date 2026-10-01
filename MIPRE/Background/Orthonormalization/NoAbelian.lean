/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Orthonormalization.CenterComparison
public import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.II1Factor

@[expose] public section

/-!
# Orthonormalization in von Neumann algebras without abelian projections

De la Salle's Theorem 1.2 (blueprint `thm:orthonormalization`) for a von Neumann algebra `M` with
no nonzero abelian projection and a faithful tracial vector functional, against any state given
by a summable family of vectors — in particular a vector state — with no factor hypothesis. This
is the orthonormalization tier the C6b port uses (the II₁ tier of `planning/mipco-track.md`,
Phase 6).

The vendored II₁-factor theorem (`Orthogonalization.povm_orthogonalization_II₁Factor`,
`MvN/II1Factor.lean`) uses its factor hypothesis only to build the scalar centre-valued trace
`x ↦ τ(x) • 1`; its proof reads the centre-valued trace only through `IsCenterValuedTrace`, and
the state only through positivity, `φ 1 = 1` and its trace-class form, never through normality.
So the same proof, with the centre-valued trace of `CenterComparison.lean` in place of the scalar
one, gives the theorem for every `M` without abelian projections
(`povm_orthogonalization_of_isCenterValuedTrace`), and for a vector state
(`povm_orthogonalization_vecTrace`).
-/

namespace MIPRE.Orthonormalization

open scoped ComplexOrder InnerProductSpace
open Orthogonalization Orthogonalization.MvN

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Theorem 1.2 from a centre-valued trace**: in a von Neumann algebra with no nonzero abelian
projection and a centre-valued trace, a POVM that is `ε`-nearly projective against a positive
normalized functional of trace-class form is `9ε`-close to a projective measurement of the
algebra. -/
theorem povm_orthogonalization_of_isCenterValuedTrace (M : VonNeumannAlgebra H)
    (hII : ∀ r, IsAbelianProj M r → r = 0) {E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)}
    (hE : IsCenterValuedTrace M 1 E) (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφ0 : ∀ x ∈ M, 0 ≤ φ (star x * x)) (hφ1 : φ 1 = 1)
    (hφg : ∃ g : ℕ → H, Summable (fun k => ‖g k‖ ^ 2) ∧ ∀ x ∈ M, φ x = ∑' k, ⟪g k, x (g k)⟫_ℂ)
    {ι : Type*} [Fintype ι] (a : ι → H →L[ℂ] H) (ha : IsPOVM M a) (ε : ℝ)
    (hε : 1 - ε < (φ (∑ i, a i * a i)).re) :
    ∃ p : ι → H →L[ℂ] H, IsPVM M p ∧
      (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
  -- The proof of the vendored `povm_orthogonalization_II₁Factor` (`MvN/II1Factor.lean`), copied
  -- because that theorem builds its centre-valued trace from its factor hypothesis.
  have h1 : IsStarProjection (1 : H →L[ℂ] H) := IsStarProjection.one _
  have h1c : IsCentralIn M 1 1 := isCentralIn_proj M h1 (one_mem M)
  -- the finite case at `p = 1`, with output set `Fin n`
  have hfin : ∀ n : ℕ, ∀ a : Fin n → H →L[ℂ] H, (∀ i, a i ∈ M) → (∀ i, 0 ≤ a i) →
      ∑ i, a i = 1 → 1 - ε < (φ (∑ i, a i * a i)).re →
      ∃ p : Fin n → H →L[ℂ] H, (∀ i, p i ∈ M) ∧ (∀ i, IsStarProjection (p i)) ∧
        ∑ i, p i = 1 ∧ (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
    intro n a haM ha0 ha1 hε
    -- Lemma 3.1 at `1`: the type I part is `c = 0`, the type II₁ part is all of `M`
    obtain ⟨q, hq, hqE, hqineq⟩ := selection_of_split M h1 (one_mem M) E
      (IsStarProjection.zero _) (isCentralIn_zero M 1) φ
      (fun m a' ha'M ha'0 ha'c => by
        -- a POVM summing to `0` is zero
        have ha'z : ∀ i, a' i = 0 := fun i => by
          simpa using (Blocks.mul_eq_self_of_sum_eq (IsStarProjection.zero _) ha'0 ha'c i).symm
        refine ⟨fun _ => 0, fun i => ⟨IsStarProjection.zero _, zero_mem M, mul_zero 0,
          Commute.zero_left _⟩, by simp, ?_⟩
        simp [ha'z])
      (fun m a' ha'M ha'0 ha'c =>
        exists_selection_typeII₁ M h1 (one_mem M) (c := 1 - 0) (by rw [sub_zero]; exact h1)
          (by rw [sub_zero]; exact h1c) (fun r hr _ => hII r hr) E hE a' ha'M ha'0 ha'c φ hφg)
      n a haM ha0 ha1
    -- Lemma 3.2 in `M_n(M)` and the three-term estimate
    obtain ⟨p, hpM, hp, -, hsum, hlt⟩ := exists_pvm_bound_of_selection M h1 (one_mem M) E
      (hE.center_fixed 1 h1c) hE.trace (hE.equiv_of_eq_matrix n)
      (fun x hx => exists_polar (matrixAlgebra M n) x hx) φ hφ0 hφ1 a haM ha0 ha1 ε hε q hq hqE
      hqineq
    exact ⟨p, hpM, hp, hsum, hlt⟩
  -- transport to the output set `ι` along `Fintype.equivFin ι`
  set e := Fintype.equivFin ι
  obtain ⟨p', hp'M, hp', hp'sum, hlt⟩ := hfin _ (fun i => a (e.symm i)) (fun i => ha.1 _)
    (fun i => ContinuousLinearMap.nonneg_iff_isPositive.mpr (ha.2.1 _))
    (by rw [Equiv.sum_comp e.symm a]; exact ha.2.2)
    (by rw [Equiv.sum_comp e.symm (fun i => a i * a i)]; exact hε)
  refine ⟨fun i => p' (e i), ⟨fun i => hp'M _, fun i => hp' _, ?_⟩, ?_⟩
  · rw [← hp'sum]
    exact Equiv.sum_comp e p'
  · rw [← Equiv.sum_comp e.symm (fun i => star (a i - p' (e i)) * (a i - p' (e i)))]
    simpa only [Equiv.apply_symm_apply] using hlt

/-- **Theorem 1.2 in a von Neumann algebra without abelian projections, at a vector state**: for
`M` with no nonzero abelian projection and a faithful tracial vector functional of finitely many
vectors, a POVM `(aᵢ)` of `M` with `∑ᵢ ‖aᵢ ψ‖² > 1 - ε` at a unit vector `ψ` is within
`∑ᵢ ‖(aᵢ - pᵢ) ψ‖² < 9ε` of a projective measurement `(pᵢ)` of `M`. -/
theorem povm_orthogonalization_vecTrace (M : VonNeumannAlgebra H)
    (hII : ∀ r, IsAbelianProj M r → r = 0) {d : ℕ} (g : Fin d → H)
    (htr : ∀ x ∈ M, ∀ y ∈ M, vecFunctional g (x * y) = vecFunctional g (y * x))
    (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) (ψ : H) (hψ : ‖ψ‖ = 1)
    {ι : Type*} [Fintype ι] (a : ι → H →L[ℂ] H) (ha : IsPOVM M a) (ε : ℝ)
    (hε : 1 - ε < ∑ i, ‖a i ψ‖ ^ 2) :
    ∃ p : ι → H →L[ℂ] H, IsPVM M p ∧ ∑ i, ‖(a i - p i) ψ‖ ^ 2 < 9 * ε := by
  obtain ⟨E, hE⟩ := exists_isCenterValuedTrace M g htr hsep
  -- the vector state `x ↦ ⟪ψ, x ψ⟫` is of trace-class form, with the single vector `ψ`
  have hφg : ∃ g : ℕ → H, Summable (fun k => ‖g k‖ ^ 2) ∧
      ∀ x ∈ M, Corollaries.vecFunctional ψ x = ∑' k, ⟪g k, x (g k)⟫_ℂ := by
    refine ⟨fun k => if k = 0 then ψ else 0,
      (hasSum_single 0 fun k hk => by simp [hk]).summable, fun x _ => ?_⟩
    rw [tsum_eq_single 0 fun k hk => by simp [hk], Corollaries.vecFunctional_apply]
    simp
  obtain ⟨p, hp, hlt⟩ := povm_orthogonalization_of_isCenterValuedTrace M hII hE
    (Corollaries.vecFunctional ψ) (fun x _ => Corollaries.vecFunctional_star_mul_self_nonneg ψ x)
    (Corollaries.vecFunctional_one ψ hψ) hφg a ha ε
    (by rwa [Corollaries.re_vecFunctional_sum_mul_self ψ a fun i => (ha.2.1 i).isSelfAdjoint])
  refine ⟨p, hp, ?_⟩
  simpa only [Corollaries.re_vecFunctional_sum_star_sub_mul_sub, sub_apply] using hlt

end MIPRE.Orthonormalization

end
