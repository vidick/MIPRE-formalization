/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/JointDiag.lean
-/
/-
# Joint diagonalization of two commuting self-adjoint operators (finite dimension)

Toolkit for Lemma 3.1 of M. de la Salle, *Orthogonalization of Positive Operator
Valued Measures* (arXiv:2103.14126v2), in the finite-dimensional case (`PLAN.md`
§3, tier T1a). The perturbation argument of that lemma takes a pair `(x, a)` of
commuting self-adjoint operators on a finite-dimensional complex Hilbert space
`H`, diagonalizes them simultaneously, and moves an amount `δ` of one eigenvalue
of `x` onto another, keeping the trace and the commutation with `a` and staying
inside the operator interval `[0, 1]`.

This file packages exactly that: a `JointEigenbasis x a` (an orthonormal basis of
`H` made of joint eigenvectors of `x` and `a`, with *real* eigenvalue functions
`lam` and `mu`), its existence for commuting self-adjoint operators, the rank-one
spectral projections `P k`, the spectral decomposition and trace formula, the
translation between the Loewner order on `x` and the pointwise order on `lam`,
the characterisation of the projections among such `x`, and the two eigenvalue
shifts (`shiftPair`, `shiftOne`).

Everything here is elementary and internal to the proof; no result of this file
is a statement of the paper, so it carries no fidelity-ledger entry.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.FinDim

open scoped BigOperators ComplexOrder InnerProductSpace
open Module

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A **joint orthonormal eigenbasis** for a pair of operators `x a : H →L[ℂ] H`:
an orthonormal basis `basis` of `H`, indexed by `Fin (finrank ℂ H)`, each of whose
vectors is an eigenvector of `x` with real eigenvalue `lam k` and an eigenvector
of `a` with real eigenvalue `mu k`.

Such a datum exists exactly when `x` and `a` are commuting self-adjoint operators:
see `Orthogonalization.FinDim.exists_jointEigenbasis` for one direction and
`JointEigenbasis.isSelfAdjoint_fst`, `JointEigenbasis.isSelfAdjoint_snd`,
`JointEigenbasis.commute` for the other. -/
structure JointEigenbasis (x a : H →L[ℂ] H) where
  /-- The orthonormal basis of joint eigenvectors. -/
  basis : OrthonormalBasis (Fin (finrank ℂ H)) ℂ H
  /-- The (real) eigenvalues of the first operator `x`. -/
  lam : Fin (finrank ℂ H) → ℝ
  /-- The (real) eigenvalues of the second operator `a`. -/
  mu : Fin (finrank ℂ H) → ℝ
  /-- `basis k` is an eigenvector of `x` for the eigenvalue `lam k`. -/
  apply_fst : ∀ k, x (basis k) = (lam k : ℂ) • basis k
  /-- `basis k` is an eigenvector of `a` for the eigenvalue `mu k`. -/
  apply_snd : ∀ k, a (basis k) = (mu k : ℂ) • basis k

section Existence

/-- **Simultaneous diagonalization.** Two commuting self-adjoint operators on a
finite-dimensional complex inner product space admit a joint orthonormal
eigenbasis with real eigenvalues. -/
theorem exists_jointEigenbasis {x a : H →L[ℂ] H} (hx : IsSelfAdjoint x)
    (ha : IsSelfAdjoint a) (hxa : Commute x a) : Nonempty (JointEigenbasis x a) := by
  classical
  have hX : LinearMap.IsSymmetric (x : H →ₗ[ℂ] H) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hx
  have hA : LinearMap.IsSymmetric (a : H →ₗ[ℂ] H) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ha
  have hXA : Commute (x : H →ₗ[ℂ] H) (a : H →ₗ[ℂ] H) := by
    have := congrArg (fun T : H →L[ℂ] H => (T : H →ₗ[ℂ] H)) hxa
    simpa [Commute, SemiconjBy, ContinuousLinearMap.toLinearMap_mul] using this
  -- The joint eigenspaces, indexed by the (finitely many) pairs of eigenvalues.
  set V : (End.Eigenvalues (a : H →ₗ[ℂ] H) × End.Eigenvalues (x : H →ₗ[ℂ] H)) →
      Submodule ℂ H :=
    fun i => End.eigenspace (x : H →ₗ[ℂ] H) (i.2 : ℂ) ⊓
      End.eigenspace (a : H →ₗ[ℂ] H) (i.1 : ℂ) with hV
  have hfam : OrthogonalFamily ℂ (fun i => (V i : Submodule ℂ H))
      fun i => (V i).subtypeₗᵢ := by
    have hpair :=
      (LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hX hA).pairwise
    refine OrthogonalFamily.of_pairwise ?_
    rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩ hij
    refine hpair (i := (p, q)) (j := (p', q')) ?_
    simp only [ne_eq, Prod.mk.injEq, not_and] at hij ⊢
    intro h1 h2
    exact hij (by subst h1; subst h2; rfl)
  have htop : (⨆ i, V i) = ⊤ := by
    rw [eq_top_iff,
      ← LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hX hA hXA]
    refine iSup_le fun α => iSup_le fun γ => ?_
    by_cases hα : End.HasEigenvalue (x : H →ₗ[ℂ] H) α
    · by_cases hγ : End.HasEigenvalue (a : H →ₗ[ℂ] H) γ
      · exact le_iSup V ((⟨γ, hγ⟩, ⟨α, hα⟩))
      · rw [End.hasEigenvalue_iff, not_not] at hγ
        simp [hV, hγ]
    · rw [End.hasEigenvalue_iff, not_not] at hα
      simp [hV, hα]
  have hint : DirectSum.IsInternal V := hfam.isInternal_iff.mpr (by rw [htop]; simp)
  set b : OrthonormalBasis (Fin (finrank ℂ H)) ℂ H :=
    hint.subordinateOrthonormalBasis rfl hfam with hb
  set idx : Fin (finrank ℂ H) →
      (End.Eigenvalues (a : H →ₗ[ℂ] H) × End.Eigenvalues (x : H →ₗ[ℂ] H)) :=
    fun k => hint.subordinateOrthonormalBasisIndex rfl k hfam with hidx
  have hmem : ∀ k, b k ∈ V (idx k) := fun k =>
    hint.subordinateOrthonormalBasis_subordinate (hn := rfl) k hfam
  -- The eigenvalues of a symmetric operator are real.
  have hreal : ∀ (T : H →ₗ[ℂ] H), T.IsSymmetric → ∀ μ : End.Eigenvalues T,
      ((RCLike.re (μ : ℂ) : ℝ) : ℂ) = (μ : ℂ) := fun T hT μ =>
    RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self μ.property)
  refine ⟨{ basis := b
            lam := fun k => RCLike.re (((idx k).2 : ℂ))
            mu := fun k => RCLike.re (((idx k).1 : ℂ))
            apply_fst := fun k => ?_
            apply_snd := fun k => ?_ }⟩
  · rw [hreal _ hX]
    exact End.mem_eigenspace_iff.mp (hmem k).1
  · rw [hreal _ hA]
    exact End.mem_eigenspace_iff.mp (hmem k).2

end Existence

namespace JointEigenbasis

variable {x a : H →L[ℂ] H} (J : JointEigenbasis x a)

include J

-- Most lemmas below only use the eigen-equations, not finite-dimensionality of `H`
-- (which enters only through `exists_jointEigenbasis`); silence the resulting noise.
set_option linter.unusedSectionVars false

/-! ### Elementary consequences of the eigen-equations -/

theorem norm_basis (k : Fin (finrank ℂ H)) : ‖J.basis k‖ = 1 := J.basis.orthonormal.1 k

theorem basis_ne_zero (k : Fin (finrank ℂ H)) : J.basis k ≠ 0 := by
  intro h
  have h1 := J.norm_basis k
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem inner_basis (k l : Fin (finrank ℂ H)) :
    inner ℂ (J.basis k) (J.basis l) = if k = l then (1 : ℂ) else 0 :=
  orthonormal_iff_ite.mp J.basis.orthonormal k l

@[simp] theorem inner_basis_self (k : Fin (finrank ℂ H)) :
    inner ℂ (J.basis k) (J.basis k) = (1 : ℂ) := by simp

/-- Two continuous operators agreeing on the joint eigenbasis are equal. -/
theorem ext_basis {S T : H →L[ℂ] H} (h : ∀ k, S (J.basis k) = T (J.basis k)) : S = T := by
  ext w
  rw [← J.basis.sum_repr' w]
  simp only [map_sum, map_smul, h]

/-- Exchanging the roles of the two operators. -/
def swap : JointEigenbasis a x where
  basis := J.basis
  lam := J.mu
  mu := J.lam
  apply_fst := J.apply_snd
  apply_snd := J.apply_fst

@[simp] theorem swap_basis : J.swap.basis = J.basis := rfl
@[simp] theorem swap_lam : J.swap.lam = J.mu := rfl
@[simp] theorem swap_mu : J.swap.mu = J.lam := rfl

/-! ### The rank-one spectral projections -/

/-- The orthogonal projection onto the line spanned by the `k`-th joint
eigenvector, i.e. the `k`-th rank-one spectral projection of the pair. -/
noncomputable def P (k : Fin (finrank ℂ H)) : H →L[ℂ] H := (ℂ ∙ J.basis k).starProjection

theorem P_apply (k : Fin (finrank ℂ H)) (w : H) :
    J.P k w = (inner ℂ (J.basis k) w : ℂ) • J.basis k :=
  Submodule.starProjection_unit_singleton ℂ (J.norm_basis k) w

/-- Each `P k` is an orthogonal (star) projection: self-adjoint and idempotent. -/
theorem P_isStarProjection (k : Fin (finrank ℂ H)) : IsStarProjection (J.P k) :=
  isStarProjection_starProjection

theorem P_isSelfAdjoint (k : Fin (finrank ℂ H)) : IsSelfAdjoint (J.P k) :=
  (J.P_isStarProjection k).isSelfAdjoint

theorem P_apply_basis (k l : Fin (finrank ℂ H)) :
    J.P k (J.basis l) = if k = l then J.basis k else 0 := by
  rw [J.P_apply, J.inner_basis]
  by_cases h : k = l <;> simp [h]

@[simp] theorem P_apply_basis_self (k : Fin (finrank ℂ H)) : J.P k (J.basis k) = J.basis k := by
  simp [J.P_apply_basis]

theorem P_apply_basis_of_ne {k l : Fin (finrank ℂ H)} (h : k ≠ l) : J.P k (J.basis l) = 0 := by
  simp [J.P_apply_basis, h]

/-- A variant of `P_apply_basis` phrased as a scalar multiple of `basis l`, convenient
for `module`-style computations. -/
theorem P_apply_basis' (k l : Fin (finrank ℂ H)) :
    J.P k (J.basis l) = (if l = k then (1 : ℂ) else 0) • J.basis l := by
  by_cases h : k = l
  · subst h; simp
  · simp [J.P_apply_basis, h, Ne.symm h]

/-- Distinct rank-one spectral projections are orthogonal. -/
theorem P_mul_P {k l : Fin (finrank ℂ H)} (h : k ≠ l) : J.P k * J.P l = 0 := by
  refine J.ext_basis fun m => ?_
  rw [mul_apply_eq_comp, J.P_apply_basis]
  by_cases hlm : l = m
  · subst hlm
    simp [J.P_apply_basis, h]
  · simp [hlm]

@[simp] theorem P_mul_self (k : Fin (finrank ℂ H)) : J.P k * J.P k = J.P k :=
  (J.P_isStarProjection k).isIdempotentElem

/-- The rank-one spectral projections form a resolution of the identity. -/
theorem sum_P : ∑ k, J.P k = 1 := by
  refine J.ext_basis fun l => ?_
  rw [sum_apply ..]
  simp [J.P_apply_basis]

/-! ### Spectral decomposition -/

/-- The spectral decomposition of `x` in its joint eigenbasis. -/
theorem eq_sum_lam_P : x = ∑ k, (J.lam k : ℂ) • J.P k := by
  refine J.ext_basis fun l => ?_
  rw [sum_apply .., J.apply_fst]
  simp [J.P_apply_basis]

/-- The spectral decomposition of `a` in its joint eigenbasis. -/
theorem eq_sum_mu_P : a = ∑ k, (J.mu k : ℂ) • J.P k := by
  refine J.ext_basis fun l => ?_
  rw [sum_apply .., J.apply_snd]
  simp [J.P_apply_basis]

/-- An operator carrying a joint eigenbasis (with real eigenvalues) is self-adjoint. -/
theorem isSelfAdjoint_fst : IsSelfAdjoint x := by
  rw [J.eq_sum_lam_P]
  refine isSelfAdjoint_sum _ fun k _ => ?_
  exact IsSelfAdjoint.smul (Complex.conj_ofReal (J.lam k)) (J.P_isSelfAdjoint k)

/-- The second operator of a joint eigenbasis is self-adjoint. -/
theorem isSelfAdjoint_snd : IsSelfAdjoint a := J.swap.isSelfAdjoint_fst

/-- Operators sharing a joint eigenbasis commute. -/
theorem commute : Commute x a := by
  refine J.ext_basis fun k => ?_
  simp only [mul_apply_eq_comp, J.apply_fst, J.apply_snd, map_smul, smul_smul, mul_comm]

/-! ### Commutation with the spectral projections -/

/-- A self-adjoint operator having `basis k` as an eigenvector with a real
eigenvalue commutes with the corresponding rank-one projection `P k`. -/
theorem commute_P_of_eigen {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {k : Fin (finrank ℂ H)}
    {c : ℝ} (hc : T (J.basis k) = (c : ℂ) • J.basis k) : Commute T (J.P k) := by
  have hsymm : LinearMap.IsSymmetric (T : H →ₗ[ℂ] H) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  ext w
  have h1 : (inner ℂ (J.basis k) (T w) : ℂ) = (c : ℂ) * inner ℂ (J.basis k) w := by
    have h2 : (inner ℂ (J.basis k) (T w) : ℂ) = inner ℂ (T (J.basis k)) w := by
      simpa using (hsymm (J.basis k) w).symm
    rw [h2, hc, inner_smul_left]
    simp
  simp only [mul_apply_eq_comp, J.P_apply, map_smul, hc, smul_smul, h1, mul_comm]

theorem commute_fst_P (k : Fin (finrank ℂ H)) : Commute x (J.P k) :=
  J.commute_P_of_eigen J.isSelfAdjoint_fst (J.apply_fst k)

theorem commute_snd_P (k : Fin (finrank ℂ H)) : Commute a (J.P k) :=
  J.commute_P_of_eigen J.isSelfAdjoint_snd (J.apply_snd k)

/-! ### Trace -/

/-- The trace of `x` is the sum of its eigenvalues. -/
theorem trace_eq_sum_lam :
    LinearMap.trace ℂ H (x : H →ₗ[ℂ] H) = ∑ k, (J.lam k : ℂ) := by
  rw [LinearMap.trace_eq_sum_inner _ J.basis]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [J.apply_fst]

/-- The trace of `a` is the sum of its eigenvalues. -/
theorem trace_eq_sum_mu :
    LinearMap.trace ℂ H (a : H →ₗ[ℂ] H) = ∑ k, (J.mu k : ℂ) := J.swap.trace_eq_sum_lam

/-! ### The Loewner order and the eigenvalues -/

/-- A nonnegative combination of the rank-one spectral projections is a positive
operator. -/
theorem isPositive_sum_smul_P {c : Fin (finrank ℂ H) → ℝ} (hc : ∀ k, 0 ≤ c k) :
    (∑ k, (c k : ℂ) • J.P k).IsPositive := by
  refine ContinuousLinearMap.isPositive_sum _ fun k _ => ?_
  exact (ContinuousLinearMap.IsPositive.of_isStarProjection
    (J.P_isStarProjection k)).smul_of_nonneg (by exact_mod_cast hc k)

/-- If all eigenvalues of `x` are nonnegative then `0 ≤ x` in the Loewner order. -/
theorem nonneg_of_lam_nonneg (h : ∀ k, 0 ≤ J.lam k) : (0 : H →L[ℂ] H) ≤ x := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, J.eq_sum_lam_P]
  exact J.isPositive_sum_smul_P h

/-- If all eigenvalues of `x` are at most `1` then `x ≤ 1` in the Loewner order. -/
theorem le_one_of_lam_le_one (h : ∀ k, J.lam k ≤ 1) : x ≤ (1 : H →L[ℂ] H) := by
  rw [ContinuousLinearMap.le_def]
  have hrw : (1 : H →L[ℂ] H) - x = ∑ k, ((1 - J.lam k : ℝ) : ℂ) • J.P k := by
    have h1 : (∑ k, ((1 - J.lam k : ℝ) : ℂ) • J.P k)
        = (∑ k, J.P k) - ∑ k, (J.lam k : ℂ) • J.P k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      module
    rw [h1, J.sum_P, ← J.eq_sum_lam_P]
  rw [hrw]
  exact J.isPositive_sum_smul_P fun k => by linarith [h k]

/-- Conversely, `0 ≤ x` forces every eigenvalue of `x` to be nonnegative. -/
theorem lam_nonneg_of_nonneg (h : (0 : H →L[ℂ] H) ≤ x) (k : Fin (finrank ℂ H)) :
    0 ≤ J.lam k := by
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive x).mp h
  have h2 := hp.re_inner_nonneg_left (J.basis k)
  rw [J.apply_fst, inner_smul_left] at h2
  simpa using h2

/-- Conversely, `x ≤ 1` forces every eigenvalue of `x` to be at most `1`. -/
theorem lam_le_one_of_le_one (h : x ≤ (1 : H →L[ℂ] H)) (k : Fin (finrank ℂ H)) :
    J.lam k ≤ 1 := by
  have hp := (ContinuousLinearMap.le_def x 1).mp h
  have h2 := hp.re_inner_nonneg_left (J.basis k)
  rw [sub_apply, one_apply_eq_self, J.apply_fst, inner_sub_left, inner_smul_left] at h2
  simp at h2
  linarith

/-- `x` is in the operator interval `[0, 1]` exactly when all its eigenvalues are. -/
theorem mem_Icc_iff :
    ((0 : H →L[ℂ] H) ≤ x ∧ x ≤ (1 : H →L[ℂ] H)) ↔ ∀ k, J.lam k ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨fun h k => ⟨J.lam_nonneg_of_nonneg h.1 k, J.lam_le_one_of_le_one h.2 k⟩,
    fun h => ⟨J.nonneg_of_lam_nonneg fun k => (h k).1,
      J.le_one_of_lam_le_one fun k => (h k).2⟩⟩

/-! ### The projections among the operators of a joint eigenbasis -/

/-- An operator diagonal in an orthonormal basis with real eigenvalues is a star
projection exactly when all its eigenvalues are `0` or `1`. -/
theorem isStarProjection_iff : IsStarProjection x ↔ ∀ k, J.lam k = 0 ∨ J.lam k = 1 := by
  constructor
  · intro hx k
    have h := congrArg (fun T : H →L[ℂ] H => T (J.basis k)) hx.isIdempotentElem
    simp only [mul_apply_eq_comp, J.apply_fst, map_smul, smul_smul] at h
    have h2 : ((J.lam k : ℂ) * (J.lam k : ℂ)) = (J.lam k : ℂ) := by
      by_contra hne
      refine J.basis_ne_zero k ?_
      have h3 := sub_eq_zero.mpr h
      rw [← sub_smul] at h3
      rcases smul_eq_zero.mp h3 with h' | h'
      · exact absurd (sub_eq_zero.mp h') hne
      · exact h'
    have h3 : J.lam k * J.lam k = J.lam k := by exact_mod_cast h2
    have h4 : J.lam k * (J.lam k - 1) = 0 := by nlinarith [h3]
    rcases mul_eq_zero.mp h4 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by linarith [sub_eq_zero.mp h'])
  · intro h
    refine ⟨?_, J.isSelfAdjoint_fst⟩
    refine J.ext_basis fun k => ?_
    simp only [mul_apply_eq_comp, J.apply_fst, map_smul, smul_smul]
    rcases h k with hk | hk <;> rw [hk] <;> norm_num

/-! ### Perturbations: moving eigenvalue mass between two basis vectors

These are the operations Lemma 3.1 performs on an extreme point of its convex
set: they preserve the joint eigenbasis (hence the commutation with `a` and the
self-adjointness), preserve or shift the trace by a controlled amount, and stay
inside `[0, 1]` as long as the perturbed eigenvalues do. -/

/-- Adding `δ` to the `k`-th eigenvalue and subtracting `δ` from the `l`-th one:
the operator `x + δ • (P k - P l)` is still diagonal in `J.basis`, and still has
`a` as a joint partner. -/
noncomputable def shiftPair (k l : Fin (finrank ℂ H)) (δ : ℝ) :
    JointEigenbasis (x + (δ : ℂ) • (J.P k - J.P l)) a where
  basis := J.basis
  lam := fun m => J.lam m + (if m = k then δ else 0) - (if m = l then δ else 0)
  mu := J.mu
  apply_fst := by
    intro m
    rw [add_apply, smul_apply, sub_apply, J.apply_fst, J.P_apply_basis', J.P_apply_basis']
    split_ifs <;> push_cast <;> module
  apply_snd := J.apply_snd

@[simp] theorem shiftPair_basis (k l : Fin (finrank ℂ H)) (δ : ℝ) :
    (J.shiftPair k l δ).basis = J.basis := rfl

@[simp] theorem shiftPair_mu (k l : Fin (finrank ℂ H)) (δ : ℝ) :
    (J.shiftPair k l δ).mu = J.mu := rfl

theorem shiftPair_lam (k l : Fin (finrank ℂ H)) (δ : ℝ) (m : Fin (finrank ℂ H)) :
    (J.shiftPair k l δ).lam m =
      J.lam m + (if m = k then δ else 0) - (if m = l then δ else 0) := rfl

theorem shiftPair_lam_fst {k l : Fin (finrank ℂ H)} (hkl : k ≠ l) (δ : ℝ) :
    (J.shiftPair k l δ).lam k = J.lam k + δ := by
  simp [shiftPair_lam, hkl]

theorem shiftPair_lam_snd {k l : Fin (finrank ℂ H)} (hkl : k ≠ l) (δ : ℝ) :
    (J.shiftPair k l δ).lam l = J.lam l - δ := by
  simp [shiftPair_lam, hkl.symm]

theorem shiftPair_lam_of_ne {k l m : Fin (finrank ℂ H)} (hk : m ≠ k) (hl : m ≠ l) (δ : ℝ) :
    (J.shiftPair k l δ).lam m = J.lam m := by
  simp [shiftPair_lam, hk, hl]

/-- Every eigenvalue of the two-sided shift is either one of the two moved ones or an
untouched eigenvalue of `x`. -/
theorem shiftPair_lam_eq_cases {k l : Fin (finrank ℂ H)} (hkl : k ≠ l) (δ : ℝ)
    (m : Fin (finrank ℂ H)) :
    (J.shiftPair k l δ).lam m = J.lam k + δ ∨
      (J.shiftPair k l δ).lam m = J.lam l - δ ∨ (J.shiftPair k l δ).lam m = J.lam m := by
  by_cases hk : m = k
  · subst hk; exact Or.inl (J.shiftPair_lam_fst hkl δ)
  by_cases hl : m = l
  · subst hl; exact Or.inr (Or.inl (J.shiftPair_lam_snd hkl δ))
  · exact Or.inr (Or.inr (J.shiftPair_lam_of_ne hk hl δ))

/-- The two-sided shift still commutes with `a`. -/
theorem commute_shiftPair (k l : Fin (finrank ℂ H)) (δ : ℝ) :
    Commute (x + (δ : ℂ) • (J.P k - J.P l)) a := (J.shiftPair k l δ).commute

/-- The two-sided shift is self-adjoint. -/
theorem isSelfAdjoint_shiftPair (k l : Fin (finrank ℂ H)) (δ : ℝ) :
    IsSelfAdjoint (x + (δ : ℂ) • (J.P k - J.P l)) := (J.shiftPair k l δ).isSelfAdjoint_fst

/-- The two-sided shift preserves the trace. -/
theorem trace_shiftPair (k l : Fin (finrank ℂ H)) (δ : ℝ) :
    LinearMap.trace ℂ H ((x + (δ : ℂ) • (J.P k - J.P l) : H →L[ℂ] H) : H →ₗ[ℂ] H) =
      LinearMap.trace ℂ H (x : H →ₗ[ℂ] H) := by
  rw [(J.shiftPair k l δ).trace_eq_sum_lam, J.trace_eq_sum_lam]
  have hcast : ∀ m, (((J.shiftPair k l δ).lam m : ℝ) : ℂ) =
      (J.lam m : ℂ) + (if m = k then (δ : ℂ) else 0) - (if m = l then (δ : ℂ) else 0) := by
    intro m
    rw [shiftPair_lam]
    split_ifs <;> push_cast <;> ring
  simp only [hcast]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp

/-- The two-sided shift stays in the operator interval `[0, 1]` as soon as the
shifted eigenvalues do. -/
theorem shiftPair_mem_Icc (k l : Fin (finrank ℂ H)) (δ : ℝ)
    (h0 : ∀ m, 0 ≤ (J.shiftPair k l δ).lam m) (h1 : ∀ m, (J.shiftPair k l δ).lam m ≤ 1) :
    (0 : H →L[ℂ] H) ≤ x + (δ : ℂ) • (J.P k - J.P l) ∧
      x + (δ : ℂ) • (J.P k - J.P l) ≤ (1 : H →L[ℂ] H) :=
  ⟨(J.shiftPair k l δ).nonneg_of_lam_nonneg h0, (J.shiftPair k l δ).le_one_of_lam_le_one h1⟩

/-- The form in which Lemma 3.1 uses the previous statement: if `x` already lies in
`[0, 1]` eigenvalue-wise and the two moved eigenvalues stay in `[0, 1]`, then so does
the perturbed operator. -/
theorem shiftPair_mem_Icc_of {k l : Fin (finrank ℂ H)} (hkl : k ≠ l) (δ : ℝ)
    (h : ∀ m, J.lam m ∈ Set.Icc (0 : ℝ) 1) (hk : J.lam k + δ ∈ Set.Icc (0 : ℝ) 1)
    (hl : J.lam l - δ ∈ Set.Icc (0 : ℝ) 1) :
    (0 : H →L[ℂ] H) ≤ x + (δ : ℂ) • (J.P k - J.P l) ∧
      x + (δ : ℂ) • (J.P k - J.P l) ≤ (1 : H →L[ℂ] H) := by
  have key : ∀ m, (J.shiftPair k l δ).lam m ∈ Set.Icc (0 : ℝ) 1 := by
    intro m
    rcases J.shiftPair_lam_eq_cases hkl δ m with h' | h' | h' <;> rw [h']
    exacts [hk, hl, h m]
  exact J.shiftPair_mem_Icc k l δ (fun m => (key m).1) (fun m => (key m).2)

/-- Adding `δ` to the `k`-th eigenvalue only: the operator `x + δ • P k` is still
diagonal in `J.basis`, and still has `a` as a joint partner. -/
noncomputable def shiftOne (k : Fin (finrank ℂ H)) (δ : ℝ) :
    JointEigenbasis (x + (δ : ℂ) • J.P k) a where
  basis := J.basis
  lam := fun m => J.lam m + (if m = k then δ else 0)
  mu := J.mu
  apply_fst := by
    intro m
    rw [add_apply, smul_apply, J.apply_fst, J.P_apply_basis']
    split_ifs <;> push_cast <;> module
  apply_snd := J.apply_snd

@[simp] theorem shiftOne_basis (k : Fin (finrank ℂ H)) (δ : ℝ) :
    (J.shiftOne k δ).basis = J.basis := rfl

@[simp] theorem shiftOne_mu (k : Fin (finrank ℂ H)) (δ : ℝ) :
    (J.shiftOne k δ).mu = J.mu := rfl

theorem shiftOne_lam (k : Fin (finrank ℂ H)) (δ : ℝ) (m : Fin (finrank ℂ H)) :
    (J.shiftOne k δ).lam m = J.lam m + (if m = k then δ else 0) := rfl

theorem shiftOne_lam_self (k : Fin (finrank ℂ H)) (δ : ℝ) :
    (J.shiftOne k δ).lam k = J.lam k + δ := by simp [shiftOne_lam]

theorem shiftOne_lam_of_ne {k m : Fin (finrank ℂ H)} (hk : m ≠ k) (δ : ℝ) :
    (J.shiftOne k δ).lam m = J.lam m := by simp [shiftOne_lam, hk]

/-- Every eigenvalue of the one-sided shift is either the moved one or an untouched
eigenvalue of `x`. -/
theorem shiftOne_lam_eq_cases (k : Fin (finrank ℂ H)) (δ : ℝ) (m : Fin (finrank ℂ H)) :
    (J.shiftOne k δ).lam m = J.lam k + δ ∨ (J.shiftOne k δ).lam m = J.lam m := by
  by_cases hk : m = k
  · subst hk; exact Or.inl (J.shiftOne_lam_self m δ)
  · exact Or.inr (J.shiftOne_lam_of_ne hk δ)

/-- The one-sided shift still commutes with `a`. -/
theorem commute_shiftOne (k : Fin (finrank ℂ H)) (δ : ℝ) :
    Commute (x + (δ : ℂ) • J.P k) a := (J.shiftOne k δ).commute

/-- The one-sided shift is self-adjoint. -/
theorem isSelfAdjoint_shiftOne (k : Fin (finrank ℂ H)) (δ : ℝ) :
    IsSelfAdjoint (x + (δ : ℂ) • J.P k) := (J.shiftOne k δ).isSelfAdjoint_fst

/-- The one-sided shift moves the trace by exactly `δ`. -/
theorem trace_shiftOne (k : Fin (finrank ℂ H)) (δ : ℝ) :
    LinearMap.trace ℂ H ((x + (δ : ℂ) • J.P k : H →L[ℂ] H) : H →ₗ[ℂ] H) =
      LinearMap.trace ℂ H (x : H →ₗ[ℂ] H) + (δ : ℂ) := by
  rw [(J.shiftOne k δ).trace_eq_sum_lam, J.trace_eq_sum_lam]
  have hcast : ∀ m, (((J.shiftOne k δ).lam m : ℝ) : ℂ) =
      (J.lam m : ℂ) + (if m = k then (δ : ℂ) else 0) := by
    intro m
    rw [shiftOne_lam]
    split_ifs <;> push_cast <;> ring
  simp only [hcast]
  rw [Finset.sum_add_distrib]
  simp

/-- The one-sided shift stays in the operator interval `[0, 1]` as soon as the
shifted eigenvalues do. -/
theorem shiftOne_mem_Icc (k : Fin (finrank ℂ H)) (δ : ℝ)
    (h0 : ∀ m, 0 ≤ (J.shiftOne k δ).lam m) (h1 : ∀ m, (J.shiftOne k δ).lam m ≤ 1) :
    (0 : H →L[ℂ] H) ≤ x + (δ : ℂ) • J.P k ∧
      x + (δ : ℂ) • J.P k ≤ (1 : H →L[ℂ] H) :=
  ⟨(J.shiftOne k δ).nonneg_of_lam_nonneg h0, (J.shiftOne k δ).le_one_of_lam_le_one h1⟩

/-- The form in which Lemma 3.1 uses the previous statement. -/
theorem shiftOne_mem_Icc_of (k : Fin (finrank ℂ H)) (δ : ℝ)
    (h : ∀ m, J.lam m ∈ Set.Icc (0 : ℝ) 1) (hk : J.lam k + δ ∈ Set.Icc (0 : ℝ) 1) :
    (0 : H →L[ℂ] H) ≤ x + (δ : ℂ) • J.P k ∧
      x + (δ : ℂ) • J.P k ≤ (1 : H →L[ℂ] H) := by
  have key : ∀ m, (J.shiftOne k δ).lam m ∈ Set.Icc (0 : ℝ) 1 := by
    intro m
    rcases J.shiftOne_lam_eq_cases k δ m with h' | h' <;> rw [h']
    exacts [hk, h m]
  exact J.shiftOne_mem_Icc k δ (fun m => (key m).1) (fun m => (key m).2)

end JointEigenbasis

end Orthogonalization.FinDim
