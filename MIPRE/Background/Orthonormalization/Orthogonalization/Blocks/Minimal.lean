/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Blocks/Minimal.lean
-/
/-
# Tier T1b: minimal projections and the central decomposition (finite dimension)

The elementary structure of a von Neumann algebra `M` on a finite-dimensional
Hilbert space needed to cut Theorem 1.2 into blocks (`PLAN.md` §8, T1b):

* the projection onto an eigenspace of an element of `M` lies in `M`
  (`eigenspace_starProjection_mem`) — the bicommutant property in its most
  elementary form, and the only "spectral" input used in this tier;
* minimal projections below a given nonzero projection of `M` exist
  (`exists_isMinimalProjIn`, by minimizing the rank) and satisfy `e M e = ℂ e`
  on self-adjoint elements (`exists_eq_smul_of_isMinimalProjIn`);
* every central projection is a finite orthogonal sum of *minimal* central
  projections (`exists_minimal_central_decomposition` for `z = 1`), by strong
  induction on the rank.

Everything here is proof-side; no statement of the paper is encoded.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.JointDiag
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Local

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.Blocks

open scoped BigOperators ComplexOrder
open Module

/-! ### Projections and their ranges -/

section Projections

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

-- Several lemmas of this section hold in any complete space; finite-dimensionality is
-- assumed throughout only so that every range has an orthogonal projection.
set_option linter.unusedSectionVars false

theorem proj_apply_eq_self_of_mem_range {e : H →L[ℂ] H} (he : IsStarProjection e) {w : H}
    (hw : w ∈ LinearMap.range (e : H →ₗ[ℂ] H)) : e w = w := by
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
  show e (e u) = e u
  rw [← mul_apply_eq_comp, he.isIdempotentElem.eq]

theorem mul_eq_self_of_range_le {e f : H →L[ℂ] H} (he : IsStarProjection e)
    (h : LinearMap.range (f : H →ₗ[ℂ] H) ≤ LinearMap.range (e : H →ₗ[ℂ] H)) : e * f = f := by
  ext v
  rw [mul_apply_eq_comp]
  exact proj_apply_eq_self_of_mem_range he (h (LinearMap.mem_range_self _ v))

theorem range_le_of_mul_eq {e f : H →L[ℂ] H} (h : e * f = f) :
    LinearMap.range (f : H →ₗ[ℂ] H) ≤ LinearMap.range (e : H →ₗ[ℂ] H) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨f v, ?_⟩
  show e (f v) = f v
  rw [← mul_apply_eq_comp, h]

theorem starProjection_range_eq {e : H →L[ℂ] H} (he : IsStarProjection e) :
    (LinearMap.range (e : H →ₗ[ℂ] H)).starProjection = e := by
  obtain ⟨_, h⟩ := isStarProjection_iff_eq_starProjection_range.mp he
  exact h.symm

/-- Two projections with the same range are equal. -/
theorem eq_of_range_eq {e f : H →L[ℂ] H} (he : IsStarProjection e) (hf : IsStarProjection f)
    (h : LinearMap.range (e : H →ₗ[ℂ] H) = LinearMap.range (f : H →ₗ[ℂ] H)) : e = f := by
  have h1 : f * e = e := mul_eq_self_of_range_le hf h.le
  have h2 : e * f = f := mul_eq_self_of_range_le he h.ge
  calc e = star e := he.isSelfAdjoint.star_eq.symm
    _ = star (f * e) := by rw [h1]
    _ = e * f := by rw [star_mul, he.isSelfAdjoint.star_eq, hf.isSelfAdjoint.star_eq]
    _ = f := h2

/-- The projection onto an eigenspace of an element of `M` belongs to `M`: the
eigenspace is invariant under the commutant. -/
theorem eigenspace_starProjection_mem (M : VonNeumannAlgebra H) {x : H →L[ℂ] H} (hx : x ∈ M)
    (μ : ℂ) : (Module.End.eigenspace (x : H →ₗ[ℂ] H) μ).starProjection ∈ M := by
  rw [VonNeumannAlgebra.IsStarProjection.mem_iff isStarProjection_starProjection]
  intro y hy
  rw [Submodule.range_starProjection, Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have hxy : x * y = y * x := VonNeumannAlgebra.mem_commutant_iff.mp hy x hx
  show x (y v) = μ • y v
  rw [← mul_apply_eq_comp, hxy, mul_apply_eq_comp]
  have hv' : x v = μ • v := hv
  rw [hv', map_smul]

end Projections

/-! ### Minimal projections -/

section Minimal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- `e` is a minimal projection of `M` below the projection `z`: a nonzero projection
of `M` with `e ≤ z` such that every projection of `M` below `e` is `0` or `e`. -/
structure IsMinimalProjIn (M : VonNeumannAlgebra H) (z e : H →L[ℂ] H) : Prop where
  mem : e ∈ M
  isStarProjection : IsStarProjection e
  ne_zero : e ≠ 0
  mul_eq : e * z = e
  minimal : ∀ f ∈ M, IsStarProjection f → f * e = f → f = 0 ∨ f = e

/-- Below every nonzero projection of `M` there is a minimal projection of `M`
(one of least rank). -/
theorem exists_isMinimalProjIn (M : VonNeumannAlgebra H) {z : H →L[ℂ] H}
    (hz : IsStarProjection z) (hzM : z ∈ M) (hz0 : z ≠ 0) : ∃ e, IsMinimalProjIn M z e := by
  classical
  let P : ℕ → Prop := fun n => ∃ f : H →L[ℂ] H, f ∈ M ∧ IsStarProjection f ∧ f ≠ 0 ∧
    f * z = f ∧ finrank ℂ (LinearMap.range (f : H →ₗ[ℂ] H)) = n
  have hP : ∃ n, P n := ⟨_, z, hzM, hz, hz0, hz.isIdempotentElem.eq, rfl⟩
  obtain ⟨e, heM, he, he0, hez, hrank⟩ := Nat.find_spec hP
  refine ⟨e, heM, he, he0, hez, ?_⟩
  intro f hfM hf hfe
  by_cases hf0 : f = 0
  · exact Or.inl hf0
  right
  have hef : e * f = f := proj_mul_left_of_mul_right hf he hfe
  have hle : LinearMap.range (f : H →ₗ[ℂ] H) ≤ LinearMap.range (e : H →ₗ[ℂ] H) :=
    range_le_of_mul_eq hef
  have hfz : f * z = f := by rw [← hfe, mul_assoc, hez]
  have hmin : Nat.find hP ≤ finrank ℂ (LinearMap.range (f : H →ₗ[ℂ] H)) :=
    Nat.find_min' hP ⟨f, hfM, hf, hf0, hfz, rfl⟩
  have hge : finrank ℂ (LinearMap.range (f : H →ₗ[ℂ] H)) ≤
      finrank ℂ (LinearMap.range (e : H →ₗ[ℂ] H)) := Submodule.finrank_mono hle
  rw [← hrank] at hmin
  exact eq_of_range_eq hf he (Submodule.eq_of_le_of_finrank_eq hle (le_antisymm hge hmin))

/-- **`e M e = ℂ e`.** A self-adjoint element of `M` supported in a minimal projection
`e` (`e x e = x`) is a real multiple of `e`. -/
theorem exists_eq_smul_of_isMinimalProjIn (M : VonNeumannAlgebra H) {z e : H →L[ℂ] H}
    (he : IsMinimalProjIn M z e) {x : H →L[ℂ] H} (hx : x ∈ M) (hxsa : IsSelfAdjoint x)
    (hex : e * x * e = x) : ∃ c : ℝ, x = (c : ℂ) • e := by
  classical
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  obtain ⟨J⟩ := FinDim.exists_jointEigenbasis hxsa hxsa (Commute.refl x)
  have hne : ∃ k, J.lam k ≠ 0 := by
    by_contra h
    have h' : ∀ k, J.lam k = 0 := fun k => not_not.mp (not_exists.mp h k)
    apply hx0
    rw [J.eq_sum_lam_P]
    simp [h']
  obtain ⟨k, hk⟩ := hne
  set μ : ℝ := J.lam k with hμ
  set W := Module.End.eigenspace (x : H →ₗ[ℂ] H) (μ : ℂ) with hW
  set P := W.starProjection with hPdef
  have hPM : P ∈ M := eigenspace_starProjection_mem M hx _
  have hP : IsStarProjection P := isStarProjection_starProjection
  have hbW : J.basis k ∈ W := by
    rw [hW, Module.End.mem_eigenspace_iff]
    exact J.apply_fst k
  have hP0 : P ≠ 0 := by
    intro h
    have h1 : P (J.basis k) = J.basis k := Submodule.starProjection_eq_self_iff.mpr hbW
    rw [h] at h1
    exact J.basis_ne_zero k (by simpa using h1.symm)
  have hxe : x * e = x := by
    calc x * e = e * x * e * e := by rw [hex]
      _ = e * x * e := by rw [mul_assoc, he.isStarProjection.isIdempotentElem.eq]
      _ = x := hex
  have hWe : W ≤ LinearMap.range (e : H →ₗ[ℂ] H) := by
    intro v hv
    rw [hW, Module.End.mem_eigenspace_iff] at hv
    have hxv : x v = (μ : ℂ) • v := hv
    refine ⟨((μ : ℂ)⁻¹) • (x * e) v, ?_⟩
    show e (((μ : ℂ)⁻¹) • (x * e) v) = v
    rw [map_smul, ← mul_apply_eq_comp, ← mul_assoc, hex, hxv, smul_smul,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hk), one_smul]
  have hPe : P * e = P := by
    have h1 : e * P = P := mul_eq_self_of_range_le he.isStarProjection
      (by rw [hPdef, Submodule.range_starProjection]; exact hWe)
    have := congrArg star h1
    rwa [star_mul, hP.isSelfAdjoint.star_eq, he.isStarProjection.isSelfAdjoint.star_eq] at this
  rcases he.minimal P hPM hP hPe with h | h
  · exact absurd h hP0
  refine ⟨μ, ?_⟩
  ext v
  rw [smul_apply]
  have hev : e v ∈ W := by
    rw [← h]
    exact Submodule.starProjection_apply_mem W v
  rw [hW, Module.End.mem_eigenspace_iff] at hev
  have hev' : x (e v) = (μ : ℂ) • e v := hev
  calc x v = x (e v) := by rw [← mul_apply_eq_comp, hxe]
    _ = (μ : ℂ) • e v := hev'

end Minimal

/-! ### The central decomposition -/

section Central

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A minimal central projection of `M`: a nonzero central projection such that every
central projection below it is `0` or itself. -/
structure IsMinimalCentral (M : VonNeumannAlgebra H) (z : H →L[ℂ] H) : Prop where
  isCentralProj : IsCentralProj M z
  ne_zero : z ≠ 0
  minimal : ∀ z', IsCentralProj M z' → z' * z = z' → z' = 0 ∨ z' = z

theorem IsCentralProj.sub {M : VonNeumannAlgebra H} {z z' : H →L[ℂ] H} (hz : IsCentralProj M z)
    (hz' : IsCentralProj M z') (hz'z : z' * z = z') : IsCentralProj M (z - z') := by
  have hzz' : z * z' = z' := by
    rw [(hz.commute z' hz'.mem).eq, hz'z]
  refine ⟨⟨?_, ?_⟩, sub_mem hz.mem hz'.mem, fun x hx => (hz.commute x hx).sub_left (hz'.commute x hx)⟩
  · show (z - z') * (z - z') = z - z'
    rw [sub_mul, mul_sub, mul_sub, hz.isStarProjection.isIdempotentElem.eq, hzz', hz'z,
      hz'.isStarProjection.isIdempotentElem.eq]
    abel
  · rw [IsSelfAdjoint, star_sub, hz.isStarProjection.isSelfAdjoint.star_eq,
      hz'.isStarProjection.isSelfAdjoint.star_eq]

/-- Every central projection `z` of `M` is an orthogonal sum of minimal central
projections below `z` (strong induction on the rank of `z`). -/
theorem exists_minimal_central_decomposition_below (M : VonNeumannAlgebra H) :
    ∀ n : ℕ, ∀ z : H →L[ℂ] H, IsCentralProj M z →
      finrank ℂ (LinearMap.range (z : H →ₗ[ℂ] H)) = n →
      ∃ (κ : Type) (_ : Fintype κ) (w : κ → H →L[ℂ] H),
        (∀ j, IsMinimalCentral M (w j)) ∧ (∀ j, w j * z = w j) ∧
        (∀ j k, j ≠ k → w j * w k = 0) ∧ ∑ j, w j = z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z hz hn
  by_cases hz0 : z = 0
  · exact ⟨Empty, inferInstance, fun j => j.elim, fun j => j.elim, fun j => j.elim,
      fun j => j.elim, by simp [hz0]⟩
  by_cases hmin : ∀ z', IsCentralProj M z' → z' * z = z' → z' = 0 ∨ z' = z
  · exact ⟨Unit, inferInstance, fun _ => z, fun _ => ⟨hz, hz0, hmin⟩,
      fun _ => hz.isStarProjection.isIdempotentElem.eq,
      fun j k hjk => absurd (Subsingleton.elim j k) hjk, by simp⟩
  obtain ⟨z', hz', hz'z, hz'0, hz'ne⟩ :
      ∃ z', IsCentralProj M z' ∧ z' * z = z' ∧ z' ≠ 0 ∧ z' ≠ z := by
    by_contra hcon
    apply hmin
    intro z' h1 h2
    by_contra h3
    exact hcon ⟨z', h1, h2, fun h => h3 (Or.inl h), fun h => h3 (Or.inr h)⟩
  have hzz' : z * z' = z' := by rw [(hz.commute z' hz'.mem).eq, hz'z]
  have hz'' : IsCentralProj M (z - z') := hz.sub hz' hz'z
  have hz''z : (z - z') * z = z - z' := by
    rw [sub_mul, hz.isStarProjection.isIdempotentElem.eq, hz'z]
  have hz''0 : z - z' ≠ 0 := fun h => hz'ne (sub_eq_zero.mp h).symm
  -- both pieces have smaller rank
  have hrank : ∀ y : H →L[ℂ] H, IsStarProjection y → z * y = y → y ≠ z →
      finrank ℂ (LinearMap.range (y : H →ₗ[ℂ] H)) < n := by
    intro y hy hzy hyz
    rw [← hn]
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (range_le_of_mul_eq hzy) ?_)
    intro heq
    exact hyz (eq_of_range_eq hy hz.isStarProjection heq)
  have hr1 := hrank z' hz'.isStarProjection hzz' hz'ne
  have hr2 := hrank (z - z') hz''.isStarProjection
    (by rw [mul_sub, hz.isStarProjection.isIdempotentElem.eq, hzz'])
    (fun h => hz'0 (by rwa [sub_eq_self] at h))
  obtain ⟨κ₁, _, w₁, hw₁, hw₁z, hw₁o, hw₁s⟩ := ih _ hr1 z' hz' rfl
  obtain ⟨κ₂, _, w₂, hw₂, hw₂z, hw₂o, hw₂s⟩ := ih _ hr2 (z - z') hz'' rfl
  have hz'z'' : z' * (z - z') = 0 := by
    rw [mul_sub, hz'z, hz'.isStarProjection.isIdempotentElem.eq, sub_self]
  refine ⟨κ₁ ⊕ κ₂, inferInstance, Sum.elim w₁ w₂, ?_, ?_, ?_, ?_⟩
  · rintro (j | j)
    · exact hw₁ j
    · exact hw₂ j
  · rintro (j | j)
    · show w₁ j * z = w₁ j
      rw [← hw₁z j, mul_assoc, hz'z]
    · show w₂ j * z = w₂ j
      rw [← hw₂z j, mul_assoc, hz''z]
  · -- cross terms vanish
    have hcross : ∀ j k, w₁ j * w₂ k = 0 := by
      intro j k
      have h2 : (z - z') * w₂ k = w₂ k := by
        rw [← ((hw₂ k).isCentralProj.commute _ hz''.mem).eq, hw₂z k]
      rw [← hw₁z j, ← h2, mul_assoc, ← mul_assoc z', hz'z'', zero_mul, mul_zero]
    rintro (j | j) (k | k) hjk
    · exact hw₁o j k (fun h => hjk (by rw [h]))
    · exact hcross j k
    · show w₂ j * w₁ k = 0
      rw [((hw₂ j).isCentralProj.commute _ (hw₁ k).isCentralProj.mem).eq]
      exact hcross k j
    · exact hw₂o j k (fun h => hjk (by rw [h]))
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hw₁s, hw₂s]
    abel

/-- **The central decomposition.** `1` is an orthogonal sum of minimal central
projections of `M`. -/
theorem exists_minimal_central_decomposition (M : VonNeumannAlgebra H) :
    ∃ (κ : Type) (_ : Fintype κ) (z : κ → H →L[ℂ] H),
      (∀ j, IsMinimalCentral M (z j)) ∧ (∀ j k, j ≠ k → z j * z k = 0) ∧ ∑ j, z j = 1 := by
  have h1 : IsCentralProj M 1 :=
    ⟨IsStarProjection.one _, one_mem M, fun x _ => Commute.one_left x⟩
  obtain ⟨κ, _, w, hw, _, hwo, hws⟩ := exists_minimal_central_decomposition_below M _ 1 h1 rfl
  exact ⟨κ, inferInstance, w, hw, hwo, hws⟩

end Central

end Orthogonalization.Blocks
