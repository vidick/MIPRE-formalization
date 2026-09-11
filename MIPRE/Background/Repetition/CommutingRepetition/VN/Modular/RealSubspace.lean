/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/RealSubspace.lean
-/
/-
# The standard subspace of a cyclic separating vector (stage E4.1; Rieffel–van Daele Prop. 4.1)

For a von Neumann algebra `M ⊆ B(K)` with a cyclic separating vector `Ω`, the
closed real subspace `𝒦 := closure {a Ω | a ∈ M, a = a*}` satisfies
`𝒦 ∩ i𝒦 = 0` and `𝒦 + i𝒦` dense, i.e. it is a `StandardSubspace` in the sense
of Mathlib (`Mathlib/Analysis/InnerProductSpace/StandardSubspace.lean`), and
`M′_s Ω ⊆ (i𝒦)^⊥` (real orthogonal complement, Mathlib's `symplComp`).
Source: Rieffel–van Daele, *A bounded operator approach to Tomita–Takesaki
theory*, Pacific J. Math. 69 (1977), Proposition 4.1 (`PLAN-tomita.md` §0.1).
Proof-side infrastructure for the modular theory of stage E4.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Cutdown

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Modular

open scoped InnerProductSpace
open Filter Topology ClosedSubmodule

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Self-adjoint decompositions -/

theorem isSelfAdjoint_half_add_star (y : K →L[ℂ] K) :
    IsSelfAdjoint ((1 / 2 : ℂ) • (y + star y)) := by
  rw [IsSelfAdjoint, star_smul, star_add, star_star, add_comm]
  congr 1
  simp

theorem isSelfAdjoint_half_I_sub_star (y : K →L[ℂ] K) :
    IsSelfAdjoint ((-(1 / 2 : ℂ) * Complex.I) • (y - star y)) := by
  rw [IsSelfAdjoint, star_smul, star_sub, star_star]
  have : star (-(1 / 2 : ℂ) * Complex.I) = (1 / 2 : ℂ) * Complex.I := by
    simp
  rw [this, ← neg_sub, smul_neg, ← neg_smul, neg_mul]

/-- `y = a + i b` with `a = (y + y*)/2`, `b = -(i/2)(y − y*)` self-adjoint. -/
theorem eq_sa_add_I_smul_sa (y : K →L[ℂ] K) :
    y = (1 / 2 : ℂ) • (y + star y) + Complex.I • ((-(1 / 2 : ℂ) * Complex.I) • (y - star y)) := by
  rw [smul_smul, smul_add, smul_sub]
  have h1 : Complex.I * (-(1 / 2 : ℂ) * Complex.I) = 1 / 2 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [h1]
  module

/-- A vector orthogonal to `a Ω` for every self-adjoint `a` in a von Neumann algebra `N` is
orthogonal to `N Ω`. -/
theorem inner_eq_zero_of_sa (N : VonNeumannAlgebra K) (Ω x : K)
    (h : ∀ a ∈ N, IsSelfAdjoint a → ⟪x, a Ω⟫_ℂ = 0) {y : K →L[ℂ] K} (hy : y ∈ N) :
    ⟪x, y Ω⟫_ℂ = 0 := by
  obtain ⟨a, ha, hsa, rfl⟩ : ∃ a, a ∈ N ∧ IsSelfAdjoint a ∧ (1 / 2 : ℂ) • (y + star y) = a :=
    ⟨_, smul_mem_vn N _ (add_mem hy (star_mem hy)), isSelfAdjoint_half_add_star y, rfl⟩
  obtain ⟨b, hb, hsb, rfl⟩ : ∃ b, b ∈ N ∧ IsSelfAdjoint b ∧
      (-(1 / 2 : ℂ) * Complex.I) • (y - star y) = b :=
    ⟨_, smul_mem_vn N _ (sub_mem hy (star_mem hy)), isSelfAdjoint_half_I_sub_star y, rfl⟩
  have hy' := eq_sa_add_I_smul_sa y
  rw [hy', _root_.add_apply, inner_add_right, h _ ha hsa, _root_.smul_apply, inner_smul_right,
    h _ hb hsb, mul_zero, add_zero]

theorem inner_eq_zero_of_sa' (N : VonNeumannAlgebra K) (Ω x : K)
    (h : ∀ a ∈ N, IsSelfAdjoint a → ⟪a Ω, x⟫_ℂ = 0) {y : K →L[ℂ] K} (hy : y ∈ N) :
    ⟪y Ω, x⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_eq_zero_of_sa N Ω x (fun a ha hsa => ?_) hy, map_zero]
  rw [← inner_conj_symm, h a ha hsa, map_zero]

/-- A vector orthogonal to `N Ω` for a von Neumann algebra `N` with `N Ω` dense is zero. -/
theorem eq_zero_of_inner_orbit (N : VonNeumannAlgebra K) {Ω : K}
    (hd : Dense (orbit (N : Set (K →L[ℂ] K)) Ω : Set K)) {x : K}
    (h : ∀ y ∈ N, ⟪x, y Ω⟫_ℂ = 0) : x = 0 := by
  have hx : x ∈ (orbit (N : Set (K →L[ℂ] K)) Ω)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    refine Submodule.span_induction (p := fun u _ => ⟪x, u⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨y, hy, rfl⟩
      exact h y hy
    · simp
    · intro u v _ _ hu hv
      rw [inner_add_right, hu, hv, add_zero]
    · intro c u _ hu
      rw [inner_smul_right, hu, mul_zero]
  rw [← Submodule.orthogonal_closure, Submodule.dense_iff_topologicalClosure_eq_top.mp hd,
    Submodule.top_orthogonal_eq_bot] at hx
  exact (Submodule.mem_bot ℂ).mp hx

/-! ## The real subspace `𝒦 = closure (M_s Ω)` -/

variable (M : VonNeumannAlgebra K) (Ω : K)

/-- `{a Ω | a ∈ M self-adjoint}`. -/
def saOrbitSet : Set K := {v | ∃ a ∈ M, IsSelfAdjoint a ∧ a Ω = v}

/-- The real span of `M_s Ω` (already a real subspace, taken as a span for convenience). -/
noncomputable def saOrbit : Submodule ℝ K := Submodule.span ℝ (saOrbitSet M Ω)

/-- The closed real subspace `𝒦 = closure (M_s Ω)`. -/
noncomputable def Kre : ClosedSubmodule ℝ K := (saOrbit M Ω).closure

theorem mem_saOrbitSet {a : K →L[ℂ] K} (ha : a ∈ M) (hsa : IsSelfAdjoint a) :
    a Ω ∈ saOrbitSet M Ω := ⟨a, ha, hsa, rfl⟩

theorem saOrbit_le_Kre : saOrbit M Ω ≤ (Kre M Ω).toSubmodule :=
  Submodule.le_topologicalClosure _

theorem mem_Kre_of_sa {a : K →L[ℂ] K} (ha : a ∈ M) (hsa : IsSelfAdjoint a) : a Ω ∈ Kre M Ω :=
  saOrbit_le_Kre M Ω (Submodule.subset_span (mem_saOrbitSet M Ω ha hsa))

theorem Ω_mem_Kre : Ω ∈ Kre M Ω := by
  have := mem_Kre_of_sa M Ω (one_mem M) ((IsSelfAdjoint.one _))
  rwa [one_apply_eq_self] at this

theorem mem_Kre_iff {x : K} : x ∈ Kre M Ω ↔ x ∈ closure (saOrbit M Ω : Set K) := by
  change x ∈ (saOrbit M Ω).topologicalClosure ↔ _
  rw [← Submodule.topologicalClosure_coe]
  rfl

/-- Induction principle for `𝒦`: a closed property holding on `M_s Ω` and stable under real
linear combinations holds on `𝒦`. -/
theorem Kre_induction {p : K → Prop} (hp : IsClosed {x | p x})
    (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y)) (hsmul : ∀ (c : ℝ) x, p x → p (c • x))
    (hgen : ∀ a ∈ M, IsSelfAdjoint a → p (a Ω)) {x : K} (hx : x ∈ Kre M Ω) : p x := by
  rw [mem_Kre_iff] at hx
  refine closure_minimal (fun y hy => ?_) hp hx
  refine Submodule.span_induction (p := fun y _ => p y) ?_ h0 ?_ ?_ hy
  · rintro _ ⟨a, ha, hsa, rfl⟩
    exact hgen a ha hsa
  · intro u v _ _ hu hv
    exact hadd u v hu hv
  · intro c u _ hu
    exact hsmul c u hu

/-- `⟪x, a′ Ω⟫` is real for `x ∈ 𝒦` and self-adjoint `a′ ∈ M′` (RvD Prop. 4.1). -/
theorem im_inner_commutant_sa {x : K} (hx : x ∈ Kre M Ω) {a' : K →L[ℂ] K}
    (ha' : a' ∈ M.commutant) (hsa' : IsSelfAdjoint a') : (⟪x, a' Ω⟫_ℂ).im = 0 := by
  refine Kre_induction M Ω (p := fun x => (⟪x, a' Ω⟫_ℂ).im = 0) ?_ ?_ ?_ ?_ ?_ hx
  · exact isClosed_eq (Complex.continuous_im.comp (continuous_id.inner continuous_const))
      continuous_const
  · simp
  · intro u v hu hv
    simp only [inner_add_left, Complex.add_im, hu, hv, add_zero]
  · intro c u hu
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left, Complex.smul_im, hu,
      smul_zero]
  · intro a ha hsa
    -- `⟪aΩ, a′Ω⟫ = ⟪Ω, (a a′) Ω⟫` with `a a′` self-adjoint
    have hcomm : a * a' = a' * a := (commutant_mul_of_mem ha ha').symm
    have hsa2 : IsSelfAdjoint (a * a') := by
      rw [IsSelfAdjoint, star_mul, hsa.star_eq, hsa'.star_eq, hcomm]
    have : ⟪a Ω, a' Ω⟫_ℂ = ⟪Ω, (a * a') Ω⟫_ℂ := by
      rw [mul_apply_eq_comp, ← BorelCalc.inner_sa hsa]
    rw [this]
    exact BorelCalc.inner_self_im hsa2 Ω

/-- `M′_s Ω ⊆ (i𝒦)^⊥`: the self-adjoint commutant orbit lies in the symplectic complement. -/
theorem commutant_sa_mem_symplComp {a' : K →L[ℂ] K} (ha' : a' ∈ M.commutant)
    (hsa' : IsSelfAdjoint a') : a' Ω ∈ (Kre M Ω).symplComp := by
  rw [mem_symplComp_iff]
  intro y hy
  exact im_inner_commutant_sa M Ω hy ha' hsa'

theorem Ω_mem_symplComp : Ω ∈ (Kre M Ω).symplComp := by
  have := commutant_sa_mem_symplComp M Ω (one_mem M.commutant) ((IsSelfAdjoint.one _))
  rwa [one_apply_eq_self] at this

theorem mem_mulI_Kre_iff {x : K} : x ∈ (Kre M Ω).mulI ↔ (-Complex.I) • x ∈ Kre M Ω := by
  rw [mulI, mem_mapEquiv_iff, scalarSMulCLE_symm_apply]
  simp [Units.smul_def, Complex.UnitI]

theorem I_smul_mem_mulI_Kre {x : K} (hx : x ∈ Kre M Ω) : Complex.I • x ∈ (Kre M Ω).mulI := by
  rw [mem_mulI_Kre_iff, smul_smul]
  simpa using hx

/-! ## The standard subspace (RvD Prop. 4.1) -/

variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

include hs in
/-- `𝒦 ∩ i𝒦 = 0`: a vector in both is orthogonal to `M′ Ω`, which is dense since `Ω` is separating
for `M`. -/
theorem Kre_inf_mulI : Kre M Ω ⊓ (Kre M Ω).mulI = ⊥ := by
  rw [eq_bot_iff, SetLike.le_def]
  intro x hx
  rw [ClosedSubmodule.mem_inf] at hx
  rw [ClosedSubmodule.mem_bot]
  obtain ⟨hx, hix⟩ := hx
  rw [mem_mulI_Kre_iff] at hix
  refine eq_zero_of_inner_orbit M.commutant hs.isCyclic_commutant fun y hy => ?_
  refine inner_eq_zero_of_sa M.commutant Ω x (fun a' ha' hsa' => ?_) hy
  have h1 := im_inner_commutant_sa M Ω hx ha' hsa'
  have h2 := im_inner_commutant_sa M Ω hix ha' hsa'
  rw [inner_smul_left, map_neg, Complex.conj_I, neg_neg, Complex.I_mul_im] at h2
  exact Complex.ext h2 h1

include hc in
/-- `𝒦 + i𝒦` is dense: a vector real-orthogonal to both is orthogonal to `M Ω`. -/
theorem Kre_sup_mulI : Kre M Ω ⊔ (Kre M Ω).mulI = ⊤ := by
  apply ClosedSubmodule.toSubmodule_injective
  rw [ClosedSubmodule.toSubmodule_sup, ClosedSubmodule.toSubmodule_top]
  change ((Kre M Ω).toSubmodule ⊔ (Kre M Ω).mulI.toSubmodule).topologicalClosure = ⊤
  rw [Submodule.topologicalClosure_eq_top_iff, ← Submodule.inf_orthogonal]
  rw [Submodule.eq_bot_iff]
  intro z hz
  rw [Submodule.mem_inf, Submodule.mem_orthogonal, Submodule.mem_orthogonal] at hz
  refine eq_zero_of_inner_orbit M hc fun y hy => ?_
  rw [← inner_conj_symm]
  rw [inner_eq_zero_of_sa' M Ω z (fun a ha hsa => ?_) hy, map_zero]
  have h1 := hz.1 (a Ω) (mem_Kre_of_sa M Ω ha hsa)
  have h2 := hz.2 (Complex.I • a Ω) (I_smul_mem_mulI_Kre M Ω (mem_Kre_of_sa M Ω ha hsa))
  rw [inner_real_eq_re_inner] at h1 h2
  rw [inner_smul_left, Complex.conj_I, neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] at h2
  exact Complex.ext h1 h2

/-- The standard subspace `𝒦 = closure (M_s Ω)` of a cyclic separating vector. -/
noncomputable def standardSubspace : StandardSubspace K where
  toClosedSubmodule := Kre M Ω
  IsSeparating := Kre_inf_mulI M Ω hs
  IsCyclic := Kre_sup_mulI M Ω hc

theorem standardSubspace_toClosedSubmodule :
    (standardSubspace M Ω hs hc).toClosedSubmodule = Kre M Ω := rfl

end Modular

end VN

end CommutingRepetition
