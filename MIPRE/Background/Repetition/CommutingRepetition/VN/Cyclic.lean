/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Cyclic.lean
-/
/-
# Cyclic and separating vectors (density stage E3.3)

For a von Neumann algebra `N ⊆ B(H)` and `ξ ∈ H`: the cyclic subspace `[N ξ]`,
its projection (which lies in the commutant `N′`), the notions *cyclic* (`N ξ`
dense) and *separating* (`x ξ = 0 ⇒ x = 0` on `N`), the equivalence
"`ξ` separating for `N` ⟺ `ξ` cyclic for `N′`" (Kadison–Ringrose 5.5.11; only
`N = N″` is used), and the upgrade from convergence at a separating vector to
bounded strong convergence, used for the Haagerup expectations `Φ_n(x) → x`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Generated
import MIPRE.Background.Repetition.CommutingRepetition.VN.Normal

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

open scoped InnerProductSpace
open Filter Topology

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The cyclic subspace -/

/-- The linear span of `{x ξ | x ∈ S}`. -/
def orbit (S : Set (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H :=
  Submodule.span ℂ ((fun x : H →L[ℂ] H => x ξ) '' S)

/-- The closed cyclic subspace `[S ξ]`. -/
def cyclicSpace (S : Set (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H :=
  (orbit S ξ).topologicalClosure

theorem isClosed_cyclicSpace (S : Set (H →L[ℂ] H)) (ξ : H) :
    IsClosed (cyclicSpace S ξ : Set H) :=
  Submodule.isClosed_topologicalClosure _

instance completeSpace_cyclicSpace (S : Set (H →L[ℂ] H)) (ξ : H) :
    CompleteSpace (cyclicSpace S ξ) :=
  (isClosed_cyclicSpace S ξ).completeSpace_coe

theorem apply_mem_orbit {S : Set (H →L[ℂ] H)} {ξ : H} {x : H →L[ℂ] H} (hx : x ∈ S) :
    x ξ ∈ orbit S ξ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem orbit_le_cyclicSpace (S : Set (H →L[ℂ] H)) (ξ : H) : orbit S ξ ≤ cyclicSpace S ξ :=
  Submodule.le_topologicalClosure _

theorem apply_mem_cyclicSpace {S : Set (H →L[ℂ] H)} {ξ : H} {x : H →L[ℂ] H} (hx : x ∈ S) :
    x ξ ∈ cyclicSpace S ξ :=
  orbit_le_cyclicSpace S ξ (apply_mem_orbit hx)

theorem mem_cyclicSpace_self (N : VonNeumannAlgebra H) (ξ : H) : ξ ∈ cyclicSpace (N : Set _) ξ := by
  have := apply_mem_cyclicSpace (ξ := ξ) (one_mem N)
  simpa using this

/-- The orbit of a von Neumann algebra is invariant under the algebra. -/
theorem apply_mem_orbit_of_mem (N : VonNeumannAlgebra H) (ξ : H) {x : H →L[ℂ] H} (hx : x ∈ N)
    {v : H} (hv : v ∈ orbit (N : Set _) ξ) : x v ∈ orbit (N : Set _) ξ := by
  refine Submodule.span_induction (p := fun w _ => x w ∈ orbit (N : Set _) ξ) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨y, hy, rfl⟩
    have : x (y ξ) = (x * y) ξ := rfl
    rw [this]
    exact apply_mem_orbit (mul_mem hx hy)
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · intro u v _ _ hu hv
    rw [map_add]
    exact Submodule.add_mem _ hu hv
  · intro c u _ hu
    rw [map_smul]
    exact Submodule.smul_mem _ c hu

/-- The cyclic subspace of a von Neumann algebra is invariant under the algebra. -/
theorem apply_mem_cyclicSpace_of_mem (N : VonNeumannAlgebra H) (ξ : H) {x : H →L[ℂ] H}
    (hx : x ∈ N) {v : H} (hv : v ∈ cyclicSpace (N : Set _) ξ) :
    x v ∈ cyclicSpace (N : Set _) ξ := by
  have hv' : v ∈ closure (orbit (N : Set _) ξ : Set H) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hv
  have := map_mem_closure x.continuous hv' fun w hw => apply_mem_orbit_of_mem N ξ hx hw
  rw [← Submodule.topologicalClosure_coe] at this
  exact this

/-- The projection onto the cyclic subspace `[N ξ]`. -/
noncomputable def cycProj (N : VonNeumannAlgebra H) (ξ : H) : H →L[ℂ] H :=
  (cyclicSpace (N : Set _) ξ).starProjection

theorem cycProj_isStarProjection (N : VonNeumannAlgebra H) (ξ : H) :
    IsStarProjection (cycProj N ξ) :=
  isStarProjection_starProjection

theorem cycProj_range (N : VonNeumannAlgebra H) (ξ : H) :
    (cycProj N ξ).range = cyclicSpace (N : Set _) ξ :=
  Submodule.range_starProjection _

/-- The projection onto `[N ξ]` lies in the commutant `N′`. -/
theorem cycProj_mem_commutant (N : VonNeumannAlgebra H) (ξ : H) : cycProj N ξ ∈ N.commutant := by
  rw [VonNeumannAlgebra.IsStarProjection.mem_iff (cycProj_isStarProjection N ξ), N.commutant_commutant]
  intro y hy
  rw [Module.End.mem_invtSubmodule_iff_mapsTo, cycProj_range]
  intro v hv
  exact apply_mem_cyclicSpace_of_mem N ξ hy hv

/-- The projection onto `[N′ ξ]` lies in `N`. -/
theorem cycProj_commutant_mem (N : VonNeumannAlgebra H) (ξ : H) : cycProj N.commutant ξ ∈ N := by
  have := cycProj_mem_commutant N.commutant ξ
  rwa [N.commutant_commutant] at this

theorem cycProj_apply_self (N : VonNeumannAlgebra H) (ξ : H) : cycProj N ξ ξ = ξ :=
  Submodule.starProjection_eq_self_iff.mpr (mem_cyclicSpace_self N ξ)

/-! ## Cyclic and separating vectors -/

/-- `ξ` is cyclic for `S`: `span (S ξ)` is dense. -/
def IsCyclic (S : Set (H →L[ℂ] H)) (ξ : H) : Prop := Dense (orbit S ξ : Set H)

/-- `ξ` is separating for `S`: `x ξ = 0 ⇒ x = 0` for `x ∈ S`. -/
def IsSeparating (S : Set (H →L[ℂ] H)) (ξ : H) : Prop := ∀ x ∈ S, x ξ = 0 → x = 0

theorem IsCyclic.cyclicSpace_eq_top {S : Set (H →L[ℂ] H)} {ξ : H} (h : IsCyclic S ξ) :
    cyclicSpace S ξ = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp h

theorem isCyclic_of_cyclicSpace_eq_top {S : Set (H →L[ℂ] H)} {ξ : H}
    (h : cyclicSpace S ξ = ⊤) : IsCyclic S ξ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr h

/-- A vector separating for `N` is cyclic for `N′` (`[N′ ξ]^⊥` is `N`-invariant, so its
projection is in `N` and kills `ξ`). -/
theorem IsSeparating.isCyclic_commutant {N : VonNeumannAlgebra H} {ξ : H}
    (h : IsSeparating (N : Set _) ξ) : IsCyclic (N.commutant : Set _) ξ := by
  refine isCyclic_of_cyclicSpace_eq_top ?_
  have hp : 1 - cycProj N.commutant ξ ∈ N := sub_mem (one_mem N) (cycProj_commutant_mem N ξ)
  have h0 : (1 - cycProj N.commutant ξ) ξ = 0 := by
    rw [_root_.sub_apply, one_apply_eq_self, cycProj_apply_self, sub_self]
  have h1 : cycProj N.commutant ξ = 1 := by
    have := h _ hp h0
    rwa [sub_eq_zero, eq_comm] at this
  rw [← cycProj_range, h1, Submodule.eq_top_iff']
  intro v
  exact LinearMap.mem_range.mpr ⟨v, rfl⟩

/-- A vector cyclic for `N′` is separating for `N`. -/
theorem IsCyclic.isSeparating_of_commutant {N : VonNeumannAlgebra H} {ξ : H}
    (h : IsCyclic (N.commutant : Set _) ξ) : IsSeparating (N : Set _) ξ := by
  intro x hx hxξ
  refine ContinuousLinearMap.ext_on (R₁ := ℂ) (s := (fun y : H →L[ℂ] H => y ξ) '' N.commutant)
    ?_ ?_
  · exact h
  · rintro _ ⟨y, hy, rfl⟩
    change x (y ξ) = (0 : H →L[ℂ] H) (y ξ)
    rw [_root_.zero_apply, ← mul_apply_eq_comp, ← commutant_mul_of_mem hx hy,
      mul_apply_eq_comp, hxξ, map_zero]

theorem isSeparating_iff_isCyclic_commutant (N : VonNeumannAlgebra H) (ξ : H) :
    IsSeparating (N : Set _) ξ ↔ IsCyclic (N.commutant : Set _) ξ :=
  ⟨IsSeparating.isCyclic_commutant, IsCyclic.isSeparating_of_commutant⟩

theorem IsSeparating.mono {S T : Set (H →L[ℂ] H)} {ξ : H} (h : IsSeparating T ξ) (hST : S ⊆ T) :
    IsSeparating S ξ :=
  fun x hx => h x (hST hx)

/-- A vector state faithful on `N` gives a separating vector. -/
theorem isSeparating_of_faithful {S : Set (H →L[ℂ] H)} {ξ : H}
    (h : ∀ x ∈ S, ⟪ξ, (star x * x) ξ⟫_ℂ = 0 → x = 0) : IsSeparating S ξ := by
  intro x hx hxξ
  refine h x hx ?_
  rw [mul_apply_eq_comp, hxξ, map_zero, inner_zero_right]

/-! ## From convergence at a separating vector to strong convergence -/

/-- Bounded pointwise convergence on a dense set gives pointwise convergence everywhere. -/
theorem tendsto_of_dense {ι : Type*} {l : Filter ι} {T : ι → H →L[ℂ] H} {L : H →L[ℂ] H}
    {C : ℝ} (hC : ∀ i, ‖T i‖ ≤ C) {s : Set H} (hs : Dense s)
    (h : ∀ v ∈ s, Tendsto (fun i => T i v) l (𝓝 (L v))) (ξ : H) :
    Tendsto (fun i => T i ξ) l (𝓝 (L ξ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set D : ℝ := max C 0 + ‖L‖ + 1 with hD
  have hD0 : 0 < D := by positivity
  obtain ⟨v, hv, hvξ⟩ := hs.exists_dist_lt ξ (ε := ε / (2 * D)) (by positivity)
  have hv' := (Metric.tendsto_nhds.mp (h v hv)) (ε / 2) (by positivity)
  filter_upwards [hv'] with i hi
  rw [dist_eq_norm] at hi hvξ ⊢
  have hCi : ‖T i (ξ - v)‖ ≤ max C 0 * ‖ξ - v‖ :=
    (T i).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_right ((hC i).trans (le_max_left _ _)) (norm_nonneg _))
  have hLv : ‖L (v - ξ)‖ ≤ ‖L‖ * ‖ξ - v‖ := by
    rw [norm_sub_rev ξ v]
    exact L.le_opNorm _
  have hsum : (max C 0 + ‖L‖) * ‖ξ - v‖ < ε / 2 := by
    calc (max C 0 + ‖L‖) * ‖ξ - v‖ ≤ D * ‖ξ - v‖ := by
          gcongr
          rw [hD]
          linarith
      _ < D * (ε / (2 * D)) := by gcongr
      _ = ε / 2 := by field_simp
  calc ‖T i ξ - L ξ‖ = ‖T i (ξ - v) + (T i v - L v) + L (v - ξ)‖ := by
        congr 1
        rw [map_sub, map_sub]
        abel
    _ ≤ ‖T i (ξ - v)‖ + ‖T i v - L v‖ + ‖L (v - ξ)‖ := norm_add₃_le
    _ ≤ max C 0 * ‖ξ - v‖ + ε / 2 + ‖L‖ * ‖ξ - v‖ := by gcongr
    _ = (max C 0 + ‖L‖) * ‖ξ - v‖ + ε / 2 := by ring
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- Convergence at a separating vector, with a uniform norm bound, upgrades to bounded strong
convergence (the commutant orbit `N′ ξ` is dense and `T i (y ξ) = y (T i ξ)`). -/
theorem tendstoStrongBdd_of_tendsto_separating (N : VonNeumannAlgebra H) {ξ : H}
    (hξ : IsSeparating (N : Set (H →L[ℂ] H)) ξ) {ι : Type*} {l : Filter ι}
    {T : ι → H →L[ℂ] H} {L : H →L[ℂ] H} (hT : ∀ i, T i ∈ N) (hL : L ∈ N) {C : ℝ}
    (hC : ∀ i, ‖T i‖ ≤ C) (h : Tendsto (fun i => T i ξ) l (𝓝 (L ξ))) :
    TendstoStrongBdd l T L := by
  refine ⟨⟨C, hC⟩, ?_⟩
  have hdense : Dense (orbit (N.commutant : Set (H →L[ℂ] H)) ξ : Set H) :=
    hξ.isCyclic_commutant
  refine tendsto_of_dense hC hdense fun v hv => ?_
  refine Submodule.span_induction (p := fun w _ => Tendsto (fun i => T i w) l (𝓝 (L w)))
    ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨y, hy, rfl⟩
    have e1 : ∀ i, T i (y ξ) = y (T i ξ) := fun i => by
      rw [← mul_apply_eq_comp, ← commutant_mul_of_mem (hT i) hy, mul_apply_eq_comp]
    have e2 : L (y ξ) = y (L ξ) := by
      rw [← mul_apply_eq_comp, ← commutant_mul_of_mem hL hy, mul_apply_eq_comp]
    simp only [e1, e2]
    exact (y.continuous.tendsto _).comp h
  · simp only [map_zero]
    exact tendsto_const_nhds
  · intro u w _ _ hu hw
    simp only [map_add]
    exact hu.add hw
  · intro c u _ hu
    simp only [map_smul]
    exact hu.const_smul c

end VN

end CommutingRepetition
