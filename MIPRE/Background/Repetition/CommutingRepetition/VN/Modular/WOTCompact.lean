/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/WOTCompact.lean
-/
/-
# Weak-operator compactness of the self-adjoint unit ball (density stage E4.0)

The one topological ingredient of Rieffel–van Daele's proof of Tomita's theorem
(their Lemma 4.3, "Sakai's linear Radon–Nikodym theorem") is that the unit ball
of the self-adjoint part of a von Neumann algebra `N` is compact for the weak
operator topology. We prove the form in which it is used: every sequence
`x n ∈ N` with `x n = (x n)*`, `‖x n‖ ≤ 1` has a cluster point `L` in the same
set, in the sense that each matrix coefficient `⟪L ζ, ξ⟫` is a cluster point of
the sequence `⟪x n ζ, ξ⟫`.

Proof: the coefficient functions `(ζ, ξ) ↦ ⟪T ζ, ξ⟫` lie in the product
`∏ closedBall 0 (‖ζ‖‖ξ‖)`, compact by Tychonoff; a cluster point `F` of the
coefficient functions is sesquilinear, bounded, symmetric and commutes with
`N′` (all closed conditions), hence is `⟪L ζ, ξ⟫` for a unique `L ∈ N`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Generated

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace WOT

open scoped InnerProductSpace ComplexConjugate
open Filter Topology

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A cluster point of a convergent sequence is its limit. -/
theorem eq_of_clusterPt_of_tendsto {Y : Type*} [TopologicalSpace Y] [T2Space Y] {ι : Type*}
    {l : Filter ι} [l.NeBot] {f : ι → Y} {y L : Y} (h : ClusterPt y (map f l))
    (hf : Tendsto f l (𝓝 L)) : y = L :=
  eq_of_nhds_neBot (h.neBot.mono (inf_le_inf_left _ hf))

/-- Cluster points are transported by continuous maps. -/
theorem clusterPt_map_seq {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] {ι : Type*}
    {l : Filter ι} {f : ι → Y} {y : Y} (h : ClusterPt y (map f l)) {Φ : Y → Z}
    (hΦ : Continuous Φ) : ClusterPt (Φ y) (map (fun i => Φ (f i)) l) :=
  ClusterPt.map h hΦ.continuousAt (tendsto_map'_iff.mpr tendsto_map)

/-- The matrix coefficients of an operator. -/
noncomputable def coeff (T : H →L[ℂ] H) : H × H → ℂ := fun p => ⟪T p.1, p.2⟫_ℂ

theorem coeff_apply (T : H →L[ℂ] H) (ζ ξ : H) : coeff T (ζ, ξ) = ⟪T ζ, ξ⟫_ℂ := rfl

/-- The compact box containing the coefficient functions of the unit ball. -/
def box : Set (H × H → ℂ) := Set.pi Set.univ fun p => Metric.closedBall 0 (‖p.1‖ * ‖p.2‖)

theorem isCompact_box : IsCompact (box (H := H)) :=
  isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem coeff_mem_box {T : H →L[ℂ] H} (hT : ‖T‖ ≤ 1) : coeff T ∈ box := by
  intro p _
  rw [Metric.mem_closedBall, dist_zero_right, coeff]
  calc ‖⟪T p.1, p.2⟫_ℂ‖ ≤ ‖T p.1‖ * ‖p.2‖ := norm_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖p.1‖) * ‖p.2‖ := by gcongr; exact T.le_opNorm _
    _ ≤ (1 * ‖p.1‖) * ‖p.2‖ := by gcongr
    _ = ‖p.1‖ * ‖p.2‖ := by ring

section Reconstruction

variable (N : VonNeumannAlgebra H) (x : ℕ → H →L[ℂ] H)
  (hx : ∀ n, x n ∈ N ∧ IsSelfAdjoint (x n) ∧ ‖x n‖ ≤ 1)
  {F : H × H → ℂ} (hF : ClusterPt F (map (fun n => coeff (x n)) atTop))

include hx hF

/-- A closed identity satisfied by all `coeff (x n)` is satisfied by `F`. -/
theorem F_eq_of_forall {Φ : (H × H → ℂ) → ℂ} (hΦ : Continuous Φ)
    (h : ∀ n, Φ (coeff (x n)) = 0) : Φ F = 0 :=
  eq_of_clusterPt_of_tendsto (clusterPt_map_seq hF hΦ) (by simp only [h]; exact tendsto_const_nhds)

theorem F_add_right (ζ ξ₁ ξ₂ : H) : F (ζ, ξ₁ + ξ₂) = F (ζ, ξ₁) + F (ζ, ξ₂) := by
  have := F_eq_of_forall N x hx hF
    (Φ := fun G => G (ζ, ξ₁ + ξ₂) - (G (ζ, ξ₁) + G (ζ, ξ₂))) (by fun_prop)
    (fun n => by simp only [coeff_apply, inner_add_right, sub_self])
  exact sub_eq_zero.mp this

theorem F_smul_right (ζ ξ : H) (c : ℂ) : F (ζ, c • ξ) = c * F (ζ, ξ) := by
  have := F_eq_of_forall N x hx hF
    (Φ := fun G => G (ζ, c • ξ) - c * G (ζ, ξ)) (by fun_prop)
    (fun n => by simp only [coeff_apply, inner_smul_right, sub_self])
  exact sub_eq_zero.mp this

theorem F_add_left (ζ₁ ζ₂ ξ : H) : F (ζ₁ + ζ₂, ξ) = F (ζ₁, ξ) + F (ζ₂, ξ) := by
  have := F_eq_of_forall N x hx hF
    (Φ := fun G => G (ζ₁ + ζ₂, ξ) - (G (ζ₁, ξ) + G (ζ₂, ξ))) (by fun_prop)
    (fun n => by simp only [coeff_apply, map_add, inner_add_left, sub_self])
  exact sub_eq_zero.mp this

theorem F_smul_left (ζ ξ : H) (c : ℂ) : F (c • ζ, ξ) = conj c * F (ζ, ξ) := by
  have := F_eq_of_forall N x hx hF
    (Φ := fun G => G (c • ζ, ξ) - conj c * G (ζ, ξ)) (by fun_prop)
    (fun n => by simp only [coeff_apply, map_smul, inner_smul_left, sub_self])
  exact sub_eq_zero.mp this

theorem F_symm (ζ ξ : H) : F (ζ, ξ) = conj (F (ξ, ζ)) := by
  have := F_eq_of_forall N x hx hF
    (Φ := fun G => G (ζ, ξ) - conj (G (ξ, ζ))) (by fun_prop)
    (fun n => by
      simp only [coeff_apply, inner_conj_symm]
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        (hx n).2.1.star_eq, sub_self])
  exact sub_eq_zero.mp this

theorem F_commutant {y : H →L[ℂ] H} (hy : y ∈ N.commutant) (ζ ξ : H) :
    F (ζ, star y ξ) = F (y ζ, ξ) := by
  have := F_eq_of_forall N x hx hF
    (Φ := fun G => G (ζ, star y ξ) - G (y ζ, ξ)) (by fun_prop)
    (fun n => by
      simp only [coeff_apply]
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
        ← mul_apply_eq_comp, ← mul_apply_eq_comp, commutant_mul_of_mem (hx n).1 hy, sub_self])
  exact sub_eq_zero.mp this

theorem F_bound (hbox : F ∈ box) (ζ ξ : H) : ‖F (ζ, ξ)‖ ≤ ‖ζ‖ * ‖ξ‖ := by
  have := hbox (ζ, ξ) (Set.mem_univ _)
  rwa [Metric.mem_closedBall, dist_zero_right] at this

/-- The sesquilinear form `F` as a bounded sesquilinear map. -/
noncomputable def sesq (hbox : F ∈ box) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    { toFun := fun ζ =>
        { toFun := fun ξ => F (ζ, ξ)
          map_add' := F_add_right N x hx hF ζ
          map_smul' := fun c ξ => by
            simp only [RingHom.id_apply, smul_eq_mul]
            exact F_smul_right N x hx hF ζ ξ c }
      map_add' := fun ζ₁ ζ₂ => by ext ξ; exact F_add_left N x hx hF ζ₁ ζ₂ ξ
      map_smul' := fun c ζ => by
        ext ξ
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul]
        exact F_smul_left N x hx hF ζ ξ c }
    1 fun ζ ξ => by simpa using F_bound N x hx hF hbox ζ ξ

theorem sesq_apply (hbox : F ∈ box) (ζ ξ : H) : sesq N x hx hF hbox ζ ξ = F (ζ, ξ) := rfl

/-- The operator `L` with `⟪L ζ, ξ⟫ = F (ζ, ξ)`. -/
noncomputable def limOp (hbox : F ∈ box) : H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin (sesq N x hx hF hbox)

theorem inner_limOp (hbox : F ∈ box) (ζ ξ : H) : ⟪limOp N x hx hF hbox ζ, ξ⟫_ℂ = F (ζ, ξ) :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ ζ ξ

theorem limOp_isSelfAdjoint (hbox : F ∈ box) : IsSelfAdjoint (limOp N x hx hF hbox) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro ζ ξ
  rw [inner_limOp, ← inner_conj_symm ζ (limOp N x hx hF hbox ξ), inner_limOp]
  exact F_symm N x hx hF ζ ξ

theorem limOp_mem (hbox : F ∈ box) : limOp N x hx hF hbox ∈ N := by
  refine mem_of_commute_commutant N fun y hy => ?_
  ext ζ
  refine ext_inner_right ℂ fun ξ => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint, inner_limOp N x hx hF hbox ζ (star y ξ),
    inner_limOp N x hx hF hbox (y ζ) ξ, F_commutant N x hx hF hy]

theorem norm_limOp_le (hbox : F ∈ box) : ‖limOp N x hx hF hbox‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ζ => ?_
  rw [one_mul]
  have h := F_bound N x hx hF hbox ζ (limOp N x hx hF hbox ζ)
  rw [← inner_limOp N x hx hF hbox ζ (limOp N x hx hF hbox ζ), inner_self_eq_norm_sq_to_K,
    norm_pow, RCLike.norm_ofReal, abs_norm, sq] at h
  by_cases h0 : ‖limOp N x hx hF hbox ζ‖ = 0
  · rw [h0]; exact norm_nonneg _
  · exact le_of_mul_le_mul_right (by simpa [mul_comm] using h)
      (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))

theorem clusterPt_inner_limOp (hbox : F ∈ box) (ζ ξ : H) :
    ClusterPt ⟪limOp N x hx hF hbox ζ, ξ⟫_ℂ (map (fun n => ⟪x n ζ, ξ⟫_ℂ) atTop) := by
  rw [inner_limOp]
  exact clusterPt_map_seq hF (Φ := fun G => G (ζ, ξ)) (continuous_apply _)

end Reconstruction

/-- **WOT compactness of the self-adjoint unit ball of a von Neumann algebra**, in cluster-point
form: a sequence in `{x ∈ N | x = x*, ‖x‖ ≤ 1}` has a cluster point `L` in that set, with every
matrix coefficient `⟪L ζ, ξ⟫` a cluster point of `n ↦ ⟪x n ζ, ξ⟫`. -/
theorem exists_clusterPt_saBall (N : VonNeumannAlgebra H) (x : ℕ → H →L[ℂ] H)
    (hx : ∀ n, x n ∈ N ∧ IsSelfAdjoint (x n) ∧ ‖x n‖ ≤ 1) :
    ∃ L : H →L[ℂ] H, L ∈ N ∧ IsSelfAdjoint L ∧ ‖L‖ ≤ 1 ∧
      ∀ ζ ξ : H, ClusterPt ⟪L ζ, ξ⟫_ℂ (map (fun n => ⟪x n ζ, ξ⟫_ℂ) atTop) := by
  have hle : map (fun n => coeff (x n)) atTop ≤ 𝓟 (box (H := H)) :=
    le_principal_iff.mpr (mem_map.mpr (Eventually.of_forall fun n => coeff_mem_box (hx n).2.2))
  obtain ⟨F, hbox, hF⟩ := isCompact_box.exists_clusterPt hle
  exact ⟨limOp N x hx hF hbox, limOp_mem N x hx hF hbox, limOp_isSelfAdjoint N x hx hF hbox,
    norm_limOp_le N x hx hF hbox, clusterPt_inner_limOp N x hx hF hbox⟩

/-- Consequence used in RvD Lemma 4.3: if a continuous real function of the coefficients converges
along the sequence, its limit is the value at `L`. -/
theorem tendsto_eq_of_clusterPt {L : H →L[ℂ] H} {x : ℕ → H →L[ℂ] H} {ζ ξ : H}
    (hL : ClusterPt ⟪L ζ, ξ⟫_ℂ (map (fun n => ⟪x n ζ, ξ⟫_ℂ) atTop)) {Φ : ℂ → ℝ}
    (hΦ : Continuous Φ) {r : ℝ} (h : Tendsto (fun n => Φ ⟪x n ζ, ξ⟫_ℂ) atTop (𝓝 r)) :
    Φ ⟪L ζ, ξ⟫_ℂ = r :=
  eq_of_clusterPt_of_tendsto (clusterPt_map_seq hL hΦ) h

end WOT

end VN

end CommutingRepetition
