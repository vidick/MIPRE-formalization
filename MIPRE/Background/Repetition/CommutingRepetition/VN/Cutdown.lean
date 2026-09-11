/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Cutdown.lean
-/
/-
# Compression of a von Neumann algebra to an invariant subspace (density stage E3.5)

For a closed subspace `K ⊆ H` invariant under a von Neumann algebra `N`, the
compressions `x ↦ P x ι : K → K` (`x ∈ N`) form a `*`-algebra `N_K` on `K`.
If `K` contains a vector `ξ` separating for `N`, then `N_K` is a von Neumann
algebra on `K`: an operator `S` on `K` commuting with the compressed commutant
`P N′ ι` is the compression of the element `x̃ ∈ N` defined on the dense
subspace `N′ ξ` by `x̃ (y ξ) = y (S ξ)`, bounded by `‖S‖` through the square
root of `P y*y ι` (the `n = 1` case of the matrix trick of Kadison–Ringrose
5.5.6, which suffices because `N′ ξ` is already a linear subspace).
With `K = [N ξ]` this is the standard form of `N`, the input of
Tomita–Takesaki theory (stage E4).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Cyclic

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

open scoped InnerProductSpace ComplexOrder
open Filter Topology

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem smul_mem_vn (N : VonNeumannAlgebra H) (c : ℂ) {y : H →L[ℂ] H} (hy : y ∈ N) : c • y ∈ N := by
  rw [Algebra.smul_def]
  exact mul_mem (VonNeumannAlgebra.mem_carrier.mp (N.toStarSubalgebra.algebraMap_mem c)) hy

/-! ## The `n = 1` matrix trick on an abstract Hilbert space

(Stated on an abstract type: the continuous functional calculus instance is not found on the
operator algebra of a subtype `↥K`, so the square root is taken here and the result is
instantiated at `E := ↥K` below.) -/

section Trick

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- For `0 ≤ b` commuting with `S`: `re ⟪S v, b (S v)⟫ ≤ ‖S‖² re ⟪v, b v⟫` (via `b = r²`). -/
theorem re_inner_apply_le_of_commute (b S : E →L[ℂ] E) (hb : 0 ≤ b) (hS : Commute b S) (v : E) :
    RCLike.re ⟪S v, b (S v)⟫_ℂ ≤ ‖S‖ ^ 2 * RCLike.re ⟪v, b v⟫_ℂ := by
  obtain ⟨r, hr⟩ : ∃ r : E →L[ℂ] E, r = cfc Real.sqrt b := ⟨_, rfl⟩
  have hrr : r * r = b := by
    rw [hr, ← cfc_mul Real.sqrt Real.sqrt b]
    have : cfc (fun x => Real.sqrt x * Real.sqrt x) b = cfc (id : ℝ → ℝ) b :=
      cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hb hx)
    rw [this]
    exact cfc_id ℝ b
  have hrsa : IsSelfAdjoint r := by
    rw [hr]
    exact cfc_predicate _ _
  have hrS : Commute r S := by
    rw [hr]
    exact hS.cfc_real _
  have key : ∀ w, ⟪w, b w⟫_ℂ = ⟪r w, r w⟫_ℂ := fun w => by
    rw [← hrr, mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint, hrsa.star_eq]
  rw [key, key, inner_self_eq_norm_sq, inner_self_eq_norm_sq, ← mul_apply_eq_comp, hrS.eq,
    mul_apply_eq_comp, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (S.le_opNorm _) 2

end Trick

/-! ## Compression of a single operator -/

variable (K : Submodule ℂ H) [CompleteSpace K]

/-- The compression `P T ι : K → K` of an operator on `H`. -/
noncomputable def compressTo (T : H →L[ℂ] H) : K →L[ℂ] K :=
  K.orthogonalProjectionOnto ∘L (T ∘L K.subtypeL)

theorem compressTo_apply (T : H →L[ℂ] H) (v : K) :
    compressTo K T v = K.orthogonalProjectionOnto (T v) := rfl

theorem coe_compressTo_apply (T : H →L[ℂ] H) (v : K) :
    (compressTo K T v : H) = K.starProjection (T v) := rfl

theorem coe_compressTo_apply_of_invariant {T : H →L[ℂ] H} (hT : ∀ v ∈ K, T v ∈ K) (v : K) :
    (compressTo K T v : H) = T v := by
  rw [coe_compressTo_apply, Submodule.starProjection_eq_self_iff]
  exact hT v v.2

theorem inner_compressTo_left (T : H →L[ℂ] H) (v w : K) :
    ⟪compressTo K T v, w⟫_ℂ = ⟪T v, (w : H)⟫_ℂ := by
  rw [compressTo_apply, ← Submodule.adjoint_subtypeL, ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem inner_compressTo_right (T : H →L[ℂ] H) (v w : K) :
    ⟪v, compressTo K T w⟫_ℂ = ⟪(v : H), T w⟫_ℂ := by
  rw [compressTo_apply, ← Submodule.adjoint_subtypeL, ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem compressTo_add (S T : H →L[ℂ] H) :
    compressTo K (S + T) = compressTo K S + compressTo K T := by
  ext v
  simp only [compressTo_apply, _root_.add_apply, map_add]

theorem compressTo_smul (c : ℂ) (T : H →L[ℂ] H) : compressTo K (c • T) = c • compressTo K T := by
  ext v
  simp only [compressTo_apply, _root_.smul_apply, map_smul]

theorem compressTo_zero : compressTo K (0 : H →L[ℂ] H) = 0 := by
  ext v
  simp [compressTo_apply]

theorem compressTo_one : compressTo K (1 : H →L[ℂ] H) = 1 := by
  ext v
  rw [compressTo_apply, one_apply_eq_self, one_apply_eq_self,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem compressTo_star (T : H →L[ℂ] H) : compressTo K (star T) = star (compressTo K T) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint]
  unfold compressTo
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
    ContinuousLinearMap.comp_assoc]

theorem compressTo_mul_of_invariant (S : H →L[ℂ] H) {T : H →L[ℂ] H} (hT : ∀ v ∈ K, T v ∈ K) :
    compressTo K (S * T) = compressTo K S * compressTo K T := by
  ext v
  rw [mul_apply_eq_comp, compressTo_apply, compressTo_apply]
  rw [mul_apply_eq_comp, coe_compressTo_apply_of_invariant K hT v]

/-- `P S ι P T ι = P (S p T) ι`. -/
theorem compressTo_mul_eq (S T : H →L[ℂ] H) :
    compressTo K S * compressTo K T = compressTo K (S * K.starProjection * T) := by
  ext v
  simp only [mul_apply_eq_comp, coe_compressTo_apply]

theorem compressTo_starProjection_mul (T : H →L[ℂ] H) :
    compressTo K (K.starProjection * T) = compressTo K T := by
  ext v
  rw [coe_compressTo_apply, coe_compressTo_apply, mul_apply_eq_comp,
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]

theorem norm_compressTo_apply_le (T : H →L[ℂ] H) (v : K) : ‖compressTo K T v‖ ≤ ‖T‖ * ‖v‖ := by
  rw [compressTo_apply]
  refine (Submodule.norm_orthogonalProjectionOnto_apply_le _ _).trans ?_
  exact T.le_opNorm _

theorem norm_compressTo_le (T : H →L[ℂ] H) : ‖compressTo K T‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_compressTo_apply_le K T)

/-- Compression preserves bounded strong convergence. -/
theorem isNormalMap_compressTo : IsNormalMap (compressTo K) := by
  intro ι l T L ⟨⟨C, hC⟩, ht⟩
  refine ⟨⟨C, fun i => (norm_compressTo_le K _).trans (hC i)⟩, fun v => ?_⟩
  simp only [compressTo_apply]
  exact (K.orthogonalProjectionOnto.continuous.tendsto _).comp (ht v)

/-- `P y*y ι` is a positive operator on `K`. -/
theorem compressTo_star_mul_self_nonneg (y : H →L[ℂ] H) : 0 ≤ compressTo K (star y * y) := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff']
  refine ⟨?_, fun v => ?_⟩
  · rw [IsSelfAdjoint, ← compressTo_star, star_mul, star_star]
  · rw [inner_compressTo_left, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
    exact pow_nonneg (Complex.zero_le_real.mpr (norm_nonneg (y (v : H)))) 2

/-- If `S` commutes with `P y*y ι` then `‖y (S v)‖ ≤ ‖S‖ ‖y v‖`. -/
theorem norm_apply_apply_le (S : K →L[ℂ] K) (y : H →L[ℂ] H)
    (hS : Commute (compressTo K (star y * y)) S) (v : K) :
    ‖y (S v : H)‖ ≤ ‖S‖ * ‖y (v : H)‖ := by
  have hb0 : 0 ≤ compressTo K (star y * y) := compressTo_star_mul_self_nonneg K y
  have h := re_inner_apply_le_of_commute _ S hb0 hS v
  have key : ∀ w : K, RCLike.re ⟪w, compressTo K (star y * y) w⟫_ℂ = ‖y (w : H)‖ ^ 2 := fun w => by
    rw [inner_compressTo_right, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq]
  rw [key, key, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-! ## The compressed algebra and the commutant -/

variable (N : VonNeumannAlgebra H) (hK : ∀ x ∈ N, ∀ v ∈ K, x v ∈ K)

include hK in
/-- The projection onto an `N`-invariant subspace lies in `N′`. -/
theorem starProjection_mem_commutant : K.starProjection ∈ N.commutant := by
  rw [VonNeumannAlgebra.IsStarProjection.mem_iff isStarProjection_starProjection,
    N.commutant_commutant]
  intro y hy
  rw [Module.End.mem_invtSubmodule_iff_mapsTo, Submodule.range_starProjection]
  intro v hv
  exact hK y hy v hv

include hK in
theorem compressTo_mul (x : H →L[ℂ] H) {y : H →L[ℂ] H} (hy : y ∈ N) :
    compressTo K (x * y) = compressTo K x * compressTo K y :=
  compressTo_mul_of_invariant K x (hK y hy)

include hK in
/-- Compressions of `N` and of `N′` commute. -/
theorem compressTo_commute_commutant {x y : H →L[ℂ] H} (hx : x ∈ N) (hy : y ∈ N.commutant) :
    compressTo K x * compressTo K y = compressTo K y * compressTo K x := by
  rw [compressTo_mul_eq, ← compressTo_mul_of_invariant K y (hK x hx),
    ← commutant_mul_of_mem hx (starProjection_mem_commutant K N hK), mul_assoc,
    compressTo_starProjection_mul, commutant_mul_of_mem hx hy]

/-! ## Extension of an operator commuting with the compressed commutant -/

section Extension

variable (ξ : H)

/-- The orbit `N′ ξ` (a linear subspace, as `N′` is an algebra). -/
def commOrbit : Submodule ℂ H := orbit (N.commutant : Set (H →L[ℂ] H)) ξ

theorem exists_rep {v : H} (hv : v ∈ commOrbit N ξ) : ∃ y ∈ N.commutant, y ξ = v := by
  refine Submodule.span_induction (p := fun v _ => ∃ y ∈ N.commutant, y ξ = v) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · exact ⟨0, zero_mem _, by simp⟩
  · rintro _ _ _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y + y', add_mem hy hy', by simp⟩
  · rintro c _ _ ⟨y, hy, rfl⟩
    exact ⟨c • y, smul_mem_vn _ c hy, by simp⟩

theorem apply_mem_commOrbit {y : H →L[ℂ] H} (hy : y ∈ N.commutant) : y ξ ∈ commOrbit N ξ :=
  apply_mem_orbit hy

theorem dense_commOrbit {ξ : H} (hξ : IsSeparating (N : Set (H →L[ℂ] H)) ξ) :
    Dense (commOrbit N ξ : Set H) :=
  hξ.isCyclic_commutant

/-- A representative `y ∈ N′` with `y ξ = v` for `v ∈ N′ ξ`. -/
noncomputable def rep (v : commOrbit N ξ) : H →L[ℂ] H := (exists_rep N ξ v.2).choose

theorem rep_mem (v : commOrbit N ξ) : rep N ξ v ∈ N.commutant := (exists_rep N ξ v.2).choose_spec.1

theorem rep_apply (v : commOrbit N ξ) : rep N ξ v ξ = v := (exists_rep N ξ v.2).choose_spec.2

variable {N} (hξK : ξ ∈ K) (S : K →L[ℂ] K)
  (hS : ∀ y ∈ N.commutant, compressTo K y * S = S * compressTo K y)

include hS in
theorem norm_apply_le_of_mem {y : H →L[ℂ] H} (hy : y ∈ N.commutant) (v : K) :
    ‖y (S v : H)‖ ≤ ‖S‖ * ‖y (v : H)‖ :=
  norm_apply_apply_le K S y (hS _ (mul_mem (star_mem hy) hy)) v

include hS in
/-- Two elements of `N′` agreeing at `ξ` agree at `S ξ`. -/
theorem apply_eq_of_apply_eq {y y' : H →L[ℂ] H} (hy : y ∈ N.commutant) (hy' : y' ∈ N.commutant)
    (h : y ξ = y' ξ) : y (S ⟨ξ, hξK⟩ : H) = y' (S ⟨ξ, hξK⟩ : H) := by
  have hd : y - y' ∈ N.commutant := sub_mem hy hy'
  have h0 : (y - y') ξ = 0 := by rw [_root_.sub_apply, h, sub_self]
  have := norm_apply_le_of_mem K S hS hd ⟨ξ, hξK⟩
  simp only at this
  rw [h0, norm_zero, mul_zero] at this
  have h1 : (y - y') (S ⟨ξ, hξK⟩ : H) = 0 := norm_le_zero_iff.mp this
  rwa [_root_.sub_apply, sub_eq_zero] at h1

/-- `x̃` on `N′ ξ`: `y ξ ↦ y (S ξ)`. -/
noncomputable def extPre : commOrbit N ξ →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun v => rep N ξ v (S ⟨ξ, hξK⟩ : H)
      map_add' := fun v w => by
        have := apply_eq_of_apply_eq K ξ hξK S hS (rep_mem N ξ (v + w))
          (add_mem (rep_mem N ξ v) (rep_mem N ξ w))
          (by rw [rep_apply, _root_.add_apply, rep_apply, rep_apply]; rfl)
        rw [this, _root_.add_apply]
      map_smul' := fun c v => by
        have := apply_eq_of_apply_eq K ξ hξK S hS (rep_mem N ξ (c • v))
          (smul_mem_vn _ c (rep_mem N ξ v))
          (by rw [rep_apply, _root_.smul_apply, rep_apply]; rfl)
        rw [this, _root_.smul_apply]
        rfl } ‖S‖ fun v => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    have := norm_apply_le_of_mem K S hS (rep_mem N ξ v) ⟨ξ, hξK⟩
    simp only [rep_apply] at this
    exact this

theorem extPre_apply (v : commOrbit N ξ) : extPre K ξ hξK S hS v = rep N ξ v (S ⟨ξ, hξK⟩ : H) := rfl

variable (hξ : IsSeparating (N : Set (H →L[ℂ] H)) ξ)

include hξ in
theorem denseRange_subtypeL_commOrbit : DenseRange (commOrbit N ξ).subtypeL := by
  have h : Set.range (commOrbit N ξ).subtypeL = (commOrbit N ξ : Set H) := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact w.2
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩
  rw [DenseRange, h]
  exact dense_commOrbit N hξ

theorem isUniformInducing_subtypeL_commOrbit : IsUniformInducing (commOrbit N ξ).subtypeL :=
  ((AddMonoidHomClass.isometry_iff_norm _).mpr fun _ => rfl).isUniformInducing

/-- The extension `x̃ ∈ B(H)` of `y ξ ↦ y (S ξ)`. -/
noncomputable def extOp : H →L[ℂ] H := (extPre K ξ hξK S hS).extend (commOrbit N ξ).subtypeL

include hξ in
theorem extOp_apply {y : H →L[ℂ] H} (hy : y ∈ N.commutant) :
    extOp K ξ hξK S hS (y ξ) = y (S ⟨ξ, hξK⟩ : H) := by
  have hv : y ξ ∈ commOrbit N ξ := apply_mem_commOrbit N ξ hy
  have h := ContinuousLinearMap.extend_eq (extPre K ξ hξK S hS)
    (denseRange_subtypeL_commOrbit ξ hξ) (isUniformInducing_subtypeL_commOrbit ξ) ⟨y ξ, hv⟩
  rw [show (commOrbit N ξ).subtypeL ⟨y ξ, hv⟩ = y ξ from rfl] at h
  rw [extOp, h, extPre_apply]
  exact apply_eq_of_apply_eq K ξ hξK S hS (rep_mem N ξ _) hy (rep_apply N ξ _)

include hξ in
theorem extOp_mem : extOp K ξ hξK S hS ∈ N := by
  refine mem_of_commute_commutant N fun z hz => ?_
  refine ContinuousLinearMap.ext_on (R₁ := ℂ)
    (s := (fun y : H →L[ℂ] H => y ξ) '' (N.commutant : Set (H →L[ℂ] H))) (dense_commOrbit N hξ) ?_
  rintro _ ⟨y, hy, rfl⟩
  change (z * extOp K ξ hξK S hS) (y ξ) = (extOp K ξ hξK S hS * z) (y ξ)
  rw [mul_apply_eq_comp, mul_apply_eq_comp, extOp_apply K ξ hξK S hS hξ hy]
  have e : z (y ξ) = (z * y) ξ := rfl
  rw [e, extOp_apply K ξ hξK S hS hξ (mul_mem hz hy), mul_apply_eq_comp]

include hK hξ in
theorem compressTo_extOp : compressTo K (extOp K ξ hξK S hS) = S := by
  -- both sides agree on the dense set `{P (y ξ) : y ∈ N′} ⊆ K`
  have hdense : Dense ((fun y : H →L[ℂ] H => compressTo K y ⟨ξ, hξK⟩) ''
      (N.commutant : Set (H →L[ℂ] H))) := by
    rw [Metric.dense_iff]
    intro v ε hε
    obtain ⟨w, hw, hwv⟩ := Metric.mem_closure_iff.mp
      ((dense_commOrbit N hξ).closure_eq ▸ Set.mem_univ (v : H)) ε hε
    obtain ⟨y, hy, rfl⟩ := exists_rep N ξ hw
    refine ⟨compressTo K y ⟨ξ, hξK⟩, ?_, ⟨y, hy, rfl⟩⟩
    rw [Metric.mem_ball, Subtype.dist_eq, coe_compressTo_apply, dist_eq_norm,
      ← Submodule.starProjection_eq_self_iff.mpr v.2, ← map_sub, Submodule.coe_mk]
    refine (Submodule.norm_starProjection_apply_le _ _).trans_lt ?_
    rwa [dist_eq_norm, norm_sub_rev] at hwv
  refine ContinuousLinearMap.ext_on (R₁ := ℂ) (Dense.mono Submodule.subset_span hdense) ?_
  rintro _ ⟨y, hy, rfl⟩
  have hξ' : compressTo K (extOp K ξ hξK S hS) ⟨ξ, hξK⟩ = S ⟨ξ, hξK⟩ := by
    apply Subtype.ext
    rw [coe_compressTo_apply, Submodule.coe_mk]
    have : extOp K ξ hξK S hS ξ = (S ⟨ξ, hξK⟩ : H) := by
      have h := extOp_apply K ξ hξK S hS hξ (one_mem N.commutant)
      rwa [one_apply_eq_self, one_apply_eq_self] at h
    rw [this, Submodule.starProjection_eq_self_iff]
    exact Subtype.coe_prop _
  rw [← mul_apply_eq_comp, compressTo_commute_commutant K N hK (extOp_mem K ξ hξK S hS hξ) hy,
    mul_apply_eq_comp, hξ', ← mul_apply_eq_comp, hS y hy, mul_apply_eq_comp]

include hK hξK hS hξ in
/-- An operator on `K` commuting with the compressed commutant is a compression of `N`. -/
theorem exists_compressTo_eq : ∃ x ∈ N, compressTo K x = S :=
  ⟨extOp K ξ hξK S hS, extOp_mem K ξ hξK S hS hξ, compressTo_extOp K hK ξ hξK S hS hξ⟩

end Extension

/-! ## The compressed von Neumann algebra -/

variable (ξ : H) (hξK : ξ ∈ K) (hξ : IsSeparating (N : Set (H →L[ℂ] H)) ξ)

/-- The compressed algebra `{P x ι | x ∈ N}` on an invariant subspace containing a separating
vector is a von Neumann algebra on `K`. -/
noncomputable def cutdown : VonNeumannAlgebra K where
  toStarSubalgebra :=
    { carrier := {S | ∃ x ∈ N, compressTo K x = S}
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, mul_mem hx hy, compressTo_mul K N hK x hy⟩
      one_mem' := ⟨1, one_mem N, compressTo_one K⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, add_mem hx hy, compressTo_add K x y⟩
      zero_mem' := ⟨0, zero_mem N, compressTo_zero K⟩
      algebraMap_mem' := fun c => ⟨algebraMap ℂ _ c,
        VonNeumannAlgebra.mem_carrier.mp (N.toStarSubalgebra.algebraMap_mem c), by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, compressTo_smul,
          compressTo_one]⟩
      star_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨star x, star_mem hx, compressTo_star K x⟩ }
  centralizer_centralizer' := by
    refine Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
    intro S hS
    refine exists_compressTo_eq K hK ξ hξK S ?_ hξ
    intro y hy
    refine hS _ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact compressTo_commute_commutant K N hK hx hy

theorem mem_cutdown_iff {S : K →L[ℂ] K} :
    S ∈ cutdown K N hK ξ hξK hξ ↔ ∃ x ∈ N, compressTo K x = S := Iff.rfl

theorem compressTo_mem_cutdown {x : H →L[ℂ] H} (hx : x ∈ N) :
    compressTo K x ∈ cutdown K N hK ξ hξK hξ := ⟨x, hx, rfl⟩

include hK ξ hξK hξ in
/-- Compression is injective on `N` (the separating vector lies in `K`). -/
theorem compressTo_injective {x y : H →L[ℂ] H} (hx : x ∈ N) (hy : y ∈ N)
    (h : compressTo K x = compressTo K y) : x = y := by
  have hxy : x - y ∈ N := sub_mem hx hy
  have : (x - y) ξ = 0 := by
    have h' := congrArg (fun S : K →L[ℂ] K => (S ⟨ξ, hξK⟩ : H)) h
    simp only [coe_compressTo_apply_of_invariant K (hK x hx),
      coe_compressTo_apply_of_invariant K (hK y hy)] at h'
    rw [_root_.sub_apply, h', sub_self]
  exact sub_eq_zero.mp (hξ _ hxy this)

/-- The separating vector is separating for the compressed algebra. -/
theorem isSeparating_cutdown :
    IsSeparating (cutdown K N hK ξ hξK hξ : Set (K →L[ℂ] K)) ⟨ξ, hξK⟩ := by
  rintro _ ⟨x, hx, rfl⟩ h0
  have : x ξ = 0 := by
    have h' := congrArg Subtype.val h0
    rwa [coe_compressTo_apply_of_invariant K (hK x hx)] at h'
  rw [hξ x hx this, compressTo_zero]

/-- The cyclic subspace `[N ξ]` is `N`-invariant. -/
theorem cyclicSpace_invariant :
    ∀ x ∈ N, ∀ v ∈ cyclicSpace (N : Set (H →L[ℂ] H)) ξ, x v ∈ cyclicSpace (N : Set (H →L[ℂ] H)) ξ :=
  fun _ hx _ hv => apply_mem_cyclicSpace_of_mem N ξ hx hv

/-- On the cyclic subspace `K = [N ξ]`, the vector `ξ` is cyclic for the compressed algebra. -/
theorem isCyclic_cutdown_cyclicSpace :
    IsCyclic (cutdown (cyclicSpace (N : Set (H →L[ℂ] H)) ξ) N (cyclicSpace_invariant N ξ) ξ
      (mem_cyclicSpace_self N ξ) hξ :
      Set (cyclicSpace (N : Set (H →L[ℂ] H)) ξ →L[ℂ] cyclicSpace (N : Set (H →L[ℂ] H)) ξ))
      ⟨ξ, mem_cyclicSpace_self N ξ⟩ := by
  rw [IsCyclic, Metric.dense_iff]
  intro v ε hε
  have hv : (v : H) ∈ closure (orbit (N : Set (H →L[ℂ] H)) ξ : Set H) := by
    rw [← Submodule.topologicalClosure_coe]
    exact v.2
  obtain ⟨w, hw, hwv⟩ := Metric.mem_closure_iff.mp hv ε hε
  have hwK : w ∈ cyclicSpace (N : Set (H →L[ℂ] H)) ξ := orbit_le_cyclicSpace _ ξ hw
  refine ⟨⟨w, hwK⟩, ?_, ?_⟩
  · rw [Metric.mem_ball, Subtype.dist_eq, dist_comm]
    exact hwv
  · refine Submodule.span_induction (p := fun w _ => ∀ hwK : w ∈ cyclicSpace (N : Set (H →L[ℂ] H)) ξ,
      (⟨w, hwK⟩ : cyclicSpace (N : Set (H →L[ℂ] H)) ξ) ∈
        orbit (cutdown (cyclicSpace (N : Set (H →L[ℂ] H)) ξ) N (cyclicSpace_invariant N ξ) ξ
          (mem_cyclicSpace_self N ξ) hξ :
          Set (cyclicSpace (N : Set (H →L[ℂ] H)) ξ →L[ℂ] cyclicSpace (N : Set (H →L[ℂ] H)) ξ))
          ⟨ξ, mem_cyclicSpace_self N ξ⟩)
      ?_ ?_ ?_ ?_ hw hwK
    · rintro _ ⟨x, hx, rfl⟩ hwK
      refine Submodule.subset_span ⟨compressTo _ x, compressTo_mem_cutdown _ N _ _ _ hξ hx, ?_⟩
      apply Subtype.ext
      exact coe_compressTo_apply_of_invariant _ (cyclicSpace_invariant N ξ x hx) _
    · intro _
      exact Submodule.zero_mem _
    · intro a b ha' hb' ha hb _
      exact Submodule.add_mem _ (ha (orbit_le_cyclicSpace _ ξ ha'))
        (hb (orbit_le_cyclicSpace _ ξ hb'))
    · intro c a ha' ha _
      exact Submodule.smul_mem _ c (ha (orbit_le_cyclicSpace _ ξ ha'))

end VN

end CommutingRepetition
