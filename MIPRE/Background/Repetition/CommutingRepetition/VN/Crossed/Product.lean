/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Crossed/Product.lean
-/
/-
# The crossed product `M ⋊_σ ℚ` (density stage E5.2, part 2)

For `(M, Ω)` with `Ω` cyclic and separating and the modular group `σ_t`, the covariant
representation on `ℓ²(ℚ, K)`: `π(y) = ⊕_s σ_{-s}(y)`, `λ(g) = shift g`, with
`λ(g) π(y) λ(g)* = π(σ_g y)`. The crossed product is the von Neumann algebra
`ℛ := W*(π(M) ∪ λ(ℚ))`; the vector `Ω̂ = δ₀ ⊗ Ω` is cyclic and separating for `ℛ`
(the commutant contains `1 ⊗ y′`, `y′ ∈ M′`, and `W_g = λ(g)(1 ⊗ Δ^{-ig})`), and its
vector state is the dual state: `⟪Ω̂, λ(g) π(y) Ω̂⟫ = δ_{g,0} ⟪Ω, yΩ⟫`. The compression
`E(X) = ev₀ X sgl₀` satisfies `E(π y) = y` and `⟪Ω̂, X Ω̂⟫ = ⟪Ω, E(X) Ω⟫`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Crossed.Space
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.Smearing

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Crossed

open scoped InnerProductSpace
open Filter Topology Modular

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (M : VonNeumannAlgebra K) (Ω : K)

/-! ## The covariant representation -/

/-- `π(y) = ⊕_s σ_{-s}(y)`. -/
noncomputable def π (y : K →L[ℂ] K) : L2Q K →L[ℂ] L2Q K := diag fun s : ℚ => σ M Ω (-(s : ℝ)) y

theorem isBddFam_π (y : K →L[ℂ] K) : IsBddFam fun s : ℚ => σ M Ω (-(s : ℝ)) y :=
  ⟨‖y‖, fun s => norm_σ_le M Ω _ y⟩

theorem π_apply (y : K →L[ℂ] K) (f : L2Q K) (s : ℚ) : π M Ω y f s = σ M Ω (-(s : ℝ)) y (f s) :=
  diag_apply _ (isBddFam_π M Ω y) f s

theorem norm_π_le (y : K →L[ℂ] K) : ‖π M Ω y‖ ≤ ‖y‖ :=
  norm_diag_le _ (norm_nonneg _) fun s => norm_σ_le M Ω _ y

theorem π_sgl (y : K →L[ℂ] K) (g : ℚ) (v : K) : π M Ω y (sgl g v) = sgl g (σ M Ω (-(g : ℝ)) y v) :=
  diag_sgl _ (isBddFam_π M Ω y) g v

theorem π_add (y z : K →L[ℂ] K) : π M Ω (y + z) = π M Ω y + π M Ω z := by
  unfold π
  rw [← diag_add (isBddFam_π M Ω y) (isBddFam_π M Ω z)]
  congr 1; funext s; exact σ_add_op M Ω _ y z

theorem π_smul (c : ℂ) (y : K →L[ℂ] K) : π M Ω (c • y) = c • π M Ω y := by
  unfold π
  rw [← diag_smul c (isBddFam_π M Ω y)]
  congr 1; funext s; exact σ_smul M Ω _ c y

theorem π_mul (y z : K →L[ℂ] K) : π M Ω (y * z) = π M Ω y * π M Ω z := by
  unfold π
  rw [← diag_mul (isBddFam_π M Ω y) (isBddFam_π M Ω z)]
  congr 1; funext s; exact σ_mul M Ω _ y z

theorem π_star (y : K →L[ℂ] K) : π M Ω (star y) = star (π M Ω y) := by
  unfold π
  rw [← diag_star (isBddFam_π M Ω y)]
  congr 1; funext s; exact σ_star M Ω _ y

theorem π_one : π M Ω (1 : K →L[ℂ] K) = 1 := by
  unfold π
  rw [← diag_one]
  congr 1; funext s; exact σ_one M Ω _

theorem π_zero : π M Ω (0 : K →L[ℂ] K) = 0 := by
  unfold π
  rw [← diag_zero]
  congr 1; funext s; simp only [σ, mul_zero, zero_mul]

/-- Covariance: `λ(g) π(y) λ(g)* = π(σ_g y)`. -/
theorem shift_π_shift (g : ℚ) (y : K →L[ℂ] K) :
    shift g * π M Ω y * shift (-g) = π M Ω (σ M Ω g y) := by
  unfold π
  rw [shift_mul_diag_mul_shift_neg _ (isBddFam_π M Ω y)]
  congr 1
  funext s
  rw [show (-((s - g : ℚ) : ℝ)) = -(s : ℝ) + g by push_cast; ring, σ_add]

theorem π_shift (g : ℚ) (y : K →L[ℂ] K) :
    π M Ω y * shift g = shift g * π M Ω (σ M Ω (-(g : ℝ)) y) := by
  have h := shift_π_shift M Ω (-g) y
  rw [Rat.cast_neg] at h
  rw [← h, neg_neg]
  simp only [mul_assoc, shift_neg_mul, mul_one]
  rw [← mul_assoc, shift_mul_neg, one_mul]

/-! ## The crossed product -/

/-- The generating set `π(M) ∪ λ(ℚ)`. -/
def gens : Set (L2Q K →L[ℂ] L2Q K) := {T | ∃ y ∈ M, π M Ω y = T} ∪ Set.range (shift (K := K))

/-- **The crossed product** `ℛ = M ⋊_σ ℚ`. -/
noncomputable def crossed : VonNeumannAlgebra (L2Q K) := wstar (gens M Ω)

theorem π_mem {y : K →L[ℂ] K} (hy : y ∈ M) : π M Ω y ∈ crossed M Ω :=
  subset_wstar (Or.inl ⟨y, hy, rfl⟩)

theorem shift_mem (g : ℚ) : (shift g : L2Q K →L[ℂ] L2Q K) ∈ crossed M Ω :=
  subset_wstar (Or.inr ⟨g, rfl⟩)

theorem star_mem_gens {T : L2Q K →L[ℂ] L2Q K} (hT : T ∈ gens M Ω) : star T ∈ gens M Ω := by
  rcases hT with ⟨y, hy, rfl⟩ | ⟨g, rfl⟩
  · exact Or.inl ⟨star y, star_mem hy, π_star M Ω y⟩
  · exact Or.inr ⟨-g, (shift_star g).symm⟩

/-- An operator commuting with the generators lies in the commutant of the crossed product. -/
theorem mem_commutant_of_commute_gens {z : L2Q K →L[ℂ] L2Q K}
    (h : ∀ T ∈ gens M Ω, Commute T z) : z ∈ (crossed M Ω).commutant := by
  rw [VonNeumannAlgebra.mem_commutant_iff]
  intro T hT
  refine (mem_wstar_iff.mp hT z ?_).symm
  rw [StarSubalgebra.mem_centralizer_iff]
  intro s hs
  exact ⟨(h s hs).eq, (h _ (star_mem_gens M Ω hs)).eq⟩

/-! ## The vector `Ω̂ = δ₀ ⊗ Ω` -/

/-- `Ω̂ = δ₀ ⊗ Ω`. -/
noncomputable def Ωh (Ω : K) : L2Q K := sgl 0 Ω

theorem norm_Ωh : ‖Ωh Ω‖ = ‖Ω‖ := norm_sgl 0 Ω

theorem π_Ωh (y : K →L[ℂ] K) : π M Ω y (Ωh Ω) = sgl 0 (y Ω) := by
  rw [Ωh, π_sgl, Rat.cast_zero, neg_zero, σ_zero]

theorem shift_π_Ωh (g : ℚ) (y : K →L[ℂ] K) : shift g (π M Ω y (Ωh Ω)) = sgl g (y Ω) := by
  rw [π_Ωh, shift_sgl, zero_add]

theorem inner_sgl_left (g : ℚ) (v : K) (f : L2Q K) : ⟪sgl g v, f⟫_ℂ = ⟪v, f g⟫_ℂ := by
  rw [lp.inner_eq_tsum]
  have : (fun s => ⟪sgl g v s, f s⟫_ℂ) = fun s => if s = g then ⟪v, f g⟫_ℂ else 0 := by
    funext s
    rw [sgl_apply]
    split_ifs with hs
    · rw [hs]
    · rw [inner_zero_left]
  rw [this, tsum_ite_eq]

/-- The dual state: `⟪Ω̂, λ(g) π(y) Ω̂⟫ = δ_{g,0} ⟪Ω, yΩ⟫`. -/
theorem inner_Ωh_shift_π (g : ℚ) (y : K →L[ℂ] K) :
    ⟪Ωh Ω, (shift g * π M Ω y : L2Q K →L[ℂ] L2Q K) (Ωh Ω)⟫_ℂ = if g = 0 then ⟪Ω, y Ω⟫_ℂ else 0 := by
  rw [mul_apply_eq_comp, shift_π_Ωh, Ωh, inner_sgl_sgl]
  by_cases h : g = 0
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

/-- The compression `E(X) = ev₀ X sgl₀`. -/
noncomputable def comp0 (X : L2Q K →L[ℂ] L2Q K) : K →L[ℂ] K := ev 0 ∘L X ∘L sgl 0

theorem comp0_apply (X : L2Q K →L[ℂ] L2Q K) (v : K) : comp0 X v = X (sgl 0 v) 0 := rfl

theorem comp0_π (y : K →L[ℂ] K) : comp0 (π M Ω y) = y := by
  ext v
  rw [comp0_apply, π_sgl, sgl_apply_self, Rat.cast_zero, neg_zero, σ_zero]

theorem inner_Ωh (X : L2Q K →L[ℂ] L2Q K) : ⟪Ωh Ω, X (Ωh Ω)⟫_ℂ = ⟪Ω, comp0 X Ω⟫_ℂ := by
  rw [Ωh, inner_sgl_left]; rfl

theorem comp0_one : comp0 (1 : L2Q K →L[ℂ] L2Q K) = 1 := by
  ext v; rw [comp0_apply, one_apply_eq_self, sgl_apply_self, one_apply_eq_self]

theorem comp0_add (X Y : L2Q K →L[ℂ] L2Q K) : comp0 (X + Y) = comp0 X + comp0 Y := by
  ext v; simp only [comp0_apply, _root_.add_apply, lp.coeFn_add, Pi.add_apply]

theorem comp0_smul (c : ℂ) (X : L2Q K →L[ℂ] L2Q K) : comp0 (c • X) = c • comp0 X := by
  ext v; simp only [comp0_apply, _root_.smul_apply, lp.coeFn_smul, Pi.smul_apply]

theorem inner_sgl_right (g : ℚ) (w : K) (f : L2Q K) : ⟪f, sgl g w⟫_ℂ = ⟪f g, w⟫_ℂ := by
  rw [← inner_conj_symm, inner_sgl_left, inner_conj_symm]

theorem comp0_star (X : L2Q K →L[ℂ] L2Q K) : comp0 (star X) = star (comp0 X) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  show ⟪(ContinuousLinearMap.adjoint X (sgl 0 v)) 0, w⟫_ℂ = ⟪v, X (sgl 0 w) 0⟫_ℂ
  rw [← inner_sgl_right, ContinuousLinearMap.adjoint_inner_left, inner_sgl_left]

theorem norm_comp0_le (X : L2Q K →L[ℂ] L2Q K) : ‖comp0 X‖ ≤ ‖X‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [comp0_apply]
  calc ‖X (sgl 0 v) 0‖ ≤ ‖X (sgl 0 v)‖ := norm_apply_le _ _
    _ ≤ ‖X‖ * ‖sgl 0 v‖ := X.le_opNorm _
    _ = ‖X‖ * ‖v‖ := by rw [norm_sgl]

theorem comp0_nonneg {X : L2Q K →L[ℂ] L2Q K} (hX : 0 ≤ X) : 0 ≤ comp0 X := by
  refine Resolver.Douglas.nonneg_of_re_inner ?_ fun v => ?_
  · have : IsSelfAdjoint X := IsSelfAdjoint.of_nonneg hX
    show star (comp0 X) = comp0 X
    rw [← comp0_star, this.star_eq]
  · rw [← inner_conj_symm, Complex.conj_re]
    show 0 ≤ (⟪v, X (sgl 0 v) 0⟫_ℂ).re
    rw [← inner_sgl_left]
    exact Resolver.Douglas.re_inner_nonneg_of_nonneg hX (sgl 0 v)

variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

include hc in
/-- `Ω̂` is cyclic for the crossed product. -/
theorem isCyclic_Ωh : IsCyclic (crossed M Ω : Set (L2Q K →L[ℂ] L2Q K)) (Ωh Ω) := by
  refine isCyclic_of_cyclicSpace_eq_top ?_
  refine eq_top_of_sgl_mem (isClosed_cyclicSpace _ _) fun g v => ?_
  have hv : v ∈ closure (orbit (M : Set (K →L[ℂ] K)) Ω : Set K) := by
    rw [hc.closure_eq]; exact Set.mem_univ v
  have hsub : (sgl g) '' (orbit (M : Set (K →L[ℂ] K)) Ω : Set K) ⊆
      (orbit (crossed M Ω : Set (L2Q K →L[ℂ] L2Q K)) (Ωh Ω) : Set (L2Q K)) := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_orbit_vn M hw
    rw [← shift_π_Ωh, ← mul_apply_eq_comp]
    exact apply_mem_orbit (mul_mem (shift_mem M Ω g) (π_mem M Ω hy))
  show sgl g v ∈ closure (orbit (crossed M Ω : Set (L2Q K →L[ℂ] L2Q K)) (Ωh Ω) : Set (L2Q K))
  exact closure_mono hsub (image_closure_subset_closure_image (sgl g).continuous ⟨v, hv, rfl⟩)

/-! ### The commutant: `1 ⊗ y′` and `W_g = λ(g)(1 ⊗ Δ^{-ig})` -/

include hs hc in
theorem amp_commutant_mem {y' : K →L[ℂ] K} (hy' : y' ∈ M.commutant) :
    amp y' ∈ (crossed M Ω).commutant := by
  refine mem_commutant_of_commute_gens M Ω fun T hT => ?_
  rcases hT with ⟨y, hy, rfl⟩ | ⟨g, rfl⟩
  · exact amp_diag_comm (isBddFam_π M Ω y) fun s =>
      VonNeumannAlgebra.mem_commutant_iff.mp hy' _ (σ_mem M Ω hs hc hy _)
  · exact shift_amp g y'

/-- `W_g = λ(g)(1 ⊗ Δ^{-ig})`. -/
noncomputable def W (g : ℚ) : L2Q K →L[ℂ] L2Q K := shift g * amp (Δit M Ω (-(g : ℝ)))

theorem W_Ωh (g : ℚ) : W M Ω g (Ωh Ω) = sgl g Ω := by
  rw [W, mul_apply_eq_comp, Ωh, amp_sgl, Δit_Ω, shift_sgl, zero_add]

theorem W_mem_commutant (g : ℚ) : W M Ω g ∈ (crossed M Ω).commutant := by
  refine mem_commutant_of_commute_gens M Ω fun T hT => ?_
  rcases hT with ⟨y, hy, rfl⟩ | ⟨h, rfl⟩
  · -- `π(y) W_g = W_g π(y)`
    rw [Commute, SemiconjBy, W, ← mul_assoc, π_shift, mul_assoc, mul_assoc]
    congr 1
    unfold π amp
    rw [← diag_mul (isBddFam_π M Ω _) (IsBddFam.const _),
      ← diag_mul (IsBddFam.const _) (isBddFam_π M Ω _)]
    congr 1
    funext s
    simp only [σ, neg_neg, mul_assoc]
    rw [← mul_assoc (Δit M Ω (g : ℝ)), Δit_comm M Ω (g : ℝ) (s : ℝ), mul_assoc, Δit_mul_neg,
      mul_one, ← mul_assoc, Δit_comm M Ω (-(s : ℝ)) (-(g : ℝ)), mul_assoc]
  · rw [Commute, SemiconjBy, W, ← mul_assoc, shift_comm, mul_assoc, shift_amp, ← mul_assoc]

include hs in
/-- `Ω̂` is cyclic for the commutant of the crossed product, hence separating. -/
theorem isSeparating_Ωh (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω) :
    IsSeparating (crossed M Ω : Set (L2Q K →L[ℂ] L2Q K)) (Ωh Ω) := by
  rw [isSeparating_iff_isCyclic_commutant]
  refine isCyclic_of_cyclicSpace_eq_top ?_
  refine eq_top_of_sgl_mem (isClosed_cyclicSpace _ _) fun g v => ?_
  have hcyc := hs.isCyclic_commutant
  have hv : v ∈ closure (orbit (M.commutant : Set (K →L[ℂ] K)) Ω : Set K) := by
    rw [hcyc.closure_eq]; exact Set.mem_univ v
  have hsub : (sgl g) '' (orbit (M.commutant : Set (K →L[ℂ] K)) Ω : Set K) ⊆
      (orbit ((crossed M Ω).commutant : Set (L2Q K →L[ℂ] L2Q K)) (Ωh Ω) : Set (L2Q K)) := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨y', hy', rfl⟩ := exists_of_mem_orbit_vn M.commutant hw
    have : sgl g (y' Ω) = (amp y' * W M Ω g) (Ωh Ω) := by
      rw [mul_apply_eq_comp, W_Ωh, amp_sgl]
    rw [this]
    exact apply_mem_orbit (mul_mem (amp_commutant_mem M Ω hs hc hy') (W_mem_commutant M Ω g))
  show sgl g v ∈ closure (orbit ((crossed M Ω).commutant : Set (L2Q K →L[ℂ] L2Q K)) (Ωh Ω) :
    Set (L2Q K))
  exact closure_mono hsub (image_closure_subset_closure_image (sgl g).continuous ⟨v, hv, rfl⟩)

end Crossed

end VN

end CommutingRepetition
