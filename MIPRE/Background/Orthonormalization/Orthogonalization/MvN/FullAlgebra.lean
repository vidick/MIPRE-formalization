/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/FullAlgebra.lean
-/
/-
# Tier T2: Theorem 1.2 for `B(H)`, `H` arbitrary

The semifinite reduction (`MvN/Semifinite.lean`, step S) applied to the net of
finite-rank projections of `B(H)`: for a finite-dimensional subspace `L ≤ H`
the corner `p B(H) p` (`p` the projection onto `L`) is `B(L)`, on which the
T1a engine applies (transport through the compression `B(H) → B(L)` and the
extension by zero `B(L) → B(H)`), so Theorem 1.2 holds at every finite-rank
projection; the projections onto the spans of finite sets of vectors form a
directed net converging strongly to `1`, and `orthAtN_of_net` concludes.

`povm_orthogonalization_of_mem_all_general` and
`povm_orthogonalization_fullAlgebra_general` are the literal instances of the
signed statement `povm_orthogonalization` for a von Neumann algebra containing
every operator, resp. for `fullAlgebra H`, on an arbitrary Hilbert space
(FIDELITY.md, "Instances"). Unconditional.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Cutdown
import MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.Main
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Semifinite
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.TypeIIINet

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder InnerProductSpace
open Filter Topology CommutingRepetition.VN Blocks

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Extension by zero -/

section Ext

-- `compressTo` and its lemmas (`../lean`, `VN/Cutdown.lean`) carry `[CompleteSpace H]`.
set_option linter.unusedSectionVars false

variable (L : Submodule ℂ H) [CompleteSpace L]

/-- The extension by zero `B(L) → B(H)`, `y ↦ ι ∘ y ∘ π`. -/
noncomputable def extByZero (y : L →L[ℂ] L) : H →L[ℂ] H :=
  L.subtypeL ∘L y ∘L L.orthogonalProjectionOnto

theorem extByZero_apply (y : L →L[ℂ] L) (v : H) :
    extByZero L y v = (y (L.orthogonalProjectionOnto v) : H) := rfl

/-- Extension by zero as a linear map. -/
noncomputable def extByZeroₗ : (L →L[ℂ] L) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun := extByZero L
  map_add' y z := by
    ext v
    simp [extByZero_apply]
  map_smul' c y := by
    ext v
    simp [extByZero_apply]

theorem extByZeroₗ_apply (y : L →L[ℂ] L) : extByZeroₗ L y = extByZero L y := rfl

theorem extByZero_sum {κ : Type*} (s : Finset κ) (f : κ → L →L[ℂ] L) :
    extByZero L (∑ k ∈ s, f k) = ∑ k ∈ s, extByZero L (f k) :=
  map_sum (extByZeroₗ L) f s

theorem extByZero_sub (y z : L →L[ℂ] L) : extByZero L (y - z) = extByZero L y - extByZero L z :=
  map_sub (extByZeroₗ L) y z

theorem compressTo_extByZero (y : L →L[ℂ] L) : compressTo L (extByZero L y) = y := by
  ext v
  rw [coe_compressTo_apply, extByZero_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.starProjection_eq_self_iff.mpr (y v).2]

theorem extByZero_compressTo {x : H →L[ℂ] H} (hx : L.starProjection * x * L.starProjection = x) :
    extByZero L (compressTo L x) = x := by
  ext v
  rw [extByZero_apply, compressTo_apply]
  change L.starProjection (x (L.starProjection v)) = x v
  conv_rhs => rw [← hx]
  rw [mul_apply_eq_comp, mul_apply_eq_comp]

theorem extByZero_mul (y z : L →L[ℂ] L) :
    extByZero L (y * z) = extByZero L y * extByZero L z := by
  ext v
  simp only [mul_apply_eq_comp, extByZero_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem extByZero_star (y : L →L[ℂ] L) : extByZero L (star y) = star (extByZero L y) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint]
  unfold extByZero
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL,
    Submodule.adjoint_orthogonalProjectionOnto, ContinuousLinearMap.comp_assoc]

theorem extByZero_one : extByZero L 1 = L.starProjection := by
  ext v
  rw [extByZero_apply, one_apply_eq_self]
  rfl

theorem extByZero_mul_starProjection (y : L →L[ℂ] L) :
    extByZero L y * L.starProjection = extByZero L y := by
  ext v
  rw [mul_apply_eq_comp, extByZero_apply, extByZero_apply]
  congr 2
  change L.orthogonalProjectionOnto ((L.orthogonalProjectionOnto v : L) : H) = _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- The compression as a linear map (general `H`). -/
noncomputable def compressToₗ' : (H →L[ℂ] H) →ₗ[ℂ] (L →L[ℂ] L) where
  toFun := compressTo L
  map_add' := compressTo_add L
  map_smul' := compressTo_smul L

theorem compressTo_sum' {κ : Type*} (s : Finset κ) (f : κ → H →L[ℂ] H) :
    compressTo L (∑ k ∈ s, f k) = ∑ k ∈ s, compressTo L (f k) :=
  map_sum (compressToₗ' L) f s

theorem compressTo_nonneg' {T : H →L[ℂ] H} (hT : 0 ≤ T) : 0 ≤ compressTo L T := by
  have hrr : CFC.sqrt T * CFC.sqrt T = T := CFC.sqrt_mul_sqrt_self T hT
  have hrsa : star (CFC.sqrt T) = CFC.sqrt T := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)).star_eq
  have hT' : T = star (CFC.sqrt T) * CFC.sqrt T := by rw [hrsa, hrr]
  rw [hT']
  exact compressTo_star_mul_self_nonneg L _

theorem compressTo_starProjection_self : compressTo L L.starProjection = 1 := by
  ext v
  rw [coe_compressTo_apply, one_apply_eq_self, Submodule.starProjection_eq_self_iff.mpr v.2,
    Submodule.starProjection_eq_self_iff.mpr v.2]

end Ext

/-! ### Theorem 1.2 at a finite-rank projection of `B(H)` -/

/-- For a von Neumann algebra containing every operator and a finite-dimensional
subspace `L`, Theorem 1.2 holds at the projection onto `L` (for every class of
functionals): the corner is `B(L)` and the T1a engine applies. -/
theorem orthAtP_of_mem_all_finiteRank (M : VonNeumannAlgebra H)
    (hM : ∀ x : H →L[ℂ] H, x ∈ M) (L : Submodule ℂ H) [FiniteDimensional ℂ L]
    (ι : Type*) [Fintype ι] (P : ((H →L[ℂ] H) →ₗ[ℂ] ℂ) → Prop) :
    OrthAtP M L.starProjection ι P := by
  intro φ _ hφ hφz a _ ha0 haz ε hε
  set p := L.starProjection with hp
  have hpP : IsStarProjection p := isStarProjection_starProjection
  have hap : ∀ i, a i * p = a i := mul_eq_self_of_sum_eq hpP ha0 haz
  have hpa : ∀ i, p * a i = a i := fun i => by
    have := congrArg star (hap i)
    rwa [star_mul, hpP.isSelfAdjoint.star_eq, (IsSelfAdjoint.of_nonneg (ha0 i)).star_eq] at this
  have hpap : ∀ i, p * a i * p = a i := fun i => by rw [hpa i, hap i]
  -- the functional on `B(L)`
  let φ' : (L →L[ℂ] L) →ₗ[ℂ] ℂ := φ.comp (extByZeroₗ L)
  have hφ'app : ∀ y, φ' y = φ (extByZero L y) := fun y => rfl
  have hφ' : ∀ y : L →L[ℂ] L, 0 ≤ φ' (star y * y) := fun y => by
    rw [hφ'app, extByZero_mul, extByZero_star]
    exact hφ _ (hM _)
  have hφ'1 : φ' 1 = 1 := by rw [hφ'app, extByZero_one]; exact hφz
  -- the POVM on `L`
  have hext : ∀ i, extByZero L (compressTo L (a i)) = a i := fun i =>
    extByZero_compressTo L (hpap i)
  have ha'0 : ∀ i, 0 ≤ compressTo L (a i) := fun i => compressTo_nonneg' L (ha0 i)
  have ha'1 : ∑ i, compressTo L (a i) = 1 := by
    rw [← compressTo_sum', haz, hp, compressTo_starProjection_self]
  have hε' : 1 - ε < (φ' (∑ i, compressTo L (a i) * compressTo L (a i))).re := by
    rw [hφ'app, extByZero_sum]
    simp only [extByZero_mul, hext]
    exact hε
  obtain ⟨p', hp', hp'1, hbound⟩ :=
    povm_orthogonalization_finDim φ' hφ' hφ'1 (fun i => compressTo L (a i)) ha'0 ha'1 ε hε'
  refine ⟨fun i => extByZero L (p' i), fun i => hM _, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · show extByZero L (p' i) * extByZero L (p' i) = extByZero L (p' i)
      rw [← extByZero_mul, (hp' i).isIdempotentElem.eq]
    · rw [IsSelfAdjoint, ← extByZero_star, (hp' i).isSelfAdjoint.star_eq]
  · exact extByZero_mul_starProjection L _
  · rw [← extByZero_sum, hp'1, extByZero_one]
  · have key : φ' (∑ i, star (compressTo L (a i) - p' i) * (compressTo L (a i) - p' i)) =
        φ (∑ i, star (a i - extByZero L (p' i)) * (a i - extByZero L (p' i))) := by
      rw [hφ'app, extByZero_sum]
      simp only [extByZero_mul, extByZero_star, extByZero_sub, hext]
    rw [key] at hbound
    exact hbound

/-! ### The net of finite-rank projections -/

/-- **Theorem 1.2 for a von Neumann algebra containing every operator**, for normal
functionals, on an arbitrary Hilbert space. -/
theorem orthAtN_of_mem_all (M : VonNeumannAlgebra H) (hM : ∀ x : H →L[ℂ] H, x ∈ M)
    (ι : Type*) [Fintype ι] : OrthAtN M 1 ι := by
  classical
  have hz : IsCentralProj M 1 := ⟨IsStarProjection.one _, one_mem M, fun x _ => Commute.one_left x⟩
  let p : Finset H → H →L[ℂ] H := fun α => (Submodule.span ℂ (α : Set H)).starProjection
  refine orthAtN_of_net M hz p (fun α => ⟨isStarProjection_starProjection, hM _, mul_one _⟩) ?_ ι
    (fun α => orthAtP_of_mem_all_finiteRank M hM _ ι _)
  refine ⟨⟨1, fun α => norm_le_one_of_isStarProjection isStarProjection_starProjection⟩,
    fun ξ => ?_⟩
  rw [one_apply_eq_self]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ({ξ} : Finset H)] with α hα
  exact (Submodule.starProjection_eq_self_iff.mpr
    (Submodule.subset_span (Finset.mem_coe.mpr (hα (Finset.mem_singleton_self ξ))))).symm

end Orthogonalization.MvN

namespace Orthogonalization

open scoped BigOperators ComplexOrder
open MvN

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Theorem 1.2** (`povm_orthogonalization`) for a von Neumann algebra containing every
operator of an arbitrary Hilbert space `H`: the instance of the signed statement
delivered by tier T2. -/
theorem povm_orthogonalization_of_mem_all_general (M : VonNeumannAlgebra H)
    (hM : ∀ x : H →L[ℂ] H, x ∈ M) (φ : NormalState M)
    {ι : Type*} [Fintype ι] (a : ι → H →L[ℂ] H) (ha : IsPOVM M a) (ε : ℝ)
    (hε : 1 - ε < (φ (∑ i, a i * a i)).re) :
    ∃ p : ι → H →L[ℂ] H, IsPVM M p ∧
      (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
  obtain ⟨p, hpM, hp, -, hsum, hlt⟩ := orthAtN_of_mem_all M hM ι φ.toLinearMap
    (NormalState.isNormalOn φ)
    φ.nonneg' φ.map_one' a ha.1
    (fun i => (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (ha.2.1 i)) ha.2.2 ε hε
  exact ⟨p, ⟨hpM, hp, hsum⟩, hlt⟩

/-- **Theorem 1.2** (`povm_orthogonalization`) for `M = B(H)`, `H` an arbitrary Hilbert
space (tier T2). -/
theorem povm_orthogonalization_fullAlgebra_general (φ : NormalState (fullAlgebra H))
    {ι : Type*} [Fintype ι] (a : ι → H →L[ℂ] H) (ha : IsPOVM (fullAlgebra H) a) (ε : ℝ)
    (hε : 1 - ε < (φ (∑ i, a i * a i)).re) :
    ∃ p : ι → H →L[ℂ] H, IsPVM (fullAlgebra H) p ∧
      (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε :=
  povm_orthogonalization_of_mem_all_general (fullAlgebra H) mem_fullAlgebra φ a ha ε hε

end Orthogonalization
