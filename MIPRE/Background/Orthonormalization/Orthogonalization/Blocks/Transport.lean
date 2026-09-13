/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Blocks/Transport.lean
-/
/-
# Tier T1b, transport of Theorem 1.2 through a bijective compression

Proof-side machinery for tier T1b (`PLAN.md` §3, §8); no statement of the paper is
formalized here. Let `M` be a von Neumann algebra on a finite-dimensional Hilbert space `H`,
`z` a central projection of `M`, and `L ≤ range z` an `M`-invariant subspace such that
compression to `L` maps `M z = {x ∈ M | x z = x}` bijectively onto `B(L)`. Then Theorem 1.2
at `z` (`OrthAt M z ι`, `Blocks/Local.lean`) follows from the `B(L)` engine of tier T1a
(`povm_orthogonalization_finDim`):

* compression `c := compressTo L` is `ℂ`-linear, positive, `*`-preserving, multiplicative on
  `M` and sends `z` to `1`;
* its inverse `liftOp : B(L) → M z` (chosen by `hsurj`, unique by `hinj`) is therefore a
  `ℂ`-linear `*`-homomorphism sending `1` to `z`;
* the functional `φ' := φ ∘ liftOp` is positive and normalized on `B(L)`, the POVM
  `a' i := c (a i)` sums to `1`, and `φ' (∑ a' i²) = φ (∑ a i²)`;
* the PVM `p'` produced on `L` lifts to the PVM `p i := liftOp (p' i)` of `M` supported in
  `z`, with the same value of the error functional.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Cutdown
import MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.Main
import MIPRE.Background.Orthonormalization.Orthogonalization.Blocks.Local

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.Blocks

open scoped BigOperators ComplexOrder InnerProductSpace
open CommutingRepetition.VN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-! ### Compression: linearity, positivity, and the identity on an invariant subspace -/

section Compress

variable (K : Submodule ℂ H) [CompleteSpace K]

/-- Compression to `K` as a `ℂ`-linear map `B(H) → B(K)`. -/
noncomputable def compressToₗ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K) where
  toFun := compressTo K
  map_add' := compressTo_add K
  map_smul' := compressTo_smul K

theorem compressToₗ_apply (T : H →L[ℂ] H) : compressToₗ K T = compressTo K T := rfl

theorem compressTo_sub (S T : H →L[ℂ] H) :
    compressTo K (S - T) = compressTo K S - compressTo K T :=
  map_sub (compressToₗ K) S T

theorem compressTo_sum {ι : Type*} (s : Finset ι) (f : ι → H →L[ℂ] H) :
    compressTo K (∑ i ∈ s, f i) = ∑ i ∈ s, compressTo K (f i) :=
  map_sum (compressToₗ K) f s

/-- An operator acting as the identity on `K` compresses to `1`. -/
theorem compressTo_eq_one_of_forall_apply_eq {T : H →L[ℂ] H} (hT : ∀ v ∈ K, T v = v) :
    compressTo K T = 1 := by
  refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
  rw [coe_compressTo_apply_of_invariant K (fun v hv => by rw [hT v hv]; exact hv), hT v v.2,
    one_apply_eq_self]

/-- Compression preserves positivity (`T = √T * √T`). -/
theorem compressTo_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) : 0 ≤ compressTo K T := by
  have hrr : CFC.sqrt T * CFC.sqrt T = T := CFC.sqrt_mul_sqrt_self T hT
  have hrsa : star (CFC.sqrt T) = CFC.sqrt T :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)).star_eq
  have hT' : T = star (CFC.sqrt T) * CFC.sqrt T := by rw [hrsa, hrr]
  rw [hT']
  exact compressTo_star_mul_self_nonneg K _

end Compress

/-! ### The inverse of a bijective compression -/

section Lift

variable {M : VonNeumannAlgebra H} {z : H →L[ℂ] H} {L : Submodule ℂ H}

/-- An element of `M` supported in `z` on the right is supported in `z` on the left too
(`z` is central). -/
theorem mul_eq_self_left (hz : IsCentralProj M z) {x : H →L[ℂ] H} (hx : x ∈ M)
    (hxz : x * z = x) : z * x = x := by
  rw [(hz.commute x hx).eq, hxz]

variable (hsurj : ∀ y : L →L[ℂ] L, ∃ x ∈ M, x * z = x ∧ compressTo L x = y)

/-- The preimage in `M z = {x ∈ M | x z = x}` of an operator on `L` (chosen by `hsurj`). -/
noncomputable def liftOp (y : L →L[ℂ] L) : H →L[ℂ] H :=
  (hsurj y).choose

theorem liftOp_mem (y : L →L[ℂ] L) : liftOp hsurj y ∈ M := (hsurj y).choose_spec.1

theorem liftOp_mul_z (y : L →L[ℂ] L) : liftOp hsurj y * z = liftOp hsurj y :=
  (hsurj y).choose_spec.2.1

theorem compressTo_liftOp (y : L →L[ℂ] L) : compressTo L (liftOp hsurj y) = y :=
  (hsurj y).choose_spec.2.2

variable (hinj : ∀ x ∈ M, x * z = x → compressTo L x = 0 → x = 0)

include hinj in
/-- Uniqueness: an element of `M z` compressing to `y` is `liftOp y`. -/
theorem liftOp_eq_of {x : H →L[ℂ] H} {y : L →L[ℂ] L} (hx : x ∈ M) (hxz : x * z = x)
    (hxy : compressTo L x = y) : liftOp hsurj y = x := by
  have h1 : x - liftOp hsurj y ∈ M := sub_mem hx (liftOp_mem hsurj y)
  have h2 : (x - liftOp hsurj y) * z = x - liftOp hsurj y := by
    rw [sub_mul, hxz, liftOp_mul_z]
  have h3 : compressTo L (x - liftOp hsurj y) = 0 := by
    rw [compressTo_sub, hxy, compressTo_liftOp, sub_self]
  exact (sub_eq_zero.mp (hinj _ h1 h2 h3)).symm

include hinj in
theorem liftOp_add (y y' : L →L[ℂ] L) :
    liftOp hsurj (y + y') = liftOp hsurj y + liftOp hsurj y' :=
  liftOp_eq_of hsurj hinj (add_mem (liftOp_mem hsurj y) (liftOp_mem hsurj y'))
    (by rw [add_mul, liftOp_mul_z, liftOp_mul_z])
    (by rw [compressTo_add, compressTo_liftOp, compressTo_liftOp])

include hinj in
theorem liftOp_smul (c : ℂ) (y : L →L[ℂ] L) : liftOp hsurj (c • y) = c • liftOp hsurj y :=
  liftOp_eq_of hsurj hinj (smul_mem_vn M c (liftOp_mem hsurj y))
    (by rw [smul_mul_assoc, liftOp_mul_z])
    (by rw [compressTo_smul, compressTo_liftOp])

/-- The inverse of a bijective compression, as a `ℂ`-linear map `B(L) → B(H)`. -/
noncomputable def liftOpₗ : (L →L[ℂ] L) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun := liftOp hsurj
  map_add' := liftOp_add hsurj hinj
  map_smul' := liftOp_smul hsurj hinj

theorem liftOpₗ_apply (y : L →L[ℂ] L) : liftOpₗ hsurj hinj y = liftOp hsurj y := rfl

include hinj in
theorem liftOp_sub (y y' : L →L[ℂ] L) :
    liftOp hsurj (y - y') = liftOp hsurj y - liftOp hsurj y' :=
  map_sub (liftOpₗ hsurj hinj) y y'

include hinj in
theorem liftOp_sum {ι : Type*} (s : Finset ι) (f : ι → L →L[ℂ] L) :
    liftOp hsurj (∑ i ∈ s, f i) = ∑ i ∈ s, liftOp hsurj (f i) :=
  map_sum (liftOpₗ hsurj hinj) f s

variable (hz : IsCentralProj M z) (hLM : ∀ x ∈ M, ∀ v ∈ L, x v ∈ L) (hLz : ∀ v ∈ L, z v = v)

include hinj hLM in
theorem liftOp_mul (y y' : L →L[ℂ] L) :
    liftOp hsurj (y * y') = liftOp hsurj y * liftOp hsurj y' :=
  liftOp_eq_of hsurj hinj (mul_mem (liftOp_mem hsurj y) (liftOp_mem hsurj y'))
    (by rw [mul_assoc, liftOp_mul_z])
    (by rw [compressTo_mul_of_invariant L _ (hLM _ (liftOp_mem hsurj y')), compressTo_liftOp,
      compressTo_liftOp])

include hinj hz in
theorem liftOp_star (y : L →L[ℂ] L) : liftOp hsurj (star y) = star (liftOp hsurj y) := by
  refine liftOp_eq_of hsurj hinj (star_mem (liftOp_mem hsurj y)) ?_
    (by rw [compressTo_star, compressTo_liftOp])
  have hzs : star z = z := hz.isStarProjection.isSelfAdjoint.star_eq
  have hzx : z * liftOp hsurj y = liftOp hsurj y :=
    mul_eq_self_left hz (liftOp_mem hsurj y) (liftOp_mul_z hsurj y)
  calc star (liftOp hsurj y) * z = star (z * liftOp hsurj y) := by rw [star_mul, hzs]
    _ = star (liftOp hsurj y) := by rw [hzx]

include hinj hz hLz in
theorem liftOp_one : liftOp hsurj 1 = z :=
  liftOp_eq_of hsurj hinj hz.mem hz.isStarProjection.isIdempotentElem.eq
    (compressTo_eq_one_of_forall_apply_eq L hLz)

include hinj hz hLM in
/-- Projections of `B(L)` lift to projections of `M`. -/
theorem isStarProjection_liftOp {y : L →L[ℂ] L} (hy : IsStarProjection y) :
    IsStarProjection (liftOp hsurj y) :=
  ⟨by
    show liftOp hsurj y * liftOp hsurj y = liftOp hsurj y
    rw [← liftOp_mul hsurj hinj hLM, hy.isIdempotentElem.eq],
   by
    show star (liftOp hsurj y) = liftOp hsurj y
    rw [← liftOp_star hsurj hinj hz, hy.isSelfAdjoint.star_eq]⟩

/-- The transported functional `φ ∘ liftOp` on `B(L)`. -/
noncomputable def liftFunctional (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) : (L →L[ℂ] L) →ₗ[ℂ] ℂ :=
  φ.comp (liftOpₗ hsurj hinj)

theorem liftFunctional_apply (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (y : L →L[ℂ] L) :
    liftFunctional hsurj hinj φ y = φ (liftOp hsurj y) := rfl

include hz hLM in
/-- A functional positive on `M` transports to a functional positive on all of `B(L)`. -/
theorem liftFunctional_nonneg {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} (hφ : ∀ x ∈ M, 0 ≤ φ (star x * x))
    (y : L →L[ℂ] L) : 0 ≤ liftFunctional hsurj hinj φ (star y * y) := by
  rw [liftFunctional_apply, liftOp_mul hsurj hinj hLM, liftOp_star hsurj hinj hz]
  exact hφ _ (liftOp_mem hsurj y)

include hz hLz in
theorem liftFunctional_one {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} (hφz : φ z = 1) :
    liftFunctional hsurj hinj φ 1 = 1 := by
  rw [liftFunctional_apply, liftOp_one hsurj hinj hz hLz, hφz]

end Lift

/-! ### The transport theorem -/

/-- **Transport of Theorem 1.2 through a bijective compression.** If `z` is a central
projection of `M`, `L ≤ range z` is an `M`-invariant subspace, and compression to `L` maps
`{x ∈ M | x z = x}` bijectively onto `B(L)`, then Theorem 1.2 holds at `z`. -/
theorem orthAt_of_compress_bijective (M : VonNeumannAlgebra H) {z : H →L[ℂ] H}
    (hz : IsCentralProj M z) (L : Submodule ℂ H) (hLz : ∀ v ∈ L, z v = v)
    (hLM : ∀ x ∈ M, ∀ v ∈ L, x v ∈ L)
    (hinj : ∀ x ∈ M, x * z = x → compressTo L x = 0 → x = 0)
    (hsurj : ∀ y : L →L[ℂ] L, ∃ x ∈ M, x * z = x ∧ compressTo L x = y)
    (ι : Type*) [Fintype ι] : OrthAt M z ι := by
  intro φ hφ hφz a haM ha0 haz ε hε
  -- the compressed POVM `a' i := compressTo L (a i)` and its lift back
  have haz' : ∀ i, a i * z = a i := mul_eq_self_of_sum_eq hz.isStarProjection ha0 haz
  have hlift_a : ∀ i, liftOp hsurj (compressTo L (a i)) = a i := fun i =>
    liftOp_eq_of hsurj hinj (haM i) (haz' i) rfl
  have ha'0 : ∀ i, 0 ≤ compressTo L (a i) := fun i => compressTo_nonneg L (ha0 i)
  have ha'1 : ∑ i, compressTo L (a i) = 1 := by
    rw [← compressTo_sum, haz, compressTo_eq_one_of_forall_apply_eq L hLz]
  -- the transported hypothesis `φ' (∑ a' i²) = φ (∑ a i²)`
  have hε' : 1 - ε <
      (liftFunctional hsurj hinj φ (∑ i, compressTo L (a i) * compressTo L (a i))).re := by
    rw [liftFunctional_apply, liftOp_sum hsurj hinj]
    simp only [liftOp_mul hsurj hinj hLM, hlift_a]
    exact hε
  -- the `B(L)` engine
  obtain ⟨p', hp', hp'1, hbound⟩ := povm_orthogonalization_finDim (liftFunctional hsurj hinj φ)
    (liftFunctional_nonneg hsurj hinj hz hLM hφ) (liftFunctional_one hsurj hinj hz hLz hφz)
    (fun i => compressTo L (a i)) ha'0 ha'1 ε hε'
  refine ⟨fun i => liftOp hsurj (p' i), fun i => liftOp_mem hsurj _,
    fun i => isStarProjection_liftOp hsurj hinj hz hLM (hp' i), fun i => liftOp_mul_z hsurj _,
    ?_, ?_⟩
  · rw [← liftOp_sum hsurj hinj, hp'1, liftOp_one hsurj hinj hz hLz]
  · have key : liftFunctional hsurj hinj φ
        (∑ i, star (compressTo L (a i) - p' i) * (compressTo L (a i) - p' i)) =
        φ (∑ i, star (a i - liftOp hsurj (p' i)) * (a i - liftOp hsurj (p' i))) := by
      rw [liftFunctional_apply, liftOp_sum hsurj hinj]
      simp only [liftOp_mul hsurj hinj hLM, liftOp_star hsurj hinj hz, liftOp_sub hsurj hinj,
        hlift_a]
    rw [key] at hbound
    exact hbound

end Orthogonalization.Blocks
