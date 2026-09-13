/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/MatrixFactor.lean
-/
/-
# `M_n(M)` of a factor is a factor; the diagonal trace on `M_n(M)`

Proof-side toolkit for tier T4a (Theorem 1.2 for II₁ factors) on the matrix
algebra `M_n(M) = matrixAlgebra M n` of `Orthogonalization/MvN/Defs.lean`,
extending the entry calculus of `Orthogonalization/MvN/Matrix.lean` and
`Orthogonalization/MvN/BlockCalc.lean`:

* the matrix units `e_{ij} ⊗ 1 = embed i ∘ proj j` on `H^n`, their entries,
  the entries of `X e_{ij}` and `e_{ij} X`, and their membership in `M_n(M)`;
* **`M_n(M)` of a factor is a factor**: an element of `M_n(M)` commuting with
  all of `M_n(M)` commutes with the matrix units, hence is an amplification
  `z ⊕ ⋯ ⊕ z`, and commutes with the amplifications `y ⊕ ⋯ ⊕ y` of `y ∈ M`,
  hence `z` is central in `M` and so a scalar;
* the **diagonal trace** `X ↦ ∑ᵢ τ(Xᵢᵢ)` on `B(H^n)` of a linear functional
  `τ` on `B(H)`: it is positive, tracial and faithful on `M_n(M)` as soon as
  `τ` is on `M`, and takes the value `n τ(x)` on `x ⊕ ⋯ ⊕ x`.

No statement of the paper is made here.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Matrix
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.BlockCalc

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

/- The algebra structure of `H^n →L[ℂ] H^n` is found by instance search only after unfolding
`PiLp`, which can exceed the default heartbeat budget (as in `MvN/BlockCalc.lean`). -/
set_option synthInstance.maxHeartbeats 100000

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder
open FinDim

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Matrix units `e_{ij} ⊗ 1` -/

/-- The matrix unit `e_{ij} ⊗ 1` on `H^n`. -/
noncomputable def matrixUnit {n : ℕ} (i j : Fin n) :
    BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n) := embed i ∘L proj j

omit [CompleteSpace H] in
theorem matrixUnit_apply {n : ℕ} (i j : Fin n) (w : BlockSpace H (Fin n)) :
    matrixUnit i j w = embed i (w j) := rfl

theorem entry_matrixUnit {n : ℕ} (i j k l : Fin n) :
    entry (matrixUnit (H := H) i j) k l = if k = i ∧ l = j then 1 else 0 := by
  ext v
  rw [entry_apply, matrixUnit_apply, proj_embed, embed_apply]
  by_cases hk : k = i
  · by_cases hl : l = j
    · simp [hk, hl]
    · simp [hk, hl, Ne.symm hl]
  · simp [hk]

/-- `(X e_{ij})_{kl} = δ_{jl} X_{ki}`. -/
theorem entry_mul_matrixUnit {n : ℕ} (X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n))
    (i j k l : Fin n) : entry (X * matrixUnit i j) k l = if j = l then entry X k i else 0 := by
  ext v
  rw [entry_apply, mul_apply_eq_comp, matrixUnit_apply, embed_apply]
  split_ifs
  · rfl
  · simp only [map_zero, zero_apply]

/-- `(e_{ij} X)_{kl} = δ_{ki} X_{jl}`. -/
theorem entry_matrixUnit_mul {n : ℕ} (i j : Fin n)
    (X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) (k l : Fin n) :
    entry (matrixUnit i j * X) k l = if k = i then entry X j l else 0 := by
  ext v
  rw [entry_apply, mul_apply_eq_comp, matrixUnit_apply, proj_embed]
  split_ifs
  · rfl
  · rfl

theorem matrixUnit_mem (M : VonNeumannAlgebra H) {n : ℕ} (i j : Fin n) :
    matrixUnit i j ∈ matrixAlgebra M n := by
  refine mem_matrixAlgebra_of_entry fun k l => ?_
  rw [entry_matrixUnit]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/-! ### `M_n(M)` of a factor is a factor -/

/-- **`M_n(M)` of a factor is a factor**: if every central element of `M` is a scalar, then
every central element of `M_n(M)` is a scalar. -/
theorem matrixAlgebra_factor (M : VonNeumannAlgebra H)
    (hfactor : ∀ z ∈ M, (∀ y ∈ M, Commute z y) → ∃ c : ℂ, z = c • (1 : H →L[ℂ] H)) (n : ℕ) :
    ∀ Z ∈ matrixAlgebra M n, (∀ Y ∈ matrixAlgebra M n, Commute Z Y) →
      ∃ c : ℂ, Z = c • (1 : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) := by
  intro Z hZ hc
  obtain _ | n := n
  · exact ⟨0, ext_entry fun i _ => i.elim0⟩
  -- commuting with `e_{ij}`: `Z_{ki} = δ_{ki} Z_{jj}`
  have key : ∀ k i j : Fin (n + 1), entry Z k i = if k = i then entry Z j j else 0 := by
    intro k i j
    have h := congrArg (fun Y => entry Y k j) (hc _ (matrixUnit_mem M i j)).eq
    simpa only [entry_mul_matrixUnit, entry_matrixUnit_mul, eq_self_iff_true, if_true] using h
  have hZz : Z = amplify (n + 1) (entry Z 0 0) :=
    ext_entry fun k i => by rw [entry_amplify, key k i 0]
  -- commuting with `y ⊕ ⋯ ⊕ y`, `y ∈ M`: `Z_{00}` is central in `M`
  obtain ⟨c, hcz⟩ := hfactor _ (entry_mem hZ 0 0) fun y hy => by
    have h := congrArg (fun Y => entry Y 0 0) (hc _ (amplify_mem hy)).eq
    rw [hZz] at h
    simp only [entry_mul_amplify, entry_amplify, if_true] at h
    exact h
  exact ⟨c, by rw [hZz, hcz, amplify_smul, amplify_one]⟩

/-! ### The diagonal trace `X ↦ ∑ᵢ τ(Xᵢᵢ)` -/

omit [CompleteSpace H] in
/-- The entry `(i, j)` as a linear map on `B(H^n)`. -/
noncomputable def entryₗ {n : ℕ} (i j : Fin n) :
    (BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun X := entry X i j
  map_add' X Y := entry_add X Y i j
  map_smul' c X := entry_smul c X i j

omit [CompleteSpace H] in
theorem entryₗ_apply {n : ℕ} (i j : Fin n) (X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) :
    entryₗ i j X = entry X i j := rfl

omit [CompleteSpace H] in
/-- The diagonal trace `X ↦ ∑ᵢ τ(Xᵢᵢ)` on `B(H^n)` of a linear functional `τ` on `B(H)`. -/
noncomputable def diagTrace (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (n : ℕ) :
    (BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) →ₗ[ℂ] ℂ :=
  ∑ i, τ.comp (entryₗ i i)

omit [CompleteSpace H] in
theorem diagTrace_apply (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (n : ℕ)
    (X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) :
    diagTrace τ n X = ∑ i, τ (entry X i i) := by
  rw [diagTrace, LinearMap.sum_apply]
  rfl

/-- The diagonal trace of a positive functional is positive on `M_n(M)`. -/
theorem diagTrace_nonneg (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hτ0 : ∀ x ∈ M, 0 ≤ τ (star x * x)) (n : ℕ) :
    ∀ X ∈ matrixAlgebra M n, 0 ≤ diagTrace τ n (star X * X) := by
  intro X hX
  rw [diagTrace_apply]
  simp only [entry_star_mul, map_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hτ0 _ (entry_mem hX k i)

/-- The diagonal trace of a tracial functional is tracial on `M_n(M)`. -/
theorem diagTrace_trace (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hτtr : ∀ x ∈ M, ∀ y ∈ M, τ (x * y) = τ (y * x)) (n : ℕ) :
    ∀ X ∈ matrixAlgebra M n, ∀ Y ∈ matrixAlgebra M n,
      diagTrace τ n (X * Y) = diagTrace τ n (Y * X) := by
  intro X hX Y hY
  simp only [diagTrace_apply, entry_mul, map_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
    hτtr _ (entry_mem hX i k) _ (entry_mem hY k i)

/-- The diagonal trace of a faithful positive functional is faithful on `M_n(M)`. -/
theorem diagTrace_faithful (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hτ0 : ∀ x ∈ M, 0 ≤ τ (star x * x)) (hτf : ∀ x ∈ M, τ (star x * x) = 0 → x = 0) (n : ℕ) :
    ∀ X ∈ matrixAlgebra M n, diagTrace τ n (star X * X) = 0 → X = 0 := by
  intro X hX h
  rw [diagTrace_apply] at h
  simp only [entry_star_mul, map_sum] at h
  rw [Finset.sum_eq_zero_iff_of_nonneg
    fun i _ => Finset.sum_nonneg fun k _ => hτ0 _ (entry_mem hX k i)] at h
  refine ext_entry fun k i => ?_
  have hi := h i (Finset.mem_univ i)
  rw [Finset.sum_eq_zero_iff_of_nonneg fun k _ => hτ0 _ (entry_mem hX k i)] at hi
  rw [entry_zero]
  exact hτf _ (entry_mem hX k i) (hi k (Finset.mem_univ k))

/-- The diagonal trace of `x ⊕ ⋯ ⊕ x` is `n τ(x)`. -/
theorem diagTrace_amplify (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (n : ℕ) (x : H →L[ℂ] H) :
    diagTrace τ n (amplify n x) = n * τ x := by
  rw [diagTrace_apply]
  simp only [entry_amplify, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- The diagonal trace of the scalar `c • 1` is `n c τ(1)`. -/
theorem diagTrace_smul_one (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (n : ℕ) (c : ℂ) :
    diagTrace τ n (c • (1 : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n))) =
      n * (c * τ 1) := by
  rw [← amplify_one n, ← amplify_smul, diagTrace_amplify, map_smul, smul_eq_mul]

end Orthogonalization.MvN
