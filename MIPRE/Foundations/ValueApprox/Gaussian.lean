/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.ValueApprox.Cayley
import MIPRE.Foundations.ValueApprox.Projective
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Gaussian rationals, and matrices with entries in a subfield

The enumeration of `lem:value-lower-approx` ranges over strategies whose matrices and state
have entries in the Gaussian rationals `ℚ(i)`. This file provides

* `GaussianRat`, the subfield of `ℂ` of numbers with rational real and imaginary parts, closed
  under complex conjugation (`GaussianRat.star_mem`) and dense (`GaussianRat.exists_norm_sub_le`);
* `EntriesIn K M`, "all entries of `M` lie in the subfield `K`", with its closure under the ring
  operations, conjugate transposition, Kronecker products, determinants, adjugates, inverses and
  hence the Cayley transform (`EntriesIn.cayley`) — which is how the enumeration reaches exact
  unitaries;
* entrywise rounding to Gaussian rationals, for matrices (`exists_entriesIn_norm_sub_le`), vectors
  (`exists_forall_mem_norm_sub_le`) and, preserving skew-Hermiticity by re-symmetrizing the
  rounded matrix, for skew-Hermitian matrices (`IsSkewHermitian.exists_entriesIn_norm_sub_le`).
-/

namespace MIPRE.ValueApprox

open Matrix
open scoped Kronecker

/-! ## The Gaussian rationals -/

/-- The Gaussian rationals `ℚ(i)`, as a subfield of `ℂ`: the numbers whose real and imaginary
parts are rational. -/
def GaussianRat : Subfield ℂ where
  carrier := {z | (∃ a : ℚ, (a : ℝ) = z.re) ∧ ∃ b : ℚ, (b : ℝ) = z.im}
  zero_mem' := ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
  one_mem' := ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩
  add_mem' := by
    rintro z w ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    exact ⟨⟨a + c, by simp [ha, hc]⟩, ⟨b + d, by simp [hb, hd]⟩⟩
  neg_mem' := by
    rintro z ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨-a, by simp [ha]⟩, ⟨-b, by simp [hb]⟩⟩
  mul_mem' := by
    rintro z w ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    exact ⟨⟨a * c - b * d, by simp [Complex.mul_re, ha, hb, hc, hd]⟩,
      ⟨a * d + b * c, by simp [Complex.mul_im, ha, hb, hc, hd]⟩⟩
  inv_mem' := by
    rintro z ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨⟨a / (a * a + b * b), ?_⟩, ⟨-b / (a * a + b * b), ?_⟩⟩
    · rw [Complex.inv_re, Complex.normSq_apply]
      push_cast
      rw [ha, hb]
    · rw [Complex.inv_im, Complex.normSq_apply]
      push_cast
      rw [ha, hb]

namespace GaussianRat

theorem mem_iff {z : ℂ} :
    z ∈ GaussianRat ↔ (∃ a : ℚ, (a : ℝ) = z.re) ∧ ∃ b : ℚ, (b : ℝ) = z.im :=
  Iff.rfl

theorem ratCast_mem (q : ℚ) : (q : ℂ) ∈ GaussianRat := ⟨⟨q, by simp⟩, ⟨0, by simp⟩⟩

theorem I_mem : Complex.I ∈ GaussianRat := ⟨⟨0, by simp⟩, ⟨1, by simp⟩⟩

theorem star_mem {z : ℂ} (hz : z ∈ GaussianRat) : star z ∈ GaussianRat := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  exact ⟨⟨a, by simp [ha]⟩, ⟨-b, by simp [hb]⟩⟩

theorem mem_iff_exists_eq {z : ℂ} : z ∈ GaussianRat ↔ ∃ a b : ℚ, z = a + b * Complex.I := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a, b, Complex.ext (by simp [ha]) (by simp [hb])⟩
  · rintro ⟨a, b, rfl⟩
    exact add_mem (ratCast_mem a) (mul_mem (ratCast_mem b) I_mem)

/-- Every complex number is within `η` of a Gaussian rational. -/
theorem exists_norm_sub_le (z : ℂ) {η : ℝ} (hη : 0 < η) : ∃ w ∈ GaussianRat, ‖z - w‖ ≤ η := by
  obtain ⟨a, ha⟩ := exists_rat_near z.re (half_pos hη)
  obtain ⟨b, hb⟩ := exists_rat_near z.im (half_pos hη)
  refine ⟨(a : ℂ) + (b : ℂ) * Complex.I,
    add_mem (ratCast_mem a) (mul_mem (ratCast_mem b) I_mem), ?_⟩
  calc ‖z - ((a : ℂ) + (b : ℂ) * Complex.I)‖
      ≤ |(z - ((a : ℂ) + (b : ℂ) * Complex.I)).re| +
          |(z - ((a : ℂ) + (b : ℂ) * Complex.I)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ η / 2 + η / 2 := by
        gcongr
        · simpa using ha.le
        · simpa using hb.le
    _ = η := add_halves η

end GaussianRat

/-! ## Matrices with entries in a subfield -/

variable (K : Subfield ℂ)

/-- All entries of `M` lie in the subfield `K`. -/
def EntriesIn {m n : Type*} (M : Matrix m n ℂ) : Prop := ∀ i j, M i j ∈ K

variable {K}

namespace EntriesIn

variable {m n p : Type*} {M N : Matrix m n ℂ}

theorem zero : EntriesIn K (0 : Matrix m n ℂ) := fun _ _ => zero_mem K

theorem add (hM : EntriesIn K M) (hN : EntriesIn K N) : EntriesIn K (M + N) :=
  fun i j => add_mem (hM i j) (hN i j)

theorem neg (hM : EntriesIn K M) : EntriesIn K (-M) := fun i j => neg_mem (hM i j)

theorem sub (hM : EntriesIn K M) (hN : EntriesIn K N) : EntriesIn K (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)

theorem smul {c : ℂ} (hc : c ∈ K) (hM : EntriesIn K M) : EntriesIn K (c • M) :=
  fun i j => mul_mem hc (hM i j)

theorem sum {ι : Type*} (s : Finset ι) {f : ι → Matrix m n ℂ}
    (hf : ∀ i ∈ s, EntriesIn K (f i)) : EntriesIn K (∑ i ∈ s, f i) := fun i j => by
  rw [Matrix.sum_apply]
  exact sum_mem fun k hk => hf k hk i j

theorem conjTranspose (hK : ∀ z ∈ K, star z ∈ K) (hM : EntriesIn K M) : EntriesIn K Mᴴ :=
  fun i j => hK _ (hM j i)

theorem mul [Fintype n] {N : Matrix n p ℂ} (hM : EntriesIn K M) (hN : EntriesIn K N) :
    EntriesIn K (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hM i k) (hN k j)

theorem one [DecidableEq n] : EntriesIn K (1 : Matrix n n ℂ) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem K
  · exact zero_mem K

theorem kronecker {m' n' : Type*} {M : Matrix m n ℂ} {N : Matrix m' n' ℂ} (hM : EntriesIn K M)
    (hN : EntriesIn K N) : EntriesIn K (M ⊗ₖ N) :=
  fun i j => mul_mem (hM i.1 j.1) (hN i.2 j.2)

theorem patternProj {A : Type*} [DecidableEq n] [DecidableEq A] (r : n → A) (a : A) :
    EntriesIn K (patternProj r a) := fun i j => by
  rw [MIPRE.ValueApprox.patternProj, Matrix.diagonal_apply]
  split_ifs
  · exact one_mem K
  · exact zero_mem K
  · exact zero_mem K

section Square

variable [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}

theorem det_mem (hM : EntriesIn K M) : M.det ∈ K := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem K _) (prod_mem fun i _ => hM _ _)

theorem adjugate (hM : EntriesIn K M) : EntriesIn K M.adjugate := fun i j => by
  rw [Matrix.adjugate_apply]
  refine det_mem fun i' j' => ?_
  rw [Matrix.updateRow_apply]
  split_ifs with h
  · rw [Pi.single_apply]
    split_ifs
    · exact one_mem K
    · exact zero_mem K
  · exact hM _ _

theorem inv (hM : EntriesIn K M) : EntriesIn K M⁻¹ := fun i j => by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact mul_mem (inv_mem hM.det_mem) (hM.adjugate i j)

/-- The Cayley transform of a matrix with entries in `K` has entries in `K`. -/
theorem cayley (hM : EntriesIn K M) : EntriesIn K (cayley M) :=
  (one.sub hM).mul (one.add hM).inv

end Square

end EntriesIn

/-! ## Rounding to Gaussian rationals -/

/-- Entrywise rounding of a matrix to Gaussian rationals. -/
theorem exists_entriesIn_norm_sub_le {m n : Type*} (M : Matrix m n ℂ) {η : ℝ} (hη : 0 < η) :
    ∃ R : Matrix m n ℂ, EntriesIn GaussianRat R ∧ ∀ i j, ‖M i j - R i j‖ ≤ η := by
  choose R hR hRη using fun i j => GaussianRat.exists_norm_sub_le (M i j) hη
  exact ⟨Matrix.of R, hR, hRη⟩

/-- Entrywise rounding of a vector to Gaussian rationals. -/
theorem exists_forall_mem_norm_sub_le {n : Type*} (v : n → ℂ) {η : ℝ} (hη : 0 < η) :
    ∃ w : n → ℂ, (∀ i, w i ∈ GaussianRat) ∧ ∀ i, ‖v i - w i‖ ≤ η := by
  choose w hw hwη using fun i => GaussianRat.exists_norm_sub_le (v i) hη
  exact ⟨w, hw, hwη⟩

/-- Rounding a skew-Hermitian matrix `S` entrywise to `R`, then re-symmetrizing to
`(R - Rᴴ) / 2`, gives a skew-Hermitian Gaussian-rational matrix within the same entrywise
distance of `S`. -/
theorem IsSkewHermitian.exists_entriesIn_norm_sub_le {n : Type*} {S : Matrix n n ℂ}
    (hS : IsSkewHermitian S) {η : ℝ} (hη : 0 < η) :
    ∃ T : Matrix n n ℂ, IsSkewHermitian T ∧ EntriesIn GaussianRat T ∧
      ∀ i j, ‖S i j - T i j‖ ≤ η := by
  obtain ⟨R, hR, hRη⟩ := MIPRE.ValueApprox.exists_entriesIn_norm_sub_le S hη
  have h2 : ((2 : ℂ)⁻¹) ∈ GaussianRat := inv_mem (by exact_mod_cast GaussianRat.ratCast_mem 2)
  refine ⟨(2 : ℂ)⁻¹ • (R - Rᴴ), ?_,
    (hR.sub (hR.conjTranspose fun _ => GaussianRat.star_mem)).smul h2, ?_⟩
  · unfold IsSkewHermitian
    rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, ← smul_neg, neg_sub]
    congr 1
    simp
  · intro i j
    have hSij : S i j = -star (S j i) := by
      have h := congrFun (congrFun hS i) j
      rw [conjTranspose_apply, Matrix.neg_apply] at h
      rw [h, neg_neg]
    have hrepr : S i j - ((2 : ℂ)⁻¹ • (R - Rᴴ)) i j
        = (2 : ℂ)⁻¹ * ((S i j - R i j) - star (S j i - R j i)) := by
      rw [Matrix.smul_apply, Matrix.sub_apply, conjTranspose_apply, smul_eq_mul, star_sub, hSij]
      ring
    have h2' : ‖(2 : ℂ)⁻¹‖ = 2⁻¹ := by simp
    rw [hrepr, norm_mul, h2']
    calc (2 : ℝ)⁻¹ * ‖(S i j - R i j) - star (S j i - R j i)‖
        ≤ 2⁻¹ * (‖S i j - R i j‖ + ‖star (S j i - R j i)‖) := by
          gcongr
          exact norm_sub_le _ _
      _ = 2⁻¹ * (‖S i j - R i j‖ + ‖S j i - R j i‖) := by rw [norm_star]
      _ ≤ 2⁻¹ * (η + η) := by
          gcongr
          · exact hRη i j
          · exact hRη j i
      _ = η := by ring

end MIPRE.ValueApprox
