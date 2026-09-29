/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import MIPRE.Tactics

@[expose] public section

/-!
# The Halmos unitary of a partial isometry, and the dilation of a positive operator valued measure

Plain algebra in the ring of matrices over a star ring `R`, which
`MIPRE/Foundations/CommutingDilation.lean` reads with `R` the bounded operators on a Hilbert
space through `MIPRE/Foundations/OperatorMatrix.lean`.

* **The Halmos unitary** (`Halmos.extension`). For a partial isometry `w` (`w wᴴ w = w`) in
  `Matrix m m R`, the block matrix `[[w, 1 − w wᴴ], [1 − wᴴ w, wᴴ]]` on `m ⊕ m` is
  unitary (`conjTranspose_mul_extension`, `extension_mul_conjTranspose`). It extends `w` without
  comparing the two defect projections `1 − w wᴴ` and `1 − wᴴ w`; an extension of `w` inside
  `Matrix m m R` itself would have to compare them, and in infinite dimension, inside the
  commutant of another family of operators, that comparison is Murray–von Neumann theory.
* **The Naimark matrix** (`Halmos.naimark`). For `s : m → R` with self-adjoint entries and
  `∑ a, s a * s a = 1`, the matrix whose `a₀`-th column is `s` and whose other columns vanish
  is a partial isometry, with `wᴴ w` the matrix unit at `(a₀, a₀)`
  (`conjTranspose_naimark_mul_naimark`, `naimark_mul_conjTranspose_mul`).
* **The dilated projections** (`Halmos.proj`). `proj w a := Uᴴ Q_a U`, with `U` the Halmos
  unitary and `Q_a` the diagonal projection onto the two copies of the coordinate `a`, is a star
  projection (`isStarProjection_proj`), the `proj w a` sum to one (`sum_proj`), the
  `(inl a₀, inl a₀)` entry of `proj (naimark s a₀) a` is `s a * s a` (`proj_naimark_inl_inl`),
  and `proj (naimark s a₀) a` commutes with the constant diagonal matrix of any `c` commuting
  with every `s a` (`commute_diagonal_proj_naimark`).

So `a ↦ proj (naimark s a₀) a` is a projection-valued measure that compresses, at the unit
vector `e_{inl a₀}`, to the positive operator valued measure `a ↦ s a * s a`, and it commutes
with whatever commutes with the `s a`. With `s a = √E_a` this is the commutation-preserving
Naimark dilation of `planning/mipco-track.md` §5, Phase 1(a), and of
`reports/co-generalization-audit.md` §4.
-/

namespace MIPRE

namespace Halmos

open Matrix

variable {m : Type*} [Fintype m] [DecidableEq m] {R : Type*} [Ring R] [StarRing R]

/-! ## The Halmos unitary -/

/-- The Halmos extension of `w`: the block matrix `[[w, 1 − w wᴴ], [1 − wᴴ w, wᴴ]]`. -/
def extension (w : Matrix m m R) : Matrix (m ⊕ m) (m ⊕ m) R :=
  fromBlocks w (1 - w * wᴴ) (1 - wᴴ * w) wᴴ

theorem conjTranspose_extension (w : Matrix m m R) :
    (extension w)ᴴ = fromBlocks wᴴ (1 - wᴴ * w) (1 - w * wᴴ) w := by
  simp only [extension, fromBlocks_conjTranspose, conjTranspose_conjTranspose, conjTranspose_sub,
    conjTranspose_one, conjTranspose_mul]

section PartialIsometry

variable {w : Matrix m m R} (hw : w * wᴴ * w = w)
include hw

omit [DecidableEq m] in
theorem conjTranspose_mul_mul_conjTranspose : wᴴ * w * wᴴ = wᴴ := by
  have h := congrArg conjTranspose hw
  simp only [conjTranspose_mul, conjTranspose_conjTranspose] at h
  rwa [Matrix.mul_assoc]

theorem mul_sub_conjTranspose_mul : w * (1 - wᴴ * w) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hw, sub_self]

theorem sub_mul_conjTranspose_mul : (1 - w * wᴴ) * w = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, hw, sub_self]

theorem conjTranspose_mul_sub : wᴴ * (1 - w * wᴴ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
    conjTranspose_mul_mul_conjTranspose hw, sub_self]

theorem sub_mul_conjTranspose : (1 - wᴴ * w) * wᴴ = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, conjTranspose_mul_mul_conjTranspose hw, sub_self]

theorem sub_conjTranspose_mul_idem : (1 - wᴴ * w) * (1 - wᴴ * w) = 1 - wᴴ * w := by
  have hq : wᴴ * w * (wᴴ * w) = wᴴ * w := by
    rw [← Matrix.mul_assoc, conjTranspose_mul_mul_conjTranspose hw]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hq, sub_self, sub_zero]

theorem sub_mul_conjTranspose_idem : (1 - w * wᴴ) * (1 - w * wᴴ) = 1 - w * wᴴ := by
  have hp : w * wᴴ * (w * wᴴ) = w * wᴴ := by rw [← Matrix.mul_assoc, hw]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hp, sub_self, sub_zero]

/-- **The Halmos extension of a partial isometry is an isometry.** -/
theorem conjTranspose_mul_extension : (extension w)ᴴ * extension w = 1 := by
  rw [conjTranspose_extension, extension, fromBlocks_multiply, sub_conjTranspose_mul_idem hw,
    conjTranspose_mul_sub hw, sub_mul_conjTranspose hw, sub_mul_conjTranspose_mul hw,
    mul_sub_conjTranspose_mul hw, sub_mul_conjTranspose_idem hw, ← fromBlocks_one]
  congr 1 <;> abel

/-- **The Halmos extension of a partial isometry is a co-isometry.** -/
theorem extension_mul_conjTranspose : extension w * (extension w)ᴴ = 1 := by
  rw [conjTranspose_extension, extension, fromBlocks_multiply, sub_mul_conjTranspose_idem hw,
    mul_sub_conjTranspose_mul hw, sub_mul_conjTranspose_mul hw, sub_mul_conjTranspose hw,
    conjTranspose_mul_sub hw, sub_conjTranspose_mul_idem hw, ← fromBlocks_one]
  congr 1 <;> abel

end PartialIsometry

/-! ## The dilated projections -/

/-- The diagonal projection of `R^(m ⊕ m)` onto the two copies of the coordinate `a`. -/
def coordProj (a : m) : Matrix (m ⊕ m) (m ⊕ m) R :=
  diagonal fun k => if k.elim id id = a then 1 else 0

omit [Fintype m] in
theorem conjTranspose_coordProj (a : m) :
    (coordProj a : Matrix (m ⊕ m) (m ⊕ m) R)ᴴ = coordProj a := by
  rw [coordProj, diagonal_conjTranspose]
  congr 1
  funext k
  split_ifs <;> simp_all

omit [StarRing R] in
theorem coordProj_mul_self (a : m) :
    (coordProj a : Matrix (m ⊕ m) (m ⊕ m) R) * coordProj a = coordProj a := by
  rw [coordProj, diagonal_mul_diagonal]
  congr 1
  funext k
  split_ifs <;> simp

omit [StarRing R] in
theorem sum_coordProj : ∑ a, (coordProj a : Matrix (m ⊕ m) (m ⊕ m) R) = 1 := by
  ext k l
  rw [Matrix.sum_apply, one_apply]
  by_cases h : k = l
  · subst h
    simp [coordProj]
  · simp [coordProj, h]

/-- The dilated projection at the outcome `a`: `Uᴴ Q_a U`, for `U` the Halmos extension. -/
def proj (w : Matrix m m R) (a : m) : Matrix (m ⊕ m) (m ⊕ m) R :=
  (extension w)ᴴ * coordProj a * extension w

/-- **The dilated projections are star projections.** -/
theorem isStarProjection_proj {w : Matrix m m R} (hw : w * wᴴ * w = w) (a : m) :
    IsStarProjection (proj w a) where
  isIdempotentElem := by
    rw [IsIdempotentElem, proj]
    calc (extension w)ᴴ * coordProj a * extension w *
          ((extension w)ᴴ * coordProj a * extension w)
        = (extension w)ᴴ * coordProj a * (extension w * (extension w)ᴴ) * coordProj a *
            extension w := by
          simp only [Matrix.mul_assoc]
      _ = (extension w)ᴴ * (coordProj a * coordProj a) * extension w := by
          rw [extension_mul_conjTranspose hw, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = (extension w)ᴴ * coordProj a * extension w := by rw [coordProj_mul_self]
  isSelfAdjoint := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, proj, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, conjTranspose_coordProj, Matrix.mul_assoc]

/-- **The dilated projections sum to one.** -/
theorem sum_proj {w : Matrix m m R} (hw : w * wᴴ * w = w) : ∑ a, proj w a = 1 := by
  simp only [proj]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_coordProj, Matrix.mul_one,
    conjTranspose_mul_extension hw]

/-! ## The Naimark matrix -/

/-- The Naimark matrix of `s` at `a₀`: its `a₀`-th column is `s`, its other columns vanish. -/
def naimark (s : m → R) (a₀ : m) : Matrix m m R :=
  of fun i j => if j = a₀ then s i else 0

section Naimark

variable {s : m → R} (hs : ∀ a, star (s a) = s a)
include hs

omit [Fintype m] in
theorem conjTranspose_naimark_apply (a₀ i j : m) :
    (naimark s a₀)ᴴ i j = if i = a₀ then s j else 0 := by
  rw [conjTranspose_apply, naimark, of_apply]
  split_ifs <;> simp [hs]

variable (hsum : ∑ a, s a * s a = 1)
include hsum

/-- `wᴴ w` is the matrix unit at `(a₀, a₀)`. -/
theorem conjTranspose_naimark_mul_naimark (a₀ : m) :
    (naimark s a₀)ᴴ * naimark s a₀ = diagonal fun j => if j = a₀ then 1 else 0 := by
  ext i j
  rw [mul_apply, diagonal_apply]
  simp only [conjTranspose_naimark_apply hs]
  simp only [naimark, of_apply]
  by_cases hi : i = a₀ <;> by_cases hj : j = a₀
  · subst hi hj
    simpa using hsum
  · simp [hj, Ne.symm hj, hi]
  · simp [hi, hj]
  · simp [hi, hj]

/-- **The Naimark matrix is a partial isometry.** -/
theorem naimark_mul_conjTranspose_mul (a₀ : m) :
    naimark s a₀ * (naimark s a₀)ᴴ * naimark s a₀ = naimark s a₀ := by
  rw [Matrix.mul_assoc, conjTranspose_naimark_mul_naimark hs hsum]
  ext i j
  rw [mul_diagonal, naimark, of_apply]
  split_ifs <;> simp

/-- **The dilation compresses to `s a * s a` at `e_{inl a₀}`.** -/
theorem proj_naimark_inl_inl (a₀ a : m) :
    proj (naimark s a₀) a (Sum.inl a₀) (Sum.inl a₀) = s a * s a := by
  have hq := conjTranspose_naimark_mul_naimark hs hsum a₀
  rw [proj, mul_apply, Fintype.sum_sum_type]
  simp only [coordProj, mul_diagonal, conjTranspose_apply, extension, fromBlocks_apply₁₁,
    fromBlocks_apply₂₁, Sum.elim_inl, Sum.elim_inr, id_eq, hq, sub_apply, one_apply,
    diagonal_apply]
  have h0 : ∀ b : m, ((if b = a₀ then (1 : R) else 0) -
      if b = a₀ then (if b = a₀ then 1 else 0) else 0) = 0 := by
    intro b
    split_ifs <;> simp
  simp only [h0, mul_zero, Finset.sum_const_zero, add_zero, naimark, of_apply, ite_true, hs]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

omit hs hsum [StarRing R] in
theorem commute_diagonal_naimark {c : R} (hc : ∀ a, Commute c (s a)) (a₀ : m) :
    Commute (diagonal fun _ : m => c) (naimark s a₀) := by
  show _ = _
  ext i j
  rw [diagonal_mul, mul_diagonal, naimark, of_apply]
  split_ifs
  · exact (hc i).eq
  · simp

omit hsum in
theorem commute_diagonal_conjTranspose_naimark {c : R} (hc : ∀ a, Commute c (s a)) (a₀ : m) :
    Commute (diagonal fun _ : m => c) (naimark s a₀)ᴴ := by
  show _ = _
  ext i j
  rw [diagonal_mul, mul_diagonal, conjTranspose_naimark_apply hs]
  split_ifs
  · exact (hc j).eq
  · simp

end Naimark

omit [DecidableEq m] [StarRing R] in
theorem commute_fromBlocks_diagonal {D X Y Z W : Matrix m m R} (hX : Commute D X)
    (hY : Commute D Y) (hZ : Commute D Z) (hW : Commute D W) :
    Commute (fromBlocks D 0 0 D) (fromBlocks X Y Z W) := by
  show _ = _
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, hX.eq, hY.eq, hZ.eq, hW.eq]

omit [Fintype m] [StarRing R] in
theorem diagonal_const_eq_fromBlocks (c : R) :
    (diagonal fun _ : m ⊕ m => c) =
      fromBlocks (diagonal fun _ => c) 0 0 (diagonal fun _ => c) := by
  rw [fromBlocks_diagonal]
  congr 1
  funext k
  cases k <;> rfl

/-- **The dilation commutes with whatever commutes with the `s a`.** -/
theorem commute_diagonal_proj_naimark {s : m → R} (hs : ∀ a, star (s a) = s a) {c : R}
    (hc : ∀ a, Commute c (s a)) (a₀ a : m) :
    Commute (diagonal fun _ : m ⊕ m => c) (proj (naimark s a₀) a) := by
  have hw := commute_diagonal_naimark hc a₀
  have hwt := commute_diagonal_conjTranspose_naimark hs hc a₀
  have h1 := Commute.one_right (diagonal fun _ : m => c)
  have hU : Commute (diagonal fun _ : m ⊕ m => c) (extension (naimark s a₀)) := by
    rw [diagonal_const_eq_fromBlocks, extension]
    exact commute_fromBlocks_diagonal hw (h1.sub_right (hw.mul_right hwt))
      (h1.sub_right (hwt.mul_right hw)) hwt
  have hUt : Commute (diagonal fun _ : m ⊕ m => c) (extension (naimark s a₀))ᴴ := by
    rw [diagonal_const_eq_fromBlocks, conjTranspose_extension]
    exact commute_fromBlocks_diagonal hwt (h1.sub_right (hwt.mul_right hw))
      (h1.sub_right (hw.mul_right hwt)) hw
  have hQ : Commute (diagonal fun _ : m ⊕ m => c) (coordProj a) := by
    show _ = _
    rw [coordProj, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext k
    split_ifs <;> simp
  exact (hUt.mul_right hQ).mul_right hU

end Halmos

end MIPRE

end
