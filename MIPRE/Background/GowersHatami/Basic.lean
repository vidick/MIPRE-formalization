/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Distances
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The Gowers–Hatami theorem

This file proves the Gowers–Hatami stability theorem for approximate unitary
representations of a finite group `G`, in the dimension-normalized Hilbert–Schmidt
norm of `MIPRE.Foundations.Distances`: every `ε`-approximate representation
`ρ : G → U(ℂᵈ)` is, on average over `G`, `2ε`-close to the compression of an exact
unitary representation on a larger space.

The proof follows the "regular representation" model, which avoids the group Fourier
transform and the decomposition into irreducible representations.  Given an
approximate representation `ρ`, it uses

* the enlarged space `L(G, ℂᵈ)` of functions `G → ℂᵈ` with the uniform inner
  product, whose matrix index type is `GowersHatami.Index G d = G × Fin d`;
* the isometry `V : ℂᵈ → L(G, ℂᵈ)`, `V u = (x ↦ ρ(x) u)`
  (`GowersHatami.embedding`, stored as the `d × (G × d)` matrix of its adjoint);
* the right regular representation `ρ₀`, `(ρ₀(x) F)(y) = F (y * x)`
  (`GowersHatami.rightRegular`).

The two identities driving the proof are that `V` is an isometry
(`GowersHatami.embedding_isometry`) and that the compression of `ρ₀(x)` by `V` is
the average `𝔼_y ρ(y)ᴴ ρ(y * x)` (`GowersHatami.compression_eq_average`).

## Main definitions

- `MIPRE.IsApproxRepresentation`: `ε`-approximate representations of a finite group,
  i.e. unitary-valued maps `f` with `𝔼_{x,y} Re ⟨f(x) f(y), f(xy)⟩_hs ≥ 1 - ε`.

## Main results

- `MIPRE.gowers_hatami_prod`: the Gowers–Hatami theorem, with the exact
  representation living on the concrete index type `G × Fin d`.
- `MIPRE.gowers_hatami`: the same statement with the enlarged space reindexed to
  `Fin d'` for some `d' ≥ d` (namely `d' = |G| * d`).

## Implementation notes

- Matrices act on row vectors, so an operator `H₁ → H₂` is stored as a
  `H₁ × H₂`-indexed matrix and the isometry condition for `V` reads `V * Vᴴ = 1`;
  the compression of an operator `R` on the enlarged space is `V * R * Vᴴ`.
- The approximation hypothesis is stated in correlation form
  (`𝔼 Re ⟨f(x) f(y), f(xy)⟩_hs ≥ 1 - ε`); for unitary-valued `f` this is equivalent
  to the defect form `𝔼 ‖f(x) f(y) - f(xy)‖²_hs ≤ 2ε` by `hsNormSq_sub_eq`.
- No positivity assumption on `ε` and no positivity assumption on `d` are needed:
  all bounds on unitaries are stated as inequalities (`hsNormSq U ≤ 1`), which hold
  trivially when `d = 0`.
- The section "Hilbert–Schmidt norm toolkit" collects general facts about
  `hsInner`/`hsNormSq`; these are natural candidates to move into
  `MIPRE.Foundations.Distances`.
-/

open scoped Matrix ComplexConjugate ComplexOrder
open Finset

namespace MIPRE

variable {d : ℕ}
variable (G : Type*) [Group G] [Fintype G]

/-! ## Hilbert–Schmidt norm toolkit -/

theorem hsInner_conj_symm {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    star (hsInner A B) = hsInner B A := by
  unfold hsInner
  rw [star_div₀, star_natCast, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

theorem hsInner_re_comm {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    (hsInner B A).re = (hsInner A B).re := by
  rw [← hsInner_conj_symm A B]
  simp

/-- Algebraic expansion of the squared Hilbert–Schmidt norm of a difference. -/
theorem hsNormSq_sub_eq {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    hsNormSq (A - B) = hsNormSq A + hsNormSq B - 2 * (hsInner A B).re := by
  have hcross := hsInner_re_comm A B
  unfold hsInner at hcross
  unfold hsNormSq hsInner
  simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
    sub_div, Complex.sub_re]
  rw [hcross]
  ring

/--
If two matrices have squared Hilbert–Schmidt norm at most one, then the usual
unitary distance/correlation identity becomes an inequality.

This is the form needed for compressions of unitaries: the compression need not be
unitary, but it is enough to know its norm is bounded by one.
-/
theorem hsNormSq_sub_le_of_le_one {n : Type*} [Fintype n] (A B : Matrix n n ℂ)
    (hA : hsNormSq A ≤ 1) (hB : hsNormSq B ≤ 1) :
    hsNormSq (A - B) ≤ 2 - 2 * (hsInner A B).re := by
  rw [hsNormSq_sub_eq A B]
  linarith

/-- A unitary matrix has squared normalized Hilbert–Schmidt norm at most one (with
equality as soon as the dimension is positive; the inequality also covers dimension
zero). -/
theorem hsNormSq_le_one_of_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A ∈ Matrix.unitaryGroup n ℂ) :
    hsNormSq A ≤ 1 := by
  have hA' : Aᴴ * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  unfold hsNormSq hsInner
  rw [hA', Matrix.trace_one]
  rcases eq_or_ne ((Fintype.card n : ℂ)) 0 with h | h
  · simp [h]
  · simp [div_self h]

/-- The average of vectors of norm at most one still has norm at most one. -/
theorem norm_average_le_one
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (F : G → E) (hF : ∀ x, ‖F x‖ ≤ 1) :
    ‖(Fintype.card G : ℂ)⁻¹ • ∑ x : G, F x‖ ≤ 1 := by
  have hcard_pos : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcard_ne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hnorm_inv :
      ‖(Fintype.card G : ℂ)⁻¹‖ = (Fintype.card G : ℝ)⁻¹ := by
    simp [norm_inv]
  have hsum_norm : ‖∑ x : G, F x‖ ≤ (Fintype.card G : ℝ) := by
    calc
      ‖∑ x : G, F x‖ ≤ ∑ x : G, ‖F x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : G, (1 : ℝ) := by
        exact Finset.sum_le_sum fun x _ => hF x
      _ = (Fintype.card G : ℝ) := by simp
  calc
    ‖(Fintype.card G : ℂ)⁻¹ • ∑ x : G, F x‖
        ≤ (Fintype.card G : ℝ)⁻¹ * ‖∑ x : G, F x‖ := by
          simpa [hnorm_inv] using
            NormedSpace.norm_smul_le
              (Fintype.card G : ℂ)⁻¹ (∑ x : G, F x)
    _ ≤ (Fintype.card G : ℝ)⁻¹ * (Fintype.card G : ℝ) := by
          exact mul_le_mul_of_nonneg_left hsum_norm
            (inv_nonneg.mpr (le_of_lt hcard_pos))
    _ = 1 := by field_simp [hcard_ne]

/--
The Hilbert–Schmidt unit ball is convex: an average of matrices of squared norm at
most one has squared norm at most one.  The proof equips matrices with the seminorm
induced by the density matrix `|n|⁻¹ • 1`, for which `hsNormSq` is the squared norm,
and applies the triangle inequality.
-/
theorem hsNormSq_average_le_one {n : Type*} [Fintype n] [DecidableEq n]
    (F : G → Matrix n n ℂ)
    (hF : ∀ x, hsNormSq (F x) ≤ 1) :
    hsNormSq ((Fintype.card G : ℂ)⁻¹ • ∑ x : G, F x) ≤ 1 := by
  have hc : (0 : ℂ) ≤ ((Fintype.card n : ℂ))⁻¹ := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg _)
  have hσ₀ : (((Fintype.card n : ℂ))⁻¹ • (1 : Matrix n n ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul hc
  letI : SeminormedAddCommGroup (Matrix n n ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup _ hσ₀
  letI : InnerProductSpace ℂ (Matrix n n ℂ) :=
    Matrix.toMatrixInnerProductSpace _ hσ₀
  have hbridge : ∀ A : Matrix n n ℂ, hsNormSq A = ‖A‖ ^ 2 := by
    intro A
    calc
      hsNormSq A
          = ((A * (((Fintype.card n : ℂ))⁻¹ • (1 : Matrix n n ℂ)) * Aᴴ).trace).re := by
            unfold hsNormSq hsInner
            rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul,
              Matrix.trace_mul_comm]
            congr 1
            rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
      _ = ‖A‖ ^ 2 := by
            rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) A]
            rfl
  have hnormF : ∀ x : G, ‖F x‖ ≤ 1 := by
    intro x
    have hsq : ‖F x‖ ^ 2 ≤ 1 := by
      rw [← hbridge (F x)]
      exact hF x
    nlinarith [norm_nonneg (F x)]
  have havg_norm := norm_average_le_one G F hnormF
  have hsq_avg : ‖((Fintype.card G : ℂ)⁻¹ • ∑ x : G, F x)‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg ((Fintype.card G : ℂ)⁻¹ • ∑ x : G, F x)]
  rw [hbridge ((Fintype.card G : ℂ)⁻¹ • ∑ x : G, F x)]
  exact hsq_avg

/-- Averaging the affine expression `2 - 2 c_x`. -/
theorem average_two_sub_two_mul
    (c : G → ℝ) :
    (∑ x : G, (2 - 2 * c x)) / Fintype.card G =
      2 - 2 * ((∑ x : G, c x) / Fintype.card G) := by
  have hcard_pos : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcard_ne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hcard_pos
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp [hcard_ne]
  simp [Finset.card_univ]
  rw [← Finset.mul_sum]
  ring

/-! ## Approximate representations -/

/--
An `ε`-approximate representation of a finite group `G` (blueprint
`def:approx-rep`) is a function `f : G → U(ℂᵈ)` whose multiplicativity defect,
measured on average in the normalized Hilbert–Schmidt inner product, is at most `ε`:
`𝔼_{x,y ∈ G} Re ⟨f(x) f(y), f(xy)⟩_hs ≥ 1 - ε`.
-/
def IsApproxRepresentation
    (f : G → Matrix (Fin d) (Fin d) ℂ)
    (ε : ℝ) : Prop :=
  (∀ x, f x ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
    (∑ x : G, ∑ y : G,
      (hsInner (f x * f y) (f (x * y))).re) /
      (Fintype.card G ^ 2 : ℝ) ≥ 1 - ε

/-! ## Unitaries and reindexing -/

/-- Column orthogonality for a unitary matrix. -/
theorem unitary_col_sum
    (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (i j : Fin d) :
    (∑ k : Fin d, (starRingEnd ℂ) (A k i) * A k j) =
      (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
  have hmat : Aᴴ * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  have hij := congr_fun (congr_fun hmat i) j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using hij

/-- If `A` and `B` are unitary, then `Aᴴ * B` is unitary. -/
theorem unitary_conjTranspose_mul
    {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    Aᴴ * B ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hAA : Aᴴ * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  have hBB : B * Bᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hB
  have hprod : (Aᴴ * B) * (Bᴴ * A) = 1 := by
    calc
      (Aᴴ * B) * (Bᴴ * A) = Aᴴ * (B * Bᴴ) * A := by
        simp [Matrix.mul_assoc]
      _ = Aᴴ * 1 * A := by rw [hBB]
      _ = 1 := by simpa [Matrix.mul_assoc] using hAA
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose] using hprod

@[simp]
theorem matrix_reindex_one
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n') :
    Matrix.reindex e e (1 : Matrix n n ℂ) = 1 :=
  Matrix.reindexLinearEquiv_one ℂ ℂ e

/-- Reindexing a unitary matrix along an equivalence gives a unitary matrix. -/
noncomputable def reindexUnitary
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n') (U : Matrix.unitaryGroup n ℂ) :
    Matrix.unitaryGroup n' ℂ where
  val := Matrix.reindex e e (U : Matrix n n ℂ)
  property := by
    rw [Matrix.mem_unitaryGroup_iff]
    change Matrix.reindex e e (U : Matrix n n ℂ) *
      (Matrix.reindex e e (U : Matrix n n ℂ))ᴴ = 1
    have hU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp U.property
    calc
      Matrix.reindex e e (U : Matrix n n ℂ) *
          (Matrix.reindex e e (U : Matrix n n ℂ))ᴴ
          = Matrix.reindex e e ((U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ) := by
              rw [Matrix.conjTranspose_reindex]
              exact Matrix.reindexLinearEquiv_mul ℂ ℂ e e e
                (U : Matrix n n ℂ) ((U : Matrix n n ℂ)ᴴ)
      _ = 1 := by
              simp [hU]

@[simp]
theorem reindexUnitary_coe
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n') (U : Matrix.unitaryGroup n ℂ) :
    (reindexUnitary e U : Matrix n' n' ℂ) =
      Matrix.reindex e e (U : Matrix n n ℂ) := rfl

/-- Reindex a unitary representation along an equivalence of index types. -/
noncomputable def reindexUnitaryRep
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n') (ρ₀ : G →* Matrix.unitaryGroup n ℂ) :
    G →* Matrix.unitaryGroup n' ℂ where
  toFun x := reindexUnitary e (ρ₀ x)
  map_one' := by
    apply Subtype.ext
    simp [reindexUnitary]
  map_mul' x y := by
    apply Subtype.ext
    simp [reindexUnitary]

omit [Fintype G] in
@[simp]
theorem reindexUnitaryRep_apply
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n') (ρ₀ : G →* Matrix.unitaryGroup n ℂ) (x : G) :
    (reindexUnitaryRep G e ρ₀ x : Matrix n' n' ℂ) =
      Matrix.reindex e e (ρ₀ x : Matrix n n ℂ) := rfl

/-- Reindexing the enlarged space preserves the compressed operator
`V * R * Vᴴ`. -/
@[simp]
theorem reindex_compression
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n')
    (V : Matrix (Fin d) n ℂ)
    (R : Matrix n n ℂ) :
    Matrix.reindex (Equiv.refl (Fin d)) e V *
      Matrix.reindex e e R *
      (Matrix.reindex (Equiv.refl (Fin d)) e V)ᴴ =
        V * R * Vᴴ := by
  have hVR :
      Matrix.reindex (Equiv.refl (Fin d)) e V * Matrix.reindex e e R =
        Matrix.reindex (Equiv.refl (Fin d)) e (V * R) := by
    exact Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl (Fin d)) e e V R
  have hVRV :
      Matrix.reindex (Equiv.refl (Fin d)) e (V * R) *
          Matrix.reindex e (Equiv.refl (Fin d)) Vᴴ =
        Matrix.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin d)) ((V * R) * Vᴴ) := by
    exact Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl (Fin d)) e
      (Equiv.refl (Fin d)) (V * R) Vᴴ
  calc
    Matrix.reindex (Equiv.refl (Fin d)) e V *
      Matrix.reindex e e R *
      (Matrix.reindex (Equiv.refl (Fin d)) e V)ᴴ
        = Matrix.reindex (Equiv.refl (Fin d)) e (V * R) *
            Matrix.reindex e (Equiv.refl (Fin d)) Vᴴ := by
              rw [Matrix.conjTranspose_reindex, hVR]
    _ = Matrix.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin d)) ((V * R) * Vᴴ) := hVRV
    _ = V * R * Vᴴ := by simp [Matrix.mul_assoc]

/-- Reindexing the enlarged space preserves the isometry equation. -/
theorem reindex_isometry
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n')
    (V : Matrix (Fin d) n ℂ)
    (hV : V * Vᴴ = 1) :
    Matrix.reindex (Equiv.refl (Fin d)) e V *
      (Matrix.reindex (Equiv.refl (Fin d)) e V)ᴴ = 1 := by
  calc
    Matrix.reindex (Equiv.refl (Fin d)) e V *
        (Matrix.reindex (Equiv.refl (Fin d)) e V)ᴴ
        = Matrix.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin d)) (V * Vᴴ) := by
            rw [Matrix.conjTranspose_reindex]
            exact Matrix.reindexLinearEquiv_mul ℂ ℂ
              (Equiv.refl (Fin d)) e (Equiv.refl (Fin d)) V Vᴴ
    _ = 1 := by simp [hV]

/-! ## The regular representation model -/

namespace GowersHatami

/-- Matrix index for the enlarged space `L(G, ℂᵈ)`, identified with
`G × Fin d`. -/
abbrev Index (G : Type*) (d : ℕ) := G × Fin d

/-- The normalization constant `|G|^(-1/2)` for the uniform inner product on
`L(G, ℂᵈ)`. -/
noncomputable def scale (G : Type*) [Fintype G] : ℂ :=
  ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ)

/-- The square of the normalization constant is `1 / |G|`. -/
theorem scale_mul_self (G : Type*) [Fintype G] [Nonempty G] :
    scale G * scale G = (Fintype.card G : ℂ)⁻¹ := by
  have hsqrt_sq :
      (Real.sqrt (Fintype.card G : ℝ) : ℂ) *
        (Real.sqrt (Fintype.card G : ℝ) : ℂ) =
          (Fintype.card G : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq]
    simp [Real.sq_sqrt (Nat.cast_nonneg _)]
  have hprod :
      scale G * scale G * (Fintype.card G : ℂ) = 1 := by
    simp [scale, ← hsqrt_sq, mul_assoc]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← mul_right_inj' hcard]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hprod

/-- The normalization constant is real, hence fixed by complex conjugation. -/
@[simp]
theorem starRingEnd_scale (G : Type*) [Fintype G] :
    (starRingEnd ℂ) (scale G) = scale G := by
  simp [scale]

/--
The isometry `V : ℂᵈ → L(G, ℂᵈ)`, `V u = (x ↦ ρ(x) u)`, stored as the
`d × (G × d)` matrix of its adjoint: the `(i, (x, j))` entry is `|G|^(-1/2)`
times the `(i, j)` entry of `ρ(x)ᴴ`.
-/
noncomputable def embedding
    (ρ : G → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Index G d) ℂ :=
  fun i xj => scale G * (starRingEnd ℂ) (ρ xj.1 xj.2 i)

/-- The right shift `(y, i) ↦ (y * x, i)` on the index of `L(G, ℂᵈ)`; this is
the permutation underlying the right regular representation
`(ρ₀(x) F)(y) = F (y * x)`. -/
def rightShift (x : G) : Equiv.Perm (Index G d) where
  toFun y := (y.1 * x, y.2)
  invFun y := (y.1 * x⁻¹, y.2)
  left_inv y := by simp [mul_assoc]
  right_inv y := by simp [mul_assoc]

/-- The matrix of the right regular representation at `x`, acting on
`L(G, ℂᵈ)`. -/
def rightRegularMatrix [DecidableEq G] (x : G) :
    Matrix (Index G d) (Index G d) ℂ :=
  (rightShift (G := G) (d := d) x).permMatrix ℂ

/-- Right shifts compose contravariantly, as functions act on the right. -/
theorem rightShift_mul
    (G : Type*) [Group G] {d : ℕ} (x y : G) :
    rightShift (G := G) (d := d) (x * y) =
      rightShift (G := G) (d := d) y * rightShift (G := G) (d := d) x := by
  ext a <;> simp [rightShift, mul_assoc]

/-- The right regular matrix is unitary. -/
theorem rightRegularMatrix_unitary [DecidableEq G] (x : G) :
    rightRegularMatrix G x ∈ Matrix.unitaryGroup (Index G d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change (rightShift (G := G) (d := d) x).permMatrix ℂ *
    ((rightShift (G := G) (d := d) x).permMatrix ℂ)ᴴ = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

/-- The identity element acts as the identity matrix. -/
theorem rightRegularMatrix_one
    (G : Type*) [Group G] [DecidableEq G] {d : ℕ} :
    rightRegularMatrix (G := G) (d := d) 1 = 1 := by
  ext y z
  simp [rightRegularMatrix, rightShift, Matrix.one_apply, Prod.ext_iff]

/-- Right regular matrices multiply according to the group multiplication. -/
theorem rightRegularMatrix_mul [DecidableEq G] (x y : G) :
    rightRegularMatrix (G := G) (d := d) (x * y) =
      rightRegularMatrix (G := G) (d := d) x *
        rightRegularMatrix (G := G) (d := d) y := by
  ext a b
  change ((rightShift (G := G) (d := d) (x * y)).permMatrix ℂ) a b =
    ((rightShift (G := G) (d := d) x).permMatrix ℂ *
      (rightShift (G := G) (d := d) y).permMatrix ℂ) a b
  rw [rightShift_mul G x y, Matrix.permMatrix_mul]

/-- The right regular matrix, bundled as a unitary matrix. -/
def rightRegularUnitary [DecidableEq G] (x : G) :
    Matrix.unitaryGroup (Index G d) ℂ :=
  ⟨rightRegularMatrix G x, rightRegularMatrix_unitary G x⟩

/-- The right regular representation of `G` on `L(G, ℂᵈ)`, as a homomorphism
into the unitary group. -/
noncomputable def rightRegular [DecidableEq G] (d : ℕ) :
    G →* Matrix.unitaryGroup (Index G d) ℂ where
  toFun := rightRegularUnitary G
  map_one' := by
    apply Subtype.ext
    exact rightRegularMatrix_one (G := G) (d := d)
  map_mul' x y := by
    apply Subtype.ext
    exact rightRegularMatrix_mul (G := G) (d := d) x y

@[simp]
theorem rightRegular_apply [DecidableEq G] (x : G) :
    (rightRegular G d x :
      Matrix (Index G d) (Index G d) ℂ) =
        rightRegularMatrix G x := rfl

/--
Multiplying on the left by the right regular matrix shifts the row index:
`(R_x M)(y, i) = M(y * x, i)`.
-/
@[simp]
theorem rightRegularMatrix_mul_apply [DecidableEq G]
    (x : G) (M : Matrix (Index G d) (Fin d) ℂ)
    (y : Index G d) (j : Fin d) :
    (rightRegularMatrix (G := G) (d := d) x * M) y j =
      M (y.1 * x, y.2) j := by
  change
    (((rightShift (G := G) (d := d) x).toPEquiv.toMatrix :
        Matrix (Index G d) (Index G d) ℂ) * M) y j =
      M ((rightShift (G := G) (d := d) x) y) j
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rfl

/-- Applying the right regular matrix to `Vᴴ` evaluates `ρ` at the shifted
group element. -/
@[simp]
theorem rightRegularMatrix_mul_embedding_conjTranspose_apply [DecidableEq G]
    (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (x : G) (y : Index G d) (j : Fin d) :
    (rightRegularMatrix (G := G) (d := d) x * (embedding G ρ)ᴴ) y j =
      scale G * ρ (y.1 * x) y.2 j := by
  simp [embedding, Matrix.conjTranspose_apply]

omit [Group G] in
/--
Entrywise expansion of `V * Vᴴ`.  This is the only bookkeeping step in the
isometry proof; `embedding_isometry` then just applies column orthogonality.
-/
theorem embedding_mul_conjTranspose_apply
    (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin d) :
    (embedding G ρ * (embedding G ρ)ᴴ) i j =
      ∑ x : G, scale G * scale G *
        (∑ k : Fin d, (starRingEnd ℂ) (ρ x k i) * ρ x k j) := by
  simp [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- The map `V u = (x ↦ ρ(x) u)` is an isometry. -/
theorem embedding_isometry
    (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (hρ : ∀ x, ρ x ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    embedding G ρ * (embedding G ρ)ᴴ = 1 := by
  ext i j
  calc
    (embedding G ρ * (embedding G ρ)ᴴ) i j
        = ∑ x : G, scale G * scale G *
            (∑ k : Fin d, (starRingEnd ℂ) (ρ x k i) * ρ x k j) := by
            exact embedding_mul_conjTranspose_apply G ρ i j
    _ = ∑ _x : G, scale G * scale G *
          (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
            simp [unitary_col_sum _ (hρ _) i j]
    _ = (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
            simp [scale_mul_self G]

/--
Entrywise expansion of the compression `V * R_x * Vᴴ`.
`compression_eq_average` then packages this expansion as the average from the
proof sketch.
-/
theorem compression_apply
    [DecidableEq G]
    (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (x : G) (i j : Fin d) :
    (embedding G ρ * rightRegularMatrix (G := G) (d := d) x *
        (embedding G ρ)ᴴ) i j =
      ∑ y : G, ∑ k : Fin d, (scale G * scale G) *
        ((starRingEnd ℂ) (ρ y k i) * ρ (y * x) k j) := by
  rw [Matrix.mul_assoc]
  change (∑ a : Index G d,
    embedding G ρ i a *
      (rightRegularMatrix (G := G) (d := d) x *
        (embedding G ρ)ᴴ) a j) =
      ∑ y : G, ∑ k : Fin d, (scale G * scale G) *
        ((starRingEnd ℂ) (ρ y k i) * ρ (y * x) k j)
  simp [embedding,
    Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm]

/--
The compression of the right regular representation by `V` is the average
`𝔼_y ρ(y)ᴴ ρ(y * x)`.
-/
theorem compression_eq_average
    [DecidableEq G]
    (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (x : G) :
    embedding G ρ *
      rightRegularMatrix (G := G) (d := d) x *
      (embedding G ρ)ᴴ =
        (Fintype.card G : ℂ)⁻¹ •
          ∑ y : G, (ρ y)ᴴ * ρ (y * x) := by
  ext i j
  calc
    (embedding G ρ * rightRegularMatrix (G := G) (d := d) x *
        (embedding G ρ)ᴴ) i j
        = ∑ y : G, ∑ k : Fin d, (scale G * scale G) *
            ((starRingEnd ℂ) (ρ y k i) * ρ (y * x) k j) := by
            exact compression_apply G ρ x i j
    _ = (Fintype.card G : ℂ)⁻¹ *
          (∑ y : G, ∑ k : Fin d,
            (starRingEnd ℂ) (ρ y k i) * ρ (y * x) k j) := by
            simp [scale_mul_self G, Finset.mul_sum]
    _ = ((Fintype.card G : ℂ)⁻¹ •
          ∑ y : G, (ρ y)ᴴ * ρ (y * x)) i j := by
            simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
              Matrix.sum_apply, Finset.mul_sum]

/--
Compression of a unitary has squared Hilbert–Schmidt norm at most one.

After rewriting the compression as an average, each summand is a product of
unitaries, hence has norm at most one; the convexity lemma
`hsNormSq_average_le_one` then gives the bound.
-/
theorem compression_hsNormSq_le_one
    [DecidableEq G]
    (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (x : G)
    (hρ : ∀ y, ρ y ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    hsNormSq
      (embedding G ρ *
        rightRegularMatrix (G := G) (d := d) x *
      (embedding G ρ)ᴴ) ≤ 1 := by
  rw [compression_eq_average G ρ x]
  apply hsNormSq_average_le_one G
  intro y
  exact hsNormSq_le_one_of_mem_unitaryGroup
    (unitary_conjTranspose_mul (hρ y) (hρ (y * x)))

/--
Taking the Hilbert–Schmidt inner product against the compressed right regular
action recovers the approximate-representation correlation, averaged over the
auxiliary group element.
-/
theorem hsInner_compression
    [DecidableEq G]
    (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (x : G) :
    hsInner (ρ x)
        (embedding G ρ *
          rightRegularMatrix (G := G) (d := d) x *
          (embedding G ρ)ᴴ) =
      (Fintype.card G : ℂ)⁻¹ *
        ∑ y : G, hsInner (ρ y * ρ x) (ρ (y * x)) := by
  rw [compression_eq_average G ρ x]
  unfold hsInner
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_div_assoc]
  congr 1
  rw [Matrix.mul_sum, Matrix.trace_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/--
The approximate-representation hypothesis gives high average correlation
between `ρ(x)` and the compressed exact representation.
-/
theorem average_correlation
    [DecidableEq G]
    (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (ε : ℝ)
    (hApprox : IsApproxRepresentation G ρ ε) :
    (∑ x : G,
      (hsInner (ρ x)
        (embedding G ρ *
          rightRegularMatrix (G := G) (d := d) x *
          (embedding G ρ)ᴴ)).re) /
      Fintype.card G ≥ 1 - ε := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hmain :
      (∑ x : G,
        (hsInner (ρ x)
          (embedding G ρ *
            rightRegularMatrix (G := G) (d := d) x *
            (embedding G ρ)ᴴ)).re) / Fintype.card G =
        (∑ x : G, ∑ y : G,
          (hsInner (ρ x * ρ y) (ρ (x * y))).re) /
          (Fintype.card G ^ 2 : ℝ) := by
    calc
      (∑ x : G,
        (hsInner (ρ x)
          (embedding G ρ *
            rightRegularMatrix (G := G) (d := d) x *
            (embedding G ρ)ᴴ)).re) / Fintype.card G
          = (∑ x : G,
              ((Fintype.card G : ℂ)⁻¹ *
                ∑ y : G, hsInner (ρ y * ρ x) (ρ (y * x))).re) /
              Fintype.card G := by
              simp [hsInner_compression G ρ]
      _ = (∑ x : G, ∑ y : G,
              (hsInner (ρ y * ρ x) (ρ (y * x))).re) /
              (Fintype.card G ^ 2 : ℝ) := by
              simp [Complex.inv_re, hcard, Finset.mul_sum, div_eq_mul_inv,
                pow_two, mul_left_comm, mul_comm]
      _ = (∑ x : G, ∑ y : G,
              (hsInner (ρ x * ρ y) (ρ (x * y))).re) /
              (Fintype.card G ^ 2 : ℝ) := by
              rw [Finset.sum_comm]
  rcases hApprox with ⟨_, hApprox⟩
  simpa [hmain] using hApprox

/-- Transport a Gowers–Hatami witness along an equivalence of the enlarged
index type. -/
theorem witness_reindex
    {n : Type*} [Fintype n] [DecidableEq n] {d' : ℕ}
    (e : n ≃ Fin d') (hd_le : d ≤ d')
    (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (ε : ℝ)
    (V : Matrix (Fin d) n ℂ)
    (hV : V * Vᴴ = 1)
    (ρ₀ : G →* Matrix.unitaryGroup n ℂ)
    (hprox :
      (∑ x : G,
        hsNormSq
          (ρ x - V * (ρ₀ x : Matrix n n ℂ) * Vᴴ)) /
        Fintype.card G ≤ 2 * ε) :
    ∃ (d' : ℕ) (_ : d ≤ d')
      (V' : Matrix (Fin d) (Fin d') ℂ)
      (_hV' : V' * V'ᴴ = 1)
      (ρ₀' : G →* Matrix.unitaryGroup (Fin d') ℂ),
      (∑ x : G,
        hsNormSq
          (ρ x - V' * (ρ₀' x : Matrix (Fin d') (Fin d') ℂ) * V'ᴴ)) /
        Fintype.card G ≤ 2 * ε := by
  let V' := Matrix.reindex (Equiv.refl (Fin d)) e V
  let ρ₀' := reindexUnitaryRep G e ρ₀
  refine ⟨d', hd_le, V', reindex_isometry e V hV, ρ₀', ?_⟩
  have hsum :
      (∑ x : G,
        hsNormSq
          (ρ x - V' * (ρ₀' x : Matrix (Fin d') (Fin d') ℂ) * V'ᴴ)) =
        ∑ x : G,
          hsNormSq
            (ρ x - V * (ρ₀ x : Matrix n n ℂ) * Vᴴ) := by
    apply Finset.sum_congr rfl
    intro x _
    simp [V', ρ₀']
  rw [hsum]
  exact hprox

end GowersHatami

/-! ## The Gowers–Hatami theorem -/

section Main

open GowersHatami

/--
The Gowers–Hatami theorem in the concrete enlarged space `L(G, ℂᵈ)`.

This is the statement proved directly by the regular representation model:
the exact representation is the right regular representation on `L(G, ℂᵈ)`,
and the isometry is `u ↦ (x ↦ ρ(x) u)`.
-/
theorem gowers_hatami_prod
    [DecidableEq G]
    (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (ε : ℝ)
    (hApprox : IsApproxRepresentation G ρ ε) :
    ∃ (V : Matrix (Fin d) (Index G d) ℂ)
      (_hV : V * Vᴴ = 1)
      (ρ₀ : G →* Matrix.unitaryGroup (Index G d) ℂ),
      (∑ x : G,
        hsNormSq
          (ρ x -
            V * (ρ₀ x : Matrix (Index G d) (Index G d) ℂ) * Vᴴ)) /
        Fintype.card G ≤ 2 * ε := by
  have hρ := hApprox.1
  refine ⟨embedding G ρ, embedding_isometry G ρ hρ,
    rightRegular G d, ?_⟩
  simp only [rightRegular_apply]
  have hcorr := average_correlation G ρ ε hApprox
  let comp : G → Matrix (Fin d) (Fin d) ℂ := fun x =>
    embedding G ρ *
      rightRegularMatrix (G := G) (d := d) x *
      (embedding G ρ)ᴴ
  have hpoint :
      ∀ x : G,
        hsNormSq (ρ x - comp x) ≤
          2 - 2 * (hsInner (ρ x) (comp x)).re := by
    intro x
    exact hsNormSq_sub_le_of_le_one (ρ x) (comp x)
      (hsNormSq_le_one_of_mem_unitaryGroup (hρ x))
      (compression_hsNormSq_le_one G ρ x hρ)
  have hsum :
      (∑ x : G, hsNormSq (ρ x - comp x)) ≤
        ∑ x : G, (2 - 2 * (hsInner (ρ x) (comp x)).re) := by
    exact Finset.sum_le_sum fun x _ => hpoint x
  have hcard_pos : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcard_ne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hcorr' :
      ((∑ x : G, (hsInner (ρ x) (comp x)).re) / Fintype.card G) ≥
        1 - ε := by
    simpa [comp] using hcorr
  calc
    (∑ x : G, hsNormSq (ρ x - comp x)) / Fintype.card G
        ≤ (∑ x : G, (2 - 2 * (hsInner (ρ x) (comp x)).re)) /
            Fintype.card G := by
          exact div_le_div_of_nonneg_right hsum (le_of_lt hcard_pos)
    _ = 2 - 2 *
          ((∑ x : G, (hsInner (ρ x) (comp x)).re) / Fintype.card G) := by
          exact average_two_sub_two_mul G
            (fun x : G => (hsInner (ρ x) (comp x)).re)
    _ ≤ 2 * ε := by
          linarith

/--
**The Gowers–Hatami theorem** (blueprint `thm:gowers-hatami`).  Let `G` be a
finite group and `ρ : G → U(ℂᵈ)` an `ε`-approximate representation of `G`.
Then there are a dimension `d' ≥ d`, an isometry `V` (given as a `d × d'`
matrix with `V * Vᴴ = 1`), and an exact representation `ρ₀ : G →* U(ℂ^d')`
such that `𝔼_x ‖ρ(x) - V ρ₀(x) Vᴴ‖²_hs ≤ 2ε`.

The witness is the right regular representation on `L(G, ℂᵈ)`, reindexed to
`Fin d'` with `d' = |G| * d`.
-/
theorem gowers_hatami
    (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (ε : ℝ)
    (hApprox : IsApproxRepresentation G ρ ε) :
    ∃ (d' : ℕ) (_ : d ≤ d')
      (V : Matrix (Fin d) (Fin d') ℂ)
      (_hV : V * Vᴴ = 1)
      (ρ₀ : G →* Matrix.unitaryGroup (Fin d') ℂ),
      (∑ x : G,
        hsNormSq
          (ρ x - V * (ρ₀ x : Matrix (Fin d') (Fin d') ℂ) * Vᴴ)) /
        Fintype.card G ≤ 2 * ε := by
  classical
  obtain ⟨V, hV, ρ₀, hprox⟩ :=
    gowers_hatami_prod G ρ ε hApprox
  let d' := Fintype.card G * d
  let e : Index G d ≃ Fin d' :=
    (Equiv.prodCongr (Fintype.equivFin G) (Equiv.refl (Fin d))).trans
      finProdFinEquiv
  have hd_le : d ≤ d' := by
    exact Nat.le_mul_of_pos_left d Fintype.card_pos
  exact witness_reindex G e hd_le ρ ε V hV ρ₀ hprox

end Main

end MIPRE
