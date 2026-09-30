/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.HalmosDilation
public import MIPRE.Foundations.Pasting

@[expose] public section

/-!
# Projective dilation against a fixed state, in any star-ordered ring

Introspection's adaptive inductions dilate a family of positive operator valued measures to
projective ones against **one fixed ancilla state**, common to the whole family: the matrix proof
uses `exists_projective_dilation` (`MIPRE/Foundations/Dilation.lean`), a unitary extension in
finite dimension. Phase 4 of `planning/mipco-track.md` needs the same in a player's algebra of a
bipartite model, where there is neither finite dimension nor, in general, a square root.

Neither is needed. In a star-ordered ring a nonnegative element is a finite sum `∑ Zᵢᴴ Zᵢ`
(`exists_sum_star_mul_self`), so each element of a POVM `Q` is `∑ᵢ Z_{a,i}ᴴ Z_{a,i}`, and the
whole POVM is the Kraus family `(Z_{a,i})_{a,i}` with `∑_{a,i} Z_{a,i}ᴴ Z_{a,i} = 1`. The Halmos
unitary of its Naimark matrix (`MIPRE/Foundations/HalmosDilation.lean`) dilates it to projections
`proj w (a, i)`, which form a projective measurement (`Halmos.isPVMIn_proj`); coarse-grained over
`i`, they compress at the fixed basis vector `e_{inl (a₀, 0)}` to `Q a`
(`exists_pvm_dilation`). The number of terms is padded to a common bound, so that one ancilla,
`DilationAncilla A K`, serves a whole finite family of POVMs.
-/

namespace MIPRE

open Finset Matrix

/-! ## Finite sums of squares -/

section Squares

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- **A nonnegative element of a star-ordered ring is a finite sum of squares `Zᴴ Z`.** -/
theorem exists_sum_star_mul_self {x : R} (hx : 0 ≤ x) :
    ∃ (k : ℕ) (Z : Fin k → R), x = ∑ i, star (Z i) * Z i := by
  rw [StarOrderedRing.nonneg_iff] at hx
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy =>
    obtain ⟨z, rfl⟩ := hy
    exact ⟨1, fun _ => z, by simp⟩
  | zero => exact ⟨0, Fin.elim0, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨k, Z, rfl⟩ := hy
    obtain ⟨k', Z', rfl⟩ := hy'
    exact ⟨k + k', Fin.append Z Z', by rw [Fin.sum_univ_add]; simp [Fin.append_left,
      Fin.append_right]⟩

omit [PartialOrder R] [StarOrderedRing R] in
/-- A finite sum of squares, padded by zeros to any longer length. -/
theorem sum_star_mul_self_pad {k K : ℕ} (hk : k ≤ K) (Z : Fin k → R) :
    ∑ i : Fin K, star (if h : i.val < k then Z ⟨i.val, h⟩ else 0) *
        (if h : i.val < k then Z ⟨i.val, h⟩ else 0) = ∑ i, star (Z i) * Z i := by
  let z : ℕ → R := fun n => if h : n < k then Z ⟨n, h⟩ else 0
  have h1 : ∑ i : Fin K, star (z i) * z i = ∑ n ∈ range K, star (z n) * z n :=
    Fin.sum_univ_eq_sum_range (fun n => star (z n) * z n) K
  have h2 : ∑ n ∈ range K, star (z n) * z n = ∑ n ∈ range k, star (z n) * z n := by
    refine (Finset.sum_subset (Finset.range_subset_range.mpr hk) fun n hn hnk => ?_).symm
    have : ¬ n < k := fun h => hnk (Finset.mem_range.mpr h)
    simp [z, this]
  have h3 : ∑ n ∈ range k, star (z n) * z n = ∑ i : Fin k, star (z i) * z i :=
    (Fin.sum_univ_eq_sum_range (fun n => star (z n) * z n) k).symm
  have h4 : ∑ i : Fin k, star (z i) * z i = ∑ i, star (Z i) * Z i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [z, i.isLt]
  exact h1.trans (h2.trans (h3.trans h4))

end Squares

/-! ## The dilated projections form a projective measurement -/

namespace Halmos

variable {m : Type*} [Fintype m] [DecidableEq m] {R : Type*} [Ring R] [StarRing R]

omit [StarRing R] in
theorem coordProj_mul_coordProj {a b : m} (hab : a ≠ b) :
    (coordProj a : Matrix (m ⊕ m) (m ⊕ m) R) * coordProj b = 0 := by
  rw [coordProj, coordProj, diagonal_mul_diagonal]
  ext k l
  rw [diagonal_apply, Matrix.zero_apply]
  split_ifs with h1 h2 <;> simp_all

/-- **The dilated projections of a partial isometry form a projective measurement.** -/
theorem isPVMIn_proj {w : Matrix m m R} (hw : w * wᴴ * w = w) : IsPVMIn (proj w) where
  star_eq a := (isStarProjection_proj hw a).isSelfAdjoint
  idem a := (isStarProjection_proj hw a).isIdempotentElem
  sum_eq_one := sum_proj hw
  orthogonal {a b} hab := by
    rw [proj, proj]
    calc (extension w)ᴴ * coordProj a * extension w * ((extension w)ᴴ * coordProj b * extension w)
        = (extension w)ᴴ * coordProj a * (extension w * (extension w)ᴴ) * coordProj b *
            extension w := by simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [extension_mul_conjTranspose hw, Matrix.mul_one, Matrix.mul_assoc
            ((extension w)ᴴ), coordProj_mul_coordProj hab, Matrix.mul_zero, Matrix.zero_mul]

end Halmos

/-! ## Dilation of a family of POVMs against one fixed state -/

/-- The ancilla of the fixed-state dilation of POVMs with outcomes `A`, padded to `K + 1` terms:
two copies of `A × Fin (K + 1)`. -/
abbrev DilationAncilla (A : Type*) (K : ℕ) := (A × Fin (K + 1)) ⊕ (A × Fin (K + 1))

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
  {Y A : Type*} [Fintype Y] [Fintype A] [DecidableEq A]

/-- **Fixed-state dilation with any large enough padding**: the dilation of
`exists_pvm_dilation` exists on `DilationAncilla A K` for every `K` beyond a threshold, so that
finitely many families, even in different rings, can share one ancilla. -/
theorem exists_pvm_dilation_ge (Q : Y → POVMIn A R) (a₀ : A) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K → ∃ P : Y → A → Matrix (DilationAncilla A K) (DilationAncilla A K) R,
      (∀ y, IsPVMIn (P y)) ∧ ∀ y a, P y a (Sum.inl (a₀, 0)) (Sum.inl (a₀, 0)) = (Q y).op a := by
  classical
  choose k Z hZ using fun (p : Y × A) => exists_sum_star_mul_self ((Q p.1).op_nonneg p.2)
  refine ⟨Finset.univ.sup fun p : Y × A => k p, fun K hK => ?_⟩
  have hk p : k p ≤ K + 1 :=
    ((Finset.le_sup (f := fun p : Y × A => k p) (mem_univ p)).trans hK).trans (Nat.le_succ K)
  let z : Y → A × Fin (K + 1) → R := fun y q =>
    if h : q.2.val < k (y, q.1) then Z (y, q.1) ⟨q.2.val, h⟩ else 0
  have hrow y a : ∑ i : Fin (K + 1), star (z y (a, i)) * z y (a, i) = (Q y).op a := by
    rw [hZ (y, a)]
    exact sum_star_mul_self_pad (hk (y, a)) (Z (y, a))
  have hsum y : ∑ q, star (z y q) * z y q = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [hrow y]
    exact (Q y).sum_op
  have hw y : Halmos.naimark (z y) (a₀, 0) * (Halmos.naimark (z y) (a₀, 0))ᴴ *
      Halmos.naimark (z y) (a₀, 0) = Halmos.naimark (z y) (a₀, 0) :=
    Halmos.naimark_mul_conjTranspose_mul' (hsum y) _
  have hcomp y a : (∑ c ∈ univ.filter (fun c : A × Fin (K + 1) => c.1 = a),
      Halmos.proj (Halmos.naimark (z y) (a₀, 0)) c) (Sum.inl (a₀, 0)) (Sum.inl (a₀, 0)) =
      (Q y).op a := by
    rw [Matrix.sum_apply]
    simp_rw [Halmos.proj_naimark_inl_inl' (hsum y)]
    rw [← hrow y a, Finset.sum_filter, Fintype.sum_prod_type]
    refine (Finset.sum_eq_single a (fun b _ hb => ?_) (fun h => absurd (mem_univ a) h)).trans ?_
    · exact Finset.sum_eq_zero fun i _ => ite_eq_right hb
    · exact Finset.sum_congr rfl fun i _ => ite_eq_left rfl
  exact ⟨fun y => fibSumIn (Halmos.proj (Halmos.naimark (z y) (a₀, 0))) Prod.fst, fun y =>
    isPVMIn_fibSumIn (Halmos.isPVMIn_proj (hw y)) Prod.fst, hcomp⟩

/-- **Every finite family of POVMs in a star-ordered ring dilates to projective measurements
against one fixed basis vector**: projective `P y` on the ancilla `DilationAncilla A K`, whose
`(inl (a₀, 0), inl (a₀, 0))` entry is `Q y`. -/
theorem exists_pvm_dilation (Q : Y → POVMIn A R) (a₀ : A) :
    ∃ K : ℕ, ∃ P : Y → A → Matrix (DilationAncilla A K) (DilationAncilla A K) R,
      (∀ y, IsPVMIn (P y)) ∧ ∀ y a, P y a (Sum.inl (a₀, 0)) (Sum.inl (a₀, 0)) = (Q y).op a := by
  obtain ⟨K₀, h⟩ := exists_pvm_dilation_ge Q a₀
  exact ⟨K₀, h K₀ le_rfl⟩

end MIPRE

end
