/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryLinear

/-!
# Binary elimination with coefficient certificates

Each row carries both its vector and a coefficient vector describing that vector
in the original generating family. Reduction XORs both components together.
The program is uniformly polynomial-time even for malformed pivots and rows.
-/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun Polynomial

abbrev RawRow := BitStr × BitStr
abbrev RawPivot := ℕ × RawRow

def reduceStep (r : RawRow) (b : RawPivot) : RawRow :=
  if r.1.getD b.1 false then
    (BinaryPolynomial.xorBits r.1 b.2.1, BinaryPolynomial.xorBits r.2 b.2.2)
  else r

def reduceRows (b : List RawPivot) (r : RawRow) : RawRow := b.foldl reduceStep r

theorem reduceStep_width (r : RawRow) (b : RawPivot) :
    (reduceStep r b).1.length ≤ r.1.length ∧
    (reduceStep r b).2.length ≤ r.2.length := by
  unfold reduceStep
  split
  · simp only [BinaryPolynomial.length_xorBits]
    exact ⟨min_le_left _ _, min_le_left _ _⟩
  · exact ⟨le_rfl, le_rfl⟩

theorem reduceRows_width (b : List RawPivot) (r : RawRow) :
    (reduceRows b r).1.length ≤ r.1.length ∧
    (reduceRows b r).2.length ≤ r.2.length := by
  induction b generalizing r with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons p b ih =>
    obtain ⟨h₁, h₂⟩ := ih (reduceStep r p)
    obtain ⟨h₁', h₂'⟩ := reduceStep_width r p
    exact ⟨h₁.trans h₁', h₂.trans h₂'⟩

abbrev Row (n t : ℕ) := (Fin n → ZMod 2) × (Fin t → ZMod 2)
abbrev Pivot (n t : ℕ) := Fin n × Row n t

def rowBits {n t : ℕ} (r : Row n t) : RawRow := (vectorBits r.1, vectorBits r.2)

def pivotBits {n t : ℕ} (p : Pivot n t) : RawPivot := (p.1, rowBits p.2)

def typedReduceStep {n t : ℕ} (r : Row n t) (p : Pivot n t) : Row n t :=
  if r.1 p.1 = 1 then (r.1 + p.2.1, r.2 + p.2.2) else r

def typedReduce {n t : ℕ} (b : List (Pivot n t)) (r : Row n t) : Row n t :=
  b.foldl typedReduceStep r

theorem getD_vectorBits {n : ℕ} (v : Fin n → ZMod 2) (j : Fin n) :
    (vectorBits v).getD j false = bit (v j) := by
  simp [vectorBits]

/-- A raw XOR step is the corresponding operation on both typed vectors. -/
theorem reduceStep_rowBits {n t : ℕ} (r : Row n t) (p : Pivot n t) :
    reduceStep (rowBits r) (pivotBits p) = rowBits (typedReduceStep r p) := by
  unfold reduceStep pivotBits rowBits
  rw [getD_vectorBits]
  simp only [bit, decide_eq_true_eq, typedReduceStep]
  split_ifs
  · rw [xorBits_vectorBits, xorBits_vectorBits]
  · rfl

/-- The entire executable reduction agrees with typed binary elimination. -/
theorem reduceRows_rowBits {n t : ℕ} (b : List (Pivot n t)) (r : Row n t) :
    reduceRows (b.map pivotBits) (rowBits r) = rowBits (typedReduce b r) := by
  induction b generalizing r with
  | nil => rfl
  | cons p b ih =>
    change reduceRows (b.map pivotBits) (reduceStep (rowBits r) (pivotBits p)) = _
    rw [reduceStep_rowBits, ih]
    rfl

/-- A row carries a valid expression in a fixed original generating family. -/
def Represents {n t : ℕ} (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (r : Row n t) : Prop := L r.2 = r.1

theorem represents_typedReduceStep {n t : ℕ}
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (r : Row n t) (p : Pivot n t) (hr : Represents L r) (hp : Represents L p.2) :
    Represents L (typedReduceStep r p) := by
  unfold typedReduceStep
  split
  · change L (r.2 + p.2.2) = r.1 + p.2.1
    rw [map_add, hr, hp]
  · exact hr

/-- Reduction preserves the coefficient certificate in the original family. -/
theorem represents_typedReduce {n t : ℕ}
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t) (hr : Represents L r)
    (hb : ∀ p ∈ b, Represents L p.2) : Represents L (typedReduce b r) := by
  induction b generalizing r with
  | nil => exact hr
  | cons p b ih =>
    exact ih _ (represents_typedReduceStep L r p hr (hb p (by simp)))
      (fun q hq => hb q (by simp [hq]))

/-- A zero remainder's certificate is a vector in the kernel of the original map. -/
theorem typedReduce_certificate_mem_ker {n t : ℕ}
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t) (hr : Represents L r)
    (hb : ∀ p ∈ b, Represents L p.2) (hzero : (typedReduce b r).1 = 0) :
    (typedReduce b r).2 ∈ L.ker := by
  rw [LinearMap.mem_ker, represents_typedReduce L b r hr hb, hzero]

private noncomputable def reduceStepProg : PolyTimeFun (RawRow × RawPivot) RawRow :=
  let pivot := fst.comp snd
  let v := fst.comp fst
  let w := snd.comp fst
  let bv := fst.comp (snd.comp snd)
  let bw := snd.comp (snd.comp snd)
  congr (ite ((SAT.ArrayProg.getD false).comp (pivot.pair v))
    ((BinaryPolynomial.xorBitsProg.comp (v.pair bv)).pair
      (BinaryPolynomial.xorBitsProg.comp (w.pair bw))) fst)
    (fun p => reduceStep p.1 p.2) (by intro p; rfl)

private theorem reduceStep_bounded : FoldBounded reduceStepProg (5 * X + 5) := by
  intro l r pre post _
  change esize (reduceRows pre r) ≤ _
  obtain ⟨hv, hw⟩ := reduceRows_width pre r
  have hv0 := length_le_esize_list r.1
  have hw0 := length_le_esize_list r.2
  have hsv := esize_bitStr_le (reduceRows pre r).1
  have hsw := esize_bitStr_le (reduceRows pre r).2
  have hs : esize r = esize r.1 + esize r.2 + 1 := rfl
  rw [esize_prod]
  grw [hsv, hsw, hv, hw, hv0, hw0]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, esize_prod]
  omega

/-- Uniform, certificate-preserving binary elimination along a supplied pivot list. -/
noncomputable def reduceRowsProg : PolyTimeFun (List RawPivot × RawRow) RawRow :=
  congr (foldl reduceStepProg (5 * X + 5) reduceStep_bounded)
    (fun p => reduceRows p.1 p.2) (by intro p; rfl)

@[simp] theorem reduceRowsProg_apply (b : List RawPivot) (r : RawRow) :
    reduceRowsProg (b, r) = reduceRows b r := rfl

end MIPRE.LowDegree.BinaryLinear
