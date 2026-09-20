/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryPolynomial
import Mathlib.Data.Matrix.Mul
import MIPRE.Foundations.SAT.ArrayProg

/-! # Executable binary vector and matrix arithmetic -/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun

/-- Canonical binary scalar coordinates. -/
def bit (x : ZMod 2) : Bool := decide (x = 1)

@[simp] theorem ofBool_bit (x : ZMod 2) : ofBool (bit x) = x := by
  revert x
  decide

@[simp] theorem bit_ofBool (x : Bool) : bit (ofBool x) = x := by cases x <;> decide

theorem ofBool_injective : Function.Injective (ofBool : Bool → ZMod 2) := by
  intro a b h
  have := congrArg bit h
  simpa using this

theorem ofBool_xor (a b : Bool) :
    (ofBool (a ^^ b) : ZMod 2) = ofBool a + ofBool b := by
  cases a <;> cases b <;> decide

theorem ofBool_and (a b : Bool) :
    (ofBool (a && b) : ZMod 2) = ofBool a * ofBool b := by
  cases a <;> cases b <;> decide

def vectorBits {n : ℕ} (v : Fin n → ZMod 2) : BitStr := List.ofFn (fun i => bit (v i))

def matrixBits {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) : List BitStr :=
  List.ofFn (fun i => vectorBits (A i))

def dotStep (b : Bool) (p : Bool × Bool) : Bool := b ^^ (p.1 && p.2)

def dotBits (a b : BitStr) : Bool := (a.zip b).foldl dotStep false

theorem ofBool_fold_dotStep (l : List (Bool × Bool)) (b : Bool) :
    (ofBool (l.foldl dotStep b) : ZMod 2) =
      ofBool b + (l.map (fun p => (ofBool p.1 : ZMod 2) * ofBool p.2)).sum := by
  induction l generalizing b with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    simp only [dotStep, ofBool_xor, ofBool_and, List.map_cons, List.sum_cons]
    ring

theorem ofBool_dotBits (a b : BitStr) :
    (ofBool (dotBits a b) : ZMod 2) =
      ((a.zip b).map (fun p => (ofBool p.1 : ZMod 2) * ofBool p.2)).sum := by
  rw [dotBits, ofBool_fold_dotStep]
  simp [ofBool]

theorem zip_vectorBits {n : ℕ} (v w : Fin n → ZMod 2) :
    (vectorBits v).zip (vectorBits w) = List.ofFn (fun i => (bit (v i), bit (w i))) := by
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    simp [vectorBits]

/-- The raw parity circuit computes the exact binary dot product. -/
theorem dotBits_vectorBits {n : ℕ} (v w : Fin n → ZMod 2) :
    dotBits (vectorBits v) (vectorBits w) = bit (∑ i, v i * w i) := by
  apply ofBool_injective
  rw [ofBool_dotBits, zip_vectorBits, ofBool_bit]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, ofBool_bit]

/-- A matrix is represented by its rows. -/
def applyBits (A : List BitStr) (v : BitStr) : BitStr := A.map (fun r => dotBits r v)

/-- Executable matrix application agrees with the usual binary matrix-vector product. -/
theorem applyBits_matrixBits {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) :
    applyBits (matrixBits A) (vectorBits v) = vectorBits (A.mulVec v) := by
  simp only [applyBits, matrixBits, List.map_ofFn, vectorBits]
  apply congrArg List.ofFn
  funext i
  exact dotBits_vectorBits (A i) v

private noncomputable def dotStepProg : PolyTimeFun (Bool × Bool × Bool) Bool :=
  let t := ite (fst.comp snd) (snd.comp snd) (const false)
  congr (ite fst (ite t (const false) (const true)) t)
    (fun p => dotStep p.1 p.2) (by
      rintro ⟨b, c, d⟩
      cases b <;> cases c <;> cases d <;> rfl)

/-- The parity dot product is one uniform ambient program. -/
noncomputable def dotBitsProg : PolyTimeFun (BitStr × BitStr) Bool :=
  let scan := foldlAdd dotStepProg 3 (by
    intro s a
    have hb : esize (dotStepProg (s, a)) ≤ 3 := by
      generalize dotStepProg (s, a) = b
      cases b <;> decide
    simp only [Polynomial.eval_ofNat]
    omega)
  congr (scan.comp (zip.pair (const false))) (fun p => dotBits p.1 p.2)
    (by intro p; rfl)

@[simp] theorem dotBitsProg_apply (a b : BitStr) : dotBitsProg (a, b) = dotBits a b := rfl

/-- Binary matrix application is polynomial-time on arbitrary raw row lists. -/
noncomputable def applyBitsProg : PolyTimeFun (List BitStr × BitStr) BitStr :=
  congr (mapWith dotBitsProg) (fun p => applyBits p.1 p.2) (by intro p; rfl)

@[simp] theorem applyBitsProg_apply (A : List BitStr) (v : BitStr) :
    applyBitsProg (A, v) = applyBits A v := rfl


/-- Coordinatewise XOR computes binary vector addition. -/
theorem xorBits_vectorBits {n : ℕ} (v w : Fin n → ZMod 2) :
    BinaryPolynomial.xorBits (vectorBits v) (vectorBits w) = vectorBits (v + w) := by
  apply List.ext_getElem
  · simp [BinaryPolynomial.xorBits, vectorBits]
  · intro i hi hj
    simp only [BinaryPolynomial.xorBits, vectorBits, List.getElem_zipWith, List.getElem_ofFn]
    apply ofBool_injective
    simp [ofBool_xor]

/-- The number of columns is explicit; short raw rows are padded with zero. -/
def transposeBits (n : ℕ) (A : List BitStr) : List BitStr :=
  (List.range n).map (fun j => A.map (fun r => r.getD j false))

/-- Raw transposition agrees with typed matrix transposition. -/
theorem transposeBits_matrixBits {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    transposeBits n (matrixBits A) = matrixBits A.transpose := by
  apply List.ext_getElem
  · simp [transposeBits, matrixBits]
  · intro j hj hj'
    have hjn : j < n := by simpa [transposeBits] using hj
    simp only [transposeBits, List.getElem_map, List.getElem_range, matrixBits,
      List.getElem_ofFn]
    apply List.ext_getElem
    · simp [vectorBits]
    · intro i hi hi'
      have him : i < m := by simpa using hi
      simp [vectorBits, List.getD_eq_getElem?_getD, hjn, him]

/-- A rectangular matrix product with an explicit output width. -/
def mulBits (n : ℕ) (A B : List BitStr) : List BitStr :=
  A.map (fun r => applyBits (transposeBits n B) r)

/-- The executable matrix product is the ordinary product over the binary field. -/
theorem mulBits_matrixBits {m n r : ℕ}
    (A : Matrix (Fin m) (Fin r) (ZMod 2)) (B : Matrix (Fin r) (Fin n) (ZMod 2)) :
    mulBits n (matrixBits A) (matrixBits B) = matrixBits (A * B) := by
  rw [mulBits, transposeBits_matrixBits]
  simp only [matrixBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change applyBits (matrixBits B.transpose) (vectorBits (A i)) = vectorBits ((A * B) i)
  rw [applyBits_matrixBits]
  congr 1
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

private noncomputable def columnProg : PolyTimeFun (ℕ × List BitStr) BitStr :=
  (mapWith ((SAT.ArrayProg.getD false).comp (snd.pair fst))).comp (snd.pair fst)

/-- Transposition is polynomial-time in the rows and the unary column count. -/
noncomputable def transposeBitsProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  congr ((mapWith columnProg).comp
    ((SAT.range'P.comp ((const 0).pair fst)).pair snd))
    (fun p => transposeBits p.1.length p.2) (by
      intro p
      simp only [comp_apply, mapWith_apply, pair_apply, fst_apply, snd_apply,
        SAT.range'P_apply, const_apply]
      change (List.range' 0 p.1.length).map (fun j => p.2.map (fun r => r.getD j false)) = _
      rw [← List.range_eq_range']
      rfl)

@[simp] theorem transposeBitsProg_apply (u : Unary) (A : List BitStr) :
    transposeBitsProg (u, A) = transposeBits u.length A := rfl

/-- Matrix multiplication is globally polynomial-time in its raw inputs. -/
noncomputable def mulBitsProg :
    PolyTimeFun (Unary × List BitStr × List BitStr) (List BitStr) :=
  congr ((mapWith (applyBitsProg.comp (snd.pair fst))).comp
    ((fst.comp snd).pair (transposeBitsProg.comp (fst.pair (snd.comp snd)))))
    (fun p => mulBits p.1.length p.2.1 p.2.2) (by intro p; rfl)

@[simp] theorem mulBitsProg_apply (u : Unary) (A B : List BitStr) :
    mulBitsProg (u, A, B) = mulBits u.length A B := rfl

end MIPRE.LowDegree.BinaryLinear

