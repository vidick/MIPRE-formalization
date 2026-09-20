/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.NormalElement
import MIPRE.Foundations.SAT.FrobeniusActionProg
import MIPRE.Foundations.LowDegree.BinaryFold

/-! # A polynomial-time constructor of a normal basis -/

noncomputable section

namespace MIPRE.SAT

open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def shoupZeroProg : PolyTimeFun Unary BitStr := map (const false)

theorem shoupZeroProg_correct (k : ℕ) (hk : 1 ≤ k) :
    shoupZeroProg (unary k) = (shoupBinField k hk).toBits 0 := by
  rw [← shoupCoordinateEquiv_encoding, map_zero]
  change (unary k).map (fun _ => false) = vectorBits (0 : Fin k → ZMod 2)
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    simp [vectorBits, bit]

theorem shoupNonzeroRow_correct (k : ℕ) (hk : 1 ≤ k) (a : (shoupBinField k hk).carrier) :
    nonzeroRow ((shoupBinField k hk).toBits a) = decide (a ≠ 0) := by
  rw [← shoupCoordinateEquiv_encoding]
  unfold nonzeroRow
  rw [zeroRow_vectorBits, ← (shoupCoordinateEquiv k hk).map_zero]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact not_congr ((vectorBits_injective (k := k)).eq_iff.trans
    (shoupCoordinateEquiv k hk).injective.eq_iff)

theorem shoupXorBits_correct (k : ℕ) (hk : 1 ≤ k) (a b : (shoupBinField k hk).carrier) :
    BinaryPolynomial.xorBits ((shoupBinField k hk).toBits a) ((shoupBinField k hk).toBits b) =
      (shoupBinField k hk).toBits (a + b) := by
  simp only [← shoupCoordinateEquiv_encoding, xorBits_vectorBits, map_add]

def selectNonzeroStep : PolyTimeFun (BitStr × BitStr) BitStr :=
  ite (nonzeroRowProg.comp snd) snd fst

/-- Scan right to left, retaining each nonzero row; the result is the first such row. -/
def firstNonzeroBitsProg : PolyTimeFun (List BitStr × BitStr) BitStr :=
  congr ((foldlAdd selectNonzeroStep X (by
    intro s a
    change esize (if nonzeroRow a then a else s) ≤ esize s + X.eval (esize a)
    rw [eval_X]
    split <;> omega)).comp ((PolyTimeFun.reverse.comp fst).pair snd))
    (fun p => p.1.foldr (fun a s => if nonzeroRow a then a else s) p.2) (by
      intro p
      change p.1.reverse.foldl (fun s a => if nonzeroRow a then a else s) p.2 = _
      exact List.foldr_eq_foldl_reverse.symm)

theorem firstNonzeroBitsProg_correct (k : ℕ) (hk : 1 ≤ k)
    (l : List (shoupBinField k hk).carrier) :
    firstNonzeroBitsProg (l.map (shoupBinField k hk).toBits, (shoupBinField k hk).toBits 0) =
      (shoupBinField k hk).toBits (firstNonzero l) := by
  change (l.map (shoupBinField k hk).toBits).foldr
    (fun a s => if nonzeroRow a then a else s) _ = _
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.foldr_cons, shoupNonzeroRow_correct, ih]
    by_cases ha : a = 0 <;> simp [ha, firstNonzero]

/-- Apply the supplied projection to each vector of the polynomial basis. -/
def shoupProjectionImagesProg : PolyTimeFun (Unary × BitStr) (List BitStr) :=
  (mapWith (shoupActionProg.comp ((fst.comp snd).pair ((snd.comp snd).pair fst)))).comp
    ((identityBitsProg.comp fst).pair (PolyTimeFun.id _))

theorem shoupProjectionImagesProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (e : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    shoupProjectionImagesProg (unary k, vectorBits (groupCoordinates k e)) =
      List.ofFn (fun j => (shoupBinField k hk).toBits
        (shoupFrobeniusAction k hk e (shoupPowerBasis k hk j))) := by
  have hu : identityBits k = List.ofFn (fun j => (shoupBinField k hk).toBits (shoupPowerBasis k hk j)) := by
    apply List.ext_getElem
    · simp [identityBits]
    · intro j hj hj'
      have hjk : j < k := by simpa [identityBits] using hj
      simp only [identityBits, List.getElem_map, List.getElem_range, List.getElem_ofFn]
      exact (shoupPowerBasis_encoding k hk (⟨j, hjk⟩ : Fin k)).symm
  change (identityBits (unary k).length).map
    (fun a => shoupActionProg (unary k, vectorBits (groupCoordinates k e), a)) = _
  rw [length_unary, hu, List.map_ofFn]
  congr 1
  funext j
  exact shoupActionProg_correct k hk e _

def shoupProjectedVectorProg : PolyTimeFun (Unary × BitStr) BitStr :=
  firstNonzeroBitsProg.comp (shoupProjectionImagesProg.pair (shoupZeroProg.comp fst))

theorem shoupProjectedVectorProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (e : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    shoupProjectedVectorProg (unary k, vectorBits (groupCoordinates k e)) =
      (shoupBinField k hk).toBits (shoupProjectedVector k hk e) := by
  change firstNonzeroBitsProg
    (shoupProjectionImagesProg (unary k, vectorBits (groupCoordinates k e)),
      shoupZeroProg (unary k)) = _
  rw [shoupProjectionImagesProg_correct k hk, shoupZeroProg_correct k hk]
  rw [show List.ofFn (fun j => (shoupBinField k hk).toBits
      (shoupFrobeniusAction k hk e (shoupPowerBasis k hk j))) =
    (List.ofFn (fun j => shoupFrobeniusAction k hk e (shoupPowerBasis k hk j))).map
      (shoupBinField k hk).toBits by rw [List.map_ofFn]; rfl]
  exact firstNonzeroBitsProg_correct k hk _

theorem shoupArithmeticFold_add_correct (k : ℕ) (hk : 1 ≤ k)
    (l : List (shoupBinField k hk).carrier) (a : (shoupBinField k hk).carrier) (p : BitStr) :
    BinaryPolynomial.arithmeticFold false p ((shoupBinField k hk).toBits a)
      (l.map (shoupBinField k hk).toBits) = (shoupBinField k hk).toBits (a + l.sum) := by
  induction l generalizing a with
  | nil => simp [BinaryPolynomial.arithmeticFold]
  | cons b l ih =>
    rw [List.map_cons, BinaryPolynomial.arithmeticFold_cons]
    simp only [Bool.false_eq_true, if_false]
    rw [shoupXorBits_correct, ih, List.sum_cons, add_assoc]

def shoupSumProg : PolyTimeFun (Unary × List BitStr) BitStr :=
  let zero := shoupZeroProg.comp fst
  (BinaryPolynomial.arithmeticFoldProg false).comp (zero.pair (zero.pair snd))

theorem shoupSumProg_correct (k : ℕ) (hk : 1 ≤ k) (l : List (shoupBinField k hk).carrier) :
    shoupSumProg (unary k, l.map (shoupBinField k hk).toBits) =
      (shoupBinField k hk).toBits l.sum := by
  change BinaryPolynomial.arithmeticFold false (shoupZeroProg (unary k))
    (shoupZeroProg (unary k)) (l.map (shoupBinField k hk).toBits) = _
  rw [shoupZeroProg_correct k hk, shoupArithmeticFold_add_correct, zero_add]

/-- Compute all primitive projections, select their first nonzero images, and sum them. -/
def shoupNormalElementProg : PolyTimeFun Unary BitStr :=
  let images := (mapWith (shoupProjectedVectorProg.comp (snd.pair fst))).comp
    (groupComponentsProg.pair (PolyTimeFun.id _))
  shoupSumProg.comp ((PolyTimeFun.id _).pair images)

theorem shoupNormalElementProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] :
    shoupNormalElementProg (unary k) = (shoupBinField k hk).toBits (shoupNormalElement k hk) := by
  change shoupSumProg (unary k, (groupComponentsProg (unary k)).map
    (fun e => shoupProjectedVectorProg (unary k, e))) = _
  rw [groupComponentsProg_correct, List.map_map]
  simp only [Function.comp_def, shoupProjectedVectorProg_correct k hk]
  rw [show (groupComponents k).map (fun e => (shoupBinField k hk).toBits (shoupProjectedVector k hk e)) =
    ((groupComponents k).map (shoupProjectedVector k hk)).map (shoupBinField k hk).toBits by
      rw [List.map_map]; rfl, shoupSumProg_correct]
  congr 1
  simp [shoupNormalElement, List.get_eq_getElem]

/-- Print the constructed normal basis in Frobenius order. -/
def shoupNormalBasisProg : PolyTimeFun Unary (List BitStr) :=
  shoupOrbitProg.comp ((PolyTimeFun.id _).pair shoupNormalElementProg)

theorem shoupNormalBasisProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    shoupNormalBasisProg (unary k) =
      List.ofFn (fun i => (shoupBinField k hk).toBits (shoupNormalBasis k hk hodd i)) := by
  change shoupOrbitProg (unary k, shoupNormalElementProg (unary k)) = _
  rw [shoupNormalElementProg_correct k hk, shoupOrbitProg_correct]
  simp only [shoupNormalBasis_apply]

end MIPRE.SAT

end
