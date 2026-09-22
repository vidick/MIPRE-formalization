/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.NormalElementProg
import MIPRE.Foundations.LowDegree.BinaryInverse

/-! # Uniform executable line representatives

The program selects the first nonzero direction coordinate, divides the point
coordinate by it, and subtracts that multiple of the direction. Selection,
inversion, multiplication and the coordinate scan are actual ambient programs.
The raw program is polynomial-time and total on every input; correctness is
stated on canonical encodings in the constructed Shoup field.
-/

noncomputable section
namespace MIPRE.Introspection.LineProgram
open Cost Cost.PolyTimeFun Polynomial LowDegree LowDegree.BinaryLinear SAT

def firstPair {F : Type*} [Zero F] [DecidableEq F] (l : List (F × F)) : F × F :=
  l.foldr (fun a s => if a.2 ≠ 0 then a else s) (0, 0)

theorem firstPair_getD {F : Type*} [Zero F] [DecidableEq F]
    (l : List (F × F)) (j : ℕ)
    (hj : (l.getD j (0, 0)).2 ≠ 0)
    (hprev : ∀ i < j, (l.getD i (0, 0)).2 = 0) :
    firstPair l = l.getD j (0, 0) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero => simpa [firstPair] using (if_pos (by simpa using hj) :
        (if a.2 ≠ 0 then a else firstPair l) = a)
    | succ j =>
      have ha : a.2 = 0 := by simpa using hprev 0 (by omega)
      have hj' : (l.getD j (0, 0)).2 ≠ 0 := by simpa using hj
      have hp : ∀ i < j, (l.getD i (0, 0)).2 = 0 := by
        intro i hi
        simpa using hprev (i + 1) (by omega)
      simpa [firstPair, ha] using ih j hj' hp

theorem firstPair_ofFn {F : Type*} [Zero F] [DecidableEq F] {n : ℕ}
    (u v : Fin n → F) (hv : ∃ j, v j ≠ 0) :
    firstPair (List.ofFn fun i => (u i, v i)) =
      (u (Fin.find (fun j => v j ≠ 0) hv), v (Fin.find (fun j => v j ≠ 0) hv)) := by
  let j := Fin.find (fun j => v j ≠ 0) hv
  have he : ∀ i : Fin n,
      (List.ofFn (fun i => (u i, v i))).getD i.val (0, 0) = (u i, v i) := by
    intro i
    simp [List.getD_eq_getElem?_getD, i.isLt]
  rw [← he j]
  apply firstPair_getD
  · rw [he]
    exact Fin.find_spec hv
  · intro i hi
    have hin : i < n := hi.trans j.isLt
    rw [he ⟨i, hin⟩]
    exact not_not.mp (Fin.find_min hv hi)

def coefficient {F : Type*} [Field F] [DecidableEq F] (l : List (F × F)) : F :=
  let p := firstPair l
  if p.2 ≠ 0 then p.1 * p.2⁻¹ else 0

def representative {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (u v : Fin n → F) : Fin n → F :=
  u - coefficient (List.ofFn fun i => (u i, v i)) • v

theorem representative_nonzero {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (u v : Fin n → F) (hv : ∃ j, v j ≠ 0) :
    representative u v = u - (u (Fin.find (fun j => v j ≠ 0) hv) /
      v (Fin.find (fun j => v j ≠ 0) hv)) • v := by
  simp only [representative, coefficient, firstPair_ofFn u v hv,
    if_pos (Fin.find_spec hv), div_eq_mul_inv]

private def selectPairStep : PolyTimeFun ((BitStr × BitStr) × (BitStr × BitStr))
    (BitStr × BitStr) :=
  ite (nonzeroRowProg.comp (snd.comp snd)) snd fst

def firstPairBitsProg :
    PolyTimeFun (List (BitStr × BitStr) × (BitStr × BitStr)) (BitStr × BitStr) :=
  congr ((foldlAdd selectPairStep X (by
    intro s a
    change esize (if nonzeroRow a.2 then a else s) ≤ esize s + X.eval (esize a)
    rw [eval_X]
    split <;> omega)).comp ((PolyTimeFun.reverse.comp fst).pair snd))
    (fun p => p.1.foldr (fun a s => if nonzeroRow a.2 then a else s) p.2) (by
      intro p
      change p.1.reverse.foldl (fun s a => if nonzeroRow a.2 then a else s) p.2 = _
      exact List.foldr_eq_foldl_reverse.symm)

theorem firstPairBitsProg_correct (k : ℕ) (hk : 1 ≤ k)
    (l : List ((shoupBinField k hk).carrier × (shoupBinField k hk).carrier)) :
    firstPairBitsProg
      (l.map (fun p => ((shoupBinField k hk).toBits p.1, (shoupBinField k hk).toBits p.2)),
        ((shoupBinField k hk).toBits 0, (shoupBinField k hk).toBits 0)) =
      ((shoupBinField k hk).toBits (firstPair l).1,
        (shoupBinField k hk).toBits (firstPair l).2) := by
  change (l.map _).foldr _ _ = _
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.foldr_cons, shoupNonzeroRow_correct, ih]
    by_cases ha : a.2 = 0 <;> simp [firstPair, ha]

private def coefficientOfPairProg : PolyTimeFun (Unary × BitStr × BitStr) BitStr :=
  ite (nonzeroRowProg.comp (snd.comp snd))
    (shoupMulProg.comp (fst.pair ((fst.comp snd).pair
      (shoupInvProg.comp (fst.pair (snd.comp snd))))))
    (shoupZeroProg.comp fst)

theorem coefficientOfPairProg_correct (k : ℕ) (hk : 1 ≤ k)
    (a c : (shoupBinField k hk).carrier) :
    coefficientOfPairProg (unary k, (shoupBinField k hk).toBits a,
      (shoupBinField k hk).toBits c) =
      (shoupBinField k hk).toBits (if c ≠ 0 then a * c⁻¹ else 0) := by
  change (if nonzeroRow ((shoupBinField k hk).toBits c) then
    shoupMulProg (unary k, (shoupBinField k hk).toBits a,
      shoupInvProg (unary k, (shoupBinField k hk).toBits c)) else
    shoupZeroProg (unary k)) = _
  rw [shoupNonzeroRow_correct]
  by_cases hc : c = 0
  · simp only [hc, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
    exact shoupZeroProg_correct k hk
  · simp only [hc, ne_eq, not_false_eq_true, decide_true, if_true]
    rw [shoupInvProg_correct k hk c hc, shoupMulProg_encoding]

/-- Select a pivot and compute its point/direction ratio; the all-zero direction
has coefficient zero. -/
def coefficientBitsProg : PolyTimeFun (Unary × List (BitStr × BitStr)) BitStr :=
  let z := shoupZeroProg.comp fst
  coefficientOfPairProg.comp (fst.pair
    (firstPairBitsProg.comp (snd.pair (z.pair z))))

theorem coefficientBitsProg_correct (k : ℕ) (hk : 1 ≤ k)
    (l : List ((shoupBinField k hk).carrier × (shoupBinField k hk).carrier)) :
    coefficientBitsProg
      (unary k, l.map (fun p => ((shoupBinField k hk).toBits p.1,
        (shoupBinField k hk).toBits p.2))) =
      (shoupBinField k hk).toBits (coefficient l) := by
  change coefficientOfPairProg (unary k, firstPairBitsProg
    (l.map _, (shoupZeroProg (unary k), shoupZeroProg (unary k)))) = _
  rw [shoupZeroProg_correct k hk, firstPairBitsProg_correct,
    coefficientOfPairProg_correct]
  rfl

private def subtractStepProg :
    PolyTimeFun ((BitStr × BitStr) × (Unary × BitStr)) BitStr :=
  BinaryPolynomial.xorBitsProg.comp ((fst.comp fst).pair
    (shoupMulProg.comp ((fst.comp snd).pair ((snd.comp snd).pair (snd.comp fst)))))

/-- One uniform program for arbitrary field widths and vector lengths. -/
def lineRepresentativeProg : PolyTimeFun (Unary × List BitStr × List BitStr) (List BitStr) :=
  let ps := zip.comp snd
  (mapWith subtractStepProg).comp
    (ps.pair (fst.pair (coefficientBitsProg.comp (fst.pair ps))))

theorem lineRepresentativeProg_correct (k : ℕ) (hk : 1 ≤ k) {n : ℕ}
    (u v : Fin n → (shoupBinField k hk).carrier) :
    lineRepresentativeProg (unary k, (shoupBinField k hk).vecBits u,
      (shoupBinField k hk).vecBits v) =
      (shoupBinField k hk).vecBits (representative u v) := by
  let l := List.ofFn fun i => (u i, v i)
  have hz : ((shoupBinField k hk).vecBits u).zip ((shoupBinField k hk).vecBits v) =
      l.map (fun p => ((shoupBinField k hk).toBits p.1,
        (shoupBinField k hk).toBits p.2)) := by
    apply List.ext_getElem
    · simp [BinField.vecBits, l]
    · intro i hi hj
      simp [BinField.vecBits, l]
  change (((shoupBinField k hk).vecBits u).zip ((shoupBinField k hk).vecBits v)).map
    (fun p => BinaryPolynomial.xorBits p.1
      (shoupMulProg (unary k, coefficientBitsProg (unary k,
        ((shoupBinField k hk).vecBits u).zip ((shoupBinField k hk).vecBits v)), p.2))) = _
  rw [hz, coefficientBitsProg_correct]
  simp only [l, List.map_ofFn, BinField.vecBits]
  apply congrArg List.ofFn
  funext i
  change BinaryPolynomial.xorBits ((shoupBinField k hk).toBits (u i))
    (shoupMulProg (unary k, (shoupBinField k hk).toBits (coefficient l),
      (shoupBinField k hk).toBits (v i))) =
    (shoupBinField k hk).toBits (u i - coefficient l * v i)
  rw [shoupMulProg_encoding, shoupXorBits_correct, CharTwo.sub_eq_add]

/-- The ambient program halts within one polynomial for every raw input,
including malformed field elements and unequal vector lengths. -/
theorem lineRepresentativeProg_runs (x : Unary × List BitStr × List BitStr) :
    ∃ r ≤ lineRepresentativeProg.timeBound.eval (esize x),
      lineRepresentativeProg.code.Runs (encode x) (encode (lineRepresentativeProg x)) r :=
  lineRepresentativeProg.computes x

/-- The same program has one polynomial bound in field width plus vector
length; the polynomial is independent of both parameters. -/
theorem lineRepresentativeProg_time_le : ∃ R : Polynomial ℕ,
    ∀ (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
      (u v : Fin n → (shoupBinField k hk).carrier),
      ∃ r ≤ R.eval (n + k + 1),
        lineRepresentativeProg.code.Runs
          (encode (unary k, (shoupBinField k hk).vecBits u,
            (shoupBinField k hk).vecBits v))
          (encode ((shoupBinField k hk).vecBits (representative u v))) r := by
  refine ⟨lineRepresentativeProg.timeBound.comp (20 * X ^ 2), fun k hk n u v => ?_⟩
  obtain ⟨r, hr, hrun⟩ := lineRepresentativeProg_runs
    (unary k, (shoupBinField k hk).vecBits u, (shoupBinField k hk).vecBits v)
  rw [lineRepresentativeProg_correct] at hrun
  refine ⟨r, hr.trans ?_, hrun⟩
  have hu := esize_rows_of_width ((shoupBinField k hk).vecBits u) k
    (fun _ he => le_of_eq ((shoupBinField k hk).width_vecBits u he))
  have hv := esize_rows_of_width ((shoupBinField k hk).vecBits v) k
    (fun _ he => le_of_eq ((shoupBinField k hk).width_vecBits v he))
  simp only [BinField.length_vecBits] at hu hv
  have hsize : esize (unary k, (shoupBinField k hk).vecBits u,
      (shoupBinField k hk).vecBits v) ≤ 20 * (n + k + 1) ^ 2 := by
    simp only [esize_prod, esize_unary]
    nlinarith [Nat.zero_le (n * n), Nat.zero_le (k * k), Nat.zero_le (n * k)]
  simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X] using
    polynomial_eval_mono lineRepresentativeProg.timeBound hsize

end MIPRE.Introspection.LineProgram
end
