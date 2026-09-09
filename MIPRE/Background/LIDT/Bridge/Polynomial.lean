/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Bridge.Field
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.LinePolynomials
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.LowDegreePolynomial

/-!
# Bridge, part 2: polynomial answer alphabets

Our answer alphabets are coefficient vectors (`LinePoly F n := Fin (n+1) → F`) and
coefficient tables (`LowIndDegPoly := (Fin m → Fin (d+1)) → F`); the MIPStarRE
development uses subtypes of Mathlib's `Polynomial` and `MvPolynomial` with degree
bounds (`AxisLinePolynomial`, `DiagonalLinePolynomial`, `MIPStarRE.LDT.Polynomial`).
This file provides the equivalences between the two, and shows that evaluation is
compatible with them through the field coding.
-/

open MIPStarRE.LDT (encodeScalar decodeScalar evalLinePolynomialModel evalPolynomialModel)

noncomputable section

namespace MIPRE.LIDT.Bridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-! ## Univariate polynomials from coefficient vectors -/

/-- The univariate polynomial with the given coefficients. -/
def ofCoeffs {n : ℕ} (c : LinePoly F n) : _root_.Polynomial F :=
  ∑ i, _root_.Polynomial.C (c i) * _root_.Polynomial.X ^ (i : ℕ)

omit [Fintype F] [DecidableEq F] in
theorem natDegree_ofCoeffs_le {n : ℕ} (c : LinePoly F n) : (ofCoeffs c).natDegree ≤ n :=
  _root_.Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (_root_.Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.isLt)

omit [Fintype F] [DecidableEq F] in
theorem coeff_ofCoeffs {n : ℕ} (c : LinePoly F n) (i : Fin (n + 1)) :
    (ofCoeffs c).coeff i = c i := by
  simp [ofCoeffs, _root_.Polynomial.finsetSum_coeff, Fin.val_inj]

omit [Fintype F] [DecidableEq F] in
theorem ofCoeffs_coeff {n : ℕ} (p : _root_.Polynomial F) (hp : p.natDegree ≤ n) :
    ofCoeffs (fun i : Fin (n + 1) => p.coeff i) = p := by
  ext k
  by_cases hk : k ≤ n
  · exact coeff_ofCoeffs (fun i : Fin (n + 1) => p.coeff i) ⟨k, Nat.lt_succ_of_le hk⟩
  · push Not at hk
    rw [_root_.Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_ofCoeffs_le _) hk),
      _root_.Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hk)]

omit [Fintype F] [DecidableEq F] in
theorem eval_ofCoeffs {n : ℕ} (c : LinePoly F n) (t : F) :
    (ofCoeffs c).eval t = c.eval t := by
  simp [ofCoeffs, LinePoly.eval, _root_.Polynomial.eval_finsetSum]

/-- Axis-line answers: coefficient vectors of length `d + 1` versus polynomials of degree
at most `d`. -/
def axisEquiv : LinePoly F d ≃ MIPStarRE.LDT.AxisLinePolynomial (lidtParams F m d) where
  toFun c := ⟨ofCoeffs c, natDegree_ofCoeffs_le c⟩
  invFun f := fun i => f.poly.coeff i
  left_inv c := funext fun i => coeff_ofCoeffs c i
  right_inv f := MIPStarRE.LDT.AxisLinePolynomial.ext (ofCoeffs_coeff f.poly f.degreeBounded)

/-- Diagonal-line answers: coefficient vectors of length `m·d + 1` versus polynomials of
degree at most `m·d`. -/
def diagEquiv : LinePoly F (m * d) ≃ MIPStarRE.LDT.DiagonalLinePolynomial (lidtParams F m d) where
  toFun c := ⟨ofCoeffs c, natDegree_ofCoeffs_le c⟩
  invFun f := fun i => f.poly.coeff i
  left_inv c := funext fun i => coeff_ofCoeffs c i
  right_inv f := MIPStarRE.LDT.DiagonalLinePolynomial.ext (ofCoeffs_coeff f.poly f.degreeBounded)

@[simp] theorem axisEquiv_poly (c : LinePoly F d) :
    (axisEquiv (m := m) c).poly = ofCoeffs c := rfl

@[simp] theorem diagEquiv_poly (c : LinePoly F (m * d)) :
    (diagEquiv (d := d) c).poly = ofCoeffs c := rfl

/-- Evaluating an axis-line answer at a coded parameter. -/
theorem axisEquiv_apply_enc (c : LinePoly F d) (t : F) :
    (axisEquiv (m := m) c) (enc t) = enc (c.eval t) := by
  change evalLinePolynomialModel _ _ _ = _
  simp [evalLinePolynomialModel, eval_ofCoeffs]

/-- Evaluating a diagonal-line answer at a coded parameter. -/
theorem diagEquiv_apply_enc (c : LinePoly F (m * d)) (t : F) :
    (diagEquiv (d := d) c) (enc t) = enc (c.eval t) := by
  change evalLinePolynomialModel _ _ _ = _
  simp [evalLinePolynomialModel, eval_ofCoeffs]

/-! ## Multivariate polynomials from coefficient tables -/

/-- The exponent vector of a monomial index. -/
def expo (e : Fin m → Fin (d + 1)) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)

omit [NeZero m] in
@[simp] theorem expo_apply (e : Fin m → Fin (d + 1)) (i : Fin m) : expo e i = e i := by
  simp [expo]

omit [NeZero m] in
theorem expo_injective : Function.Injective (expo (m := m) (d := d)) := by
  intro e e' h
  funext i
  simpa [Fin.val_inj] using congrArg (fun s : Fin m →₀ ℕ => s i) h

/-- The multivariate polynomial with the given coefficient table. -/
def toMv (c : LowIndDegPoly (F := F) (m := m) (d := d)) : MvPolynomial (Fin m) F :=
  ∑ e, MvPolynomial.monomial (expo e) (c e)

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem coeff_toMv (c : LowIndDegPoly (F := F) (m := m) (d := d)) (e : Fin m → Fin (d + 1)) :
    (toMv c).coeff (expo e) = c e := by
  simp [toMv, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, expo_injective.eq_iff]

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem coeff_toMv_of_not_le (c : LowIndDegPoly (F := F) (m := m) (d := d)) (s : Fin m →₀ ℕ)
    (hs : ¬ ∀ i, s i ≤ d) : (toMv c).coeff s = 0 := by
  simp only [toMv, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  intro h
  apply hs
  intro i
  rw [← h, expo_apply]
  exact Nat.lt_succ_iff.mp (e i).isLt

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem degreeOf_toMv_le (c : LowIndDegPoly (F := F) (m := m) (d := d)) (i : Fin m) :
    (toMv c).degreeOf i ≤ d := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro s hs
  by_contra h
  exact MvPolynomial.mem_support_iff.mp hs
    (coeff_toMv_of_not_le c s fun h' => h (h' i))

omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- A polynomial of bounded individual degree is determined by its coefficient table. -/
theorem toMv_coeff (p : MvPolynomial (Fin m) F) (hp : ∀ i, p.degreeOf i ≤ d) :
    toMv (fun e : Fin m → Fin (d + 1) => p.coeff (expo e)) = p := by
  refine MvPolynomial.ext _ _ fun s => ?_
  by_cases hs : ∀ i, s i ≤ d
  · have : s = expo fun i => (⟨s i, Nat.lt_succ_of_le (hs i)⟩ : Fin (d + 1)) := by
      ext i; simp
    rw [this, coeff_toMv]
  · rw [coeff_toMv_of_not_le _ s hs]
    by_contra h
    push Not at hs
    obtain ⟨i, hi⟩ := hs
    have := MvPolynomial.degreeOf_le_iff.mp (hp i) s
      (MvPolynomial.mem_support_iff.mpr (Ne.symm h))
    omega

/-- Extensionality for MIPStarRE's global polynomial answers. -/
theorem polynomial_ext {g g' : MIPStarRE.LDT.Polynomial (lidtParams F m d)} (h : g.poly = g'.poly) :
    g = g' := by
  cases g; cases g'; cases h; rfl

/-- Global answers: coefficient tables versus polynomials of individual degree at most
`d`. -/
def lowIndDegEquiv :
    LowIndDegPoly (F := F) (m := m) (d := d) ≃ MIPStarRE.LDT.Polynomial (lidtParams F m d) where
  toFun c := ⟨toMv c, degreeOf_toMv_le c⟩
  invFun g := fun e => g.poly.coeff (expo e)
  left_inv c := funext fun e => coeff_toMv c e
  right_inv g := polynomial_ext (toMv_coeff g.poly g.lowIndividualDegree)

@[simp] theorem lowIndDegEquiv_poly (c : LowIndDegPoly (F := F) (m := m) (d := d)) :
    (lowIndDegEquiv c).poly = toMv c := rfl

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem eval_toMv (c : LowIndDegPoly (F := F) (m := m) (d := d)) (u : Point F m) :
    MvPolynomial.eval u (toMv c) = c.eval u := by
  simp only [toMv, map_sum, MvPolynomial.eval_monomial, LowIndDegPoly.eval]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finsupp.prod_fintype _ _ fun i => pow_zero (u i)]
  simp

/-- Evaluating a global answer at a coded point. -/
theorem lowIndDegEquiv_apply_encP (c : LowIndDegPoly (F := F) (m := m) (d := d))
    (u : Point F m) :
    (lowIndDegEquiv c) (encP u) = enc (c.eval u) := by
  change evalPolynomialModel _ _ _ = _
  simp [evalPolynomialModel, eval_toMv]

end MIPRE.LIDT.Bridge

end
