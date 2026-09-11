/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Bridge.Polynomial
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyCore

/-!
# Bridge, part 3: measurements

A strategy for our game carries one projective measurement per question, with outcomes
in `Answer F m d`. The MIPStarRE strategy container `ProjStrat` wants instead

* point measurements with outcomes in the coded field,
* a measurement for *every* presentation `(base, direction)` of an axis-parallel line,
  with outcomes the polynomials of degree `≤ d` in the parameter of that presentation,
  covariant under rebasing the presentation (`AxisParallelMeasurementReparamInvariant`),
* and likewise for diagonal lines.

This file builds these from the strategy's measurements at the *canonical* line
questions: the measurement at a presentation `ℓ` is the coarse-graining
(`ProjMeas.postprocess`) of the measurement at the canonical question of `ℓ` along the
map sending an answer `g` (a polynomial in the canonical parameter `s`) to the polynomial
`t ↦ g(b + c·t)` in the parameter `t` of `ℓ`, where `s = b + c·t` is the change of
parameters. Covariance under rebasing then follows from the composition law
`affine_comp_shift`, and ill-typed answers are sent to the zero polynomial.
-/

open MIPStarRE.LDT (Fq ProjMeas SubMeas Measurement IdxProjMeas AxisParallelLine DiagonalLine
  AxisLinePolynomial DiagonalLinePolynomial AxisParallelMeasurementReparamInvariant
  DiagonalMeasurementReparamInvariant decodeScalar encodeScalar zeroCoord)
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace MIPRE.LIDT

/-! ## Lemmas on canonical lines -/

namespace Line

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-- `Fin.find` only depends on the predicate. -/
theorem find_congr {p q : Fin m → Prop} [DecidablePred p] [DecidablePred q]
    (hp : ∃ k, p k) (hq : ∃ k, q k) (h : ∀ k, p k ↔ q k) :
    Fin.find p hp = Fin.find q hq := by
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    exact Fin.find_min hp hlt ((h _).mpr (Fin.find_spec hq))
  · by_contra hlt
    push Not at hlt
    exact Fin.find_min hq hlt ((h _).mp (Fin.find_spec hp))

omit [Fintype F] in
/-- The canonical presentation only depends on the line. -/
theorem through_add_smul (u v : Point F m) (t : F) :
    through (u + t • v) v = through u v := by
  unfold through
  split_ifs with h
  · have hj : v (Fin.find (fun j => v j ≠ 0) h) ≠ 0 := Fin.find_spec h
    simp only [Prod.mk.injEq, and_true]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · have hv : v = 0 := by
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    simp [hv]

omit [Fintype F] in
/-- The base point of a canonical presentation lies on it. -/
theorem mem_through (u v : Point F m) : (through u v).Mem u := by
  unfold through Mem
  split_ifs with h
  · refine ⟨u (Fin.find (fun j => v j ≠ 0) h), ?_⟩
    simp only [sub_add_cancel]
  · exact ⟨0, by simp⟩

omit [Fintype F] in
/-- The parameter of the base point on its canonical presentation. -/
theorem param_through (u v : Point F m) :
    (through u v).param u =
      if h : ∃ j, v j ≠ 0 then u (Fin.find (fun j => v j ≠ 0) h) else 0 := by
  unfold through param
  by_cases h : ∃ j, v j ≠ 0
  · have hj : v (Fin.find (fun j => v j ≠ 0) h) ≠ 0 := Fin.find_spec h
    have hiff : ∀ k, ((v (Fin.find (fun j => v j ≠ 0) h))⁻¹ • v) k ≠ 0 ↔ v k ≠ 0 :=
      fun k => by simp [hj]
    simp only [dif_pos h]
    split_ifs with h'
    · congr 1
      exact find_congr h' h hiff
    · exact absurd ⟨_, (hiff _).mpr hj⟩ h'
  · simp only [dif_neg h]
    split_ifs with h'
    · simp at h'
    · rfl

omit [Fintype F] in
/-- The parameter of a point on its canonical axis-parallel line is its coordinate in the
direction of the line. -/
theorem param_through_single (u : Point F m) (i : Fin m) :
    (through u (Pi.single i 1)).param u = u i := by
  have h : ∃ j, Pi.single (M := fun _ => F) i 1 j ≠ 0 := ⟨i, by simp⟩
  rw [param_through, dif_pos h]
  congr 1
  have hs := Fin.find_spec h
  by_contra hne
  exact hs (Pi.single_eq_of_ne hne 1)

end Line

namespace Bridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-! ## From projective measurement families to MIPStarRE measurements -/

/-- The measurement for the question `x` of a projective family on `ℂ^{n×n}`, as a
MIPStarRE projective measurement. -/
def toProjMeas {X A n : Type*} [Fintype A] [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) : ProjMeas A n where
  outcome := P.M x
  total := 1
  outcome_pos a := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (P.M x a)
    rw [← Matrix.star_eq_conjTranspose, P.selfAdjoint x a, P.projective x a] at h
    exact Matrix.nonneg_iff_posSemidef.mpr h
  sum_eq_total := P.normalized x
  total_le_one := le_rfl
  total_eq_one := rfl
  proj := P.projective x

@[simp] theorem toProjMeas_outcome {X A n : Type*} [Fintype A] [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) (a : A) :
    (toProjMeas P x).outcome a = P.M x a := rfl

@[simp] theorem toProjMeas_total {X A n : Type*} [Fintype A] [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) :
    (toProjMeas P x).total = 1 := rfl

/-- Two coarse-grainings of the same measurement agree on outcomes whose fibers agree. -/
theorem postprocess_outcome_congr {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq ι] (M : ProjMeas α ι) (φ φ' : α → β) (b b' : β)
    (h : ∀ a, φ' a = b' ↔ φ a = b) :
    (M.postprocess φ').outcome b' = (M.postprocess φ).outcome b := by
  classical
  change (MIPStarRE.LDT.postprocess M.toSubMeas φ').outcome b' =
    (MIPStarRE.LDT.postprocess M.toSubMeas φ).outcome b
  simp only [MIPStarRE.LDT.SubMeas.postprocess_outcome]
  exact Finset.sum_congr (Finset.filter_congr fun a _ => h a) fun _ _ => rfl

/-! ## Affine reparametrization of line answers -/

/-- Substitute `b + c·X` into a univariate polynomial. -/
def affine (g : _root_.Polynomial F) (b c : F) : _root_.Polynomial F :=
  g.comp (_root_.Polynomial.C b + _root_.Polynomial.C c * _root_.Polynomial.X)

omit [Fintype F] [DecidableEq F] in
theorem natDegree_affine_le {g : _root_.Polynomial F} {k : ℕ} (hg : g.natDegree ≤ k)
    (b c : F) : (affine g b c).natDegree ≤ k := by
  refine _root_.Polynomial.natDegree_comp_le.trans ?_
  have h1 : (_root_.Polynomial.C b + _root_.Polynomial.C c * _root_.Polynomial.X).natDegree ≤ 1 :=
    (_root_.Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
      ((_root_.Polynomial.natDegree_C_mul_le _ _).trans _root_.Polynomial.natDegree_X_le))
  calc g.natDegree * (_root_.Polynomial.C b + _root_.Polynomial.C c * _root_.Polynomial.X).natDegree
      ≤ k * 1 := Nat.mul_le_mul hg h1
    _ = k := mul_one k

omit [Fintype F] [DecidableEq F] in
/-- Shifting the parameter of an affinely reparametrized polynomial. -/
theorem affine_comp_shift (g : _root_.Polynomial F) (b c t : F) :
    (affine g b c).comp (_root_.Polynomial.C t + _root_.Polynomial.X) = affine g (b + c * t) c := by
  simp only [affine, _root_.Polynomial.comp_assoc]
  congr 1
  simp only [_root_.Polynomial.add_comp, _root_.Polynomial.mul_comp, _root_.Polynomial.C_comp,
    _root_.Polynomial.X_comp, _root_.Polynomial.C_add, _root_.Polynomial.C_mul]
  ring

omit [Fintype F] [DecidableEq F] in
@[simp] theorem eval_affine (g : _root_.Polynomial F) (b c t : F) :
    (affine g b c).eval t = g.eval (b + c * t) := by
  simp [affine, _root_.Polynomial.eval_comp]

/-- The univariate polynomial of degree `≤ d` answered to an axis-parallel line question
(`0` for ill-typed answers). -/
def axisPolyOf : Answer F m d → _root_.Polynomial F
  | .axisPoly c => ofCoeffs c
  | _ => 0

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem natDegree_axisPolyOf_le (a : Answer F m d) : (axisPolyOf a).natDegree ≤ d := by
  cases a <;> simp [axisPolyOf, natDegree_ofCoeffs_le]

/-- The univariate polynomial of degree `≤ m·d` answered to a diagonal line question
(`0` for ill-typed answers). -/
def diagPolyOf : Answer F m d → _root_.Polynomial F
  | .diagPoly c => ofCoeffs c
  | _ => 0

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem natDegree_diagPolyOf_le (a : Answer F m d) : (diagPolyOf a).natDegree ≤ m * d := by
  cases a <;> simp [diagPolyOf, natDegree_ofCoeffs_le]

/-- The axis-line answer, in the parameter `t` of a presentation whose base point has
parameter `b` on the canonical line (so that `s = b + t`), read from an answer of the
strategy at the canonical question. -/
def axisAnswer (b : F) (a : Answer F m d) : AxisLinePolynomial (lidtParams F m d) :=
  ⟨affine (axisPolyOf a) b 1, natDegree_affine_le (natDegree_axisPolyOf_le a) b 1⟩

/-- The diagonal-line answer, in the parameter `t` of a presentation related to the
canonical parameter by `s = b + c·t`, read from an answer of the strategy at the
canonical question. -/
def diagAnswer (b c : F) (a : Answer F m d) : DiagonalLinePolynomial (lidtParams F m d) :=
  ⟨affine (diagPolyOf a) b c, natDegree_affine_le (natDegree_diagPolyOf_le a) b c⟩

theorem axisAnswer_reparamAt (b : F) (a : Answer F m d) (t : Fq (lidtParams F m d)) :
    (axisAnswer b a).reparamAt t = axisAnswer (b + dec t) a := by
  apply AxisLinePolynomial.ext
  change (affine _ b 1).comp (_root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X) =
    affine _ (b + dec t) 1
  -- `rw [affine_comp_shift]` no longer finds its pattern under Lean v4.33; use the lemma
  -- as a term, up to `1 * s = s`.
  exact (affine_comp_shift _ _ _ _).trans
    (congrArg (fun s => affine (axisPolyOf a) (b + s) 1) (one_mul _))

theorem diagAnswer_reparamAt (b c : F) (a : Answer F m d) (t : Fq (lidtParams F m d)) :
    (diagAnswer b c a).reparamAt t = diagAnswer (b + c * dec t) c a := by
  apply DiagonalLinePolynomial.ext
  change (affine _ b c).comp (_root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X) =
    affine _ (b + c * dec t) c
  exact affine_comp_shift _ _ _ _

/-- The value at the coded parameter `0` of an axis-line answer. -/
theorem axisAnswer_zeroCoord (b : F) (a : Answer F m d) :
    (axisAnswer b a) (zeroCoord (params := lidtParams F m d)) = enc ((axisPolyOf a).eval b) := by
  change MIPStarRE.LDT.evalLinePolynomialModel _ _ _ = _
  simp [MIPStarRE.LDT.evalLinePolynomialModel, axisAnswer]

/-- The value at the coded parameter `0` of a diagonal-line answer. -/
theorem diagAnswer_zeroCoord (b c : F) (a : Answer F m d) :
    (diagAnswer b c a) (zeroCoord (params := lidtParams F m d)) = enc ((diagPolyOf a).eval b) := by
  change MIPStarRE.LDT.evalLinePolynomialModel _ _ _ = _
  simp [MIPStarRE.LDT.evalLinePolynomialModel, diagAnswer]

/-! ## Line measurement families -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The canonical line of an axis-parallel line presentation. -/
def axisCanon (ℓ : AxisParallelLine (lidtParams F m d)) : Line F m :=
  Line.through (decP ℓ.base) (Pi.single ℓ.direction 1)

/-- The parameter, on the canonical line, of the base point of an axis-parallel line
presentation. -/
def axisBase (ℓ : AxisParallelLine (lidtParams F m d)) : F := dec (ℓ.base ℓ.direction)

/-- The axis-parallel line measurement family induced by a strategy's measurement family. -/
def axisMeas (P : ProjectiveMeasurement (Question F m) (Answer F m d) (Matrix n n ℂ)) :
    IdxProjMeas (AxisParallelLine (lidtParams F m d)) (AxisLinePolynomial (lidtParams F m d)) n :=
  fun ℓ => (toProjMeas P (.axisLine (axisCanon ℓ))).postprocess (axisAnswer (axisBase ℓ))

theorem axisCanon_rebaseAt (ℓ : AxisParallelLine (lidtParams F m d)) (t : Fq (lidtParams F m d)) :
    axisCanon (ℓ.rebaseAt t) = axisCanon ℓ := by
  simp only [axisCanon, AxisParallelLine.rebaseAt, decP_axis_pointAt]
  exact Line.through_add_smul _ _ _

theorem axisBase_rebaseAt (ℓ : AxisParallelLine (lidtParams F m d)) (t : Fq (lidtParams F m d)) :
    axisBase (ℓ.rebaseAt t) = axisBase ℓ + dec t := by
  simp [axisBase, AxisParallelLine.rebaseAt, AxisParallelLine.pointAt]

theorem axisMeas_invariant (P : ProjectiveMeasurement (Question F m) (Answer F m d) (Matrix n n ℂ)) :
    AxisParallelMeasurementReparamInvariant (lidtParams F m d) (axisMeas P) := by
  intro ℓ t f
  simp only [axisMeas, axisCanon_rebaseAt, axisBase_rebaseAt]
  apply postprocess_outcome_congr
  intro a
  rw [← axisAnswer_reparamAt]
  exact (AxisLinePolynomial.reparamAtEquiv t).apply_eq_iff_eq

/-- The canonical line of a diagonal line presentation. -/
def diagCanon (ℓ : DiagonalLine (lidtParams F m d)) : Line F m :=
  Line.through (decP ℓ.base) (decP ℓ.direction)

/-- The change of parameters `s = b + c·t` from a diagonal line presentation to its canonical
line: `b` is the pivot coordinate of the base point and `c` the pivot coordinate of the
direction (`(0, 0)` for a singleton line). -/
def diagData (ℓ : DiagonalLine (lidtParams F m d)) : F × F :=
  if h : ∃ j, decP ℓ.direction j ≠ 0 then
    (decP ℓ.base (Fin.find (fun j => decP ℓ.direction j ≠ 0) h),
      decP ℓ.direction (Fin.find (fun j => decP ℓ.direction j ≠ 0) h))
  else (0, 0)

/-- The diagonal line measurement family induced by a strategy's measurement family. -/
def diagMeas (P : ProjectiveMeasurement (Question F m) (Answer F m d) (Matrix n n ℂ)) :
    IdxProjMeas (DiagonalLine (lidtParams F m d)) (DiagonalLinePolynomial (lidtParams F m d)) n :=
  fun ℓ => (toProjMeas P (.diagLine (diagCanon ℓ))).postprocess
    (diagAnswer (diagData ℓ).1 (diagData ℓ).2)

theorem diagCanon_rebaseAt (ℓ : DiagonalLine (lidtParams F m d)) (t : Fq (lidtParams F m d)) :
    diagCanon (ℓ.rebaseAt t) = diagCanon ℓ := by
  simp only [diagCanon, DiagonalLine.rebaseAt, decP_diag_pointAt]
  exact Line.through_add_smul _ _ _

theorem diagData_rebaseAt (ℓ : DiagonalLine (lidtParams F m d)) (t : Fq (lidtParams F m d)) :
    diagData (ℓ.rebaseAt t) = ((diagData ℓ).1 + (diagData ℓ).2 * dec t, (diagData ℓ).2) := by
  by_cases h : ∃ j, decP ℓ.direction j ≠ 0
  · simp only [diagData, DiagonalLine.rebaseAt, dif_pos h]
    rw [decP_diag_pointAt]
    refine Prod.ext ?_ rfl
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp [diagData, DiagonalLine.rebaseAt, dif_neg h]

theorem diagMeas_invariant (P : ProjectiveMeasurement (Question F m) (Answer F m d) (Matrix n n ℂ)) :
    DiagonalMeasurementReparamInvariant (lidtParams F m d) (diagMeas P) := by
  intro ℓ t f
  simp only [diagMeas, diagCanon_rebaseAt, diagData_rebaseAt]
  apply postprocess_outcome_congr
  intro a
  rw [← diagAnswer_reparamAt]
  exact (DiagonalLinePolynomial.reparamAtEquiv t).apply_eq_iff_eq

/-! ## Point measurement families -/

/-- The coded value of an answer to a point question. -/
def codedValue (a : Answer F m d) : Fq (lidtParams F m d) := enc a.toValue

/-- The point measurement family induced by a strategy's measurement family. -/
def pointMeas (P : ProjectiveMeasurement (Question F m) (Answer F m d) (Matrix n n ℂ)) :
    IdxProjMeas (MIPStarRE.LDT.Point (lidtParams F m d)) (Fq (lidtParams F m d)) n :=
  fun u => (toProjMeas P (.point (decP u))).postprocess codedValue

end Bridge

end MIPRE.LIDT

end
