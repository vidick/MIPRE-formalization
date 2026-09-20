/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Combined
import MIPRE.Foundations.Pasting

/-!
# Pairs of lines

Blueprint `lem:qld-pairs-of-lines`, the paper's `lem:qld-xz-lines`. The combined point measurement
of `lem:qld-combined-points` returns both bases' values at the two sampled points; this stage
replaces it by a measurement returning a *pair of line polynomials*, one per basis, which is what
the padding stage can then compare with a low-degree test.

The analytic content is the pasting lemma (`MIPRE/Foundations/Pasting.lean`). What this file
supplies is its four hypotheses at the QLD line measurements, and there are three pieces of
bookkeeping in the way.

* **The marginal step.** `lem:qld-combined-points` gives the joint measurement against the
  *ordered product* of the two point measurements; the pasting lemma wants each marginal against a
  single line measurement. `sum_xSqNorm_marg_le'` takes the first step and a three-term triangle
  through Bob's own point measurement takes the second.
* **The extended space.** The joint measurement lives on each party's space enlarged by one
  `F_q x F_q` register (the Naimark dilation); the line measurements live on the unenlarged ones.
  `xSqNorm_extVec2_aOp` transports the latter.
* **The probe.** The pasting lemma's collision term needs the point to be uniform on its line once
  the line is fixed. Here the content determines both, so the factorization is produced by
  *shifting the point along the direction the content itself carries*: for each fixed shift the map
  is a bijection of contents, the line data is invariant under it, and the parameter of the point
  moves by exactly the shift.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

/-! ## Line polynomials as polynomials

`LinePoly F n` is a coefficient vector, which is what makes the answer alphabets finite types. To
count the parameters at which two of them agree one wants Mathlib's `Polynomial`, and the bridge is
one definition and three lemmas. -/

section Poly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- The polynomial a coefficient vector represents. -/
def toPoly (f : LinePoly F n) : Polynomial F :=
  ∑ i : Fin (n + 1), Polynomial.monomial (i : ℕ) (f i)

theorem natDegree_toPoly_le (f : LinePoly F n) : (toPoly f).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  exact le_trans (Polynomial.natDegree_monomial_le (f i)) (Nat.lt_succ_iff.mp i.isLt)

theorem eval_toPoly (f : LinePoly F n) (t : F) :
    (toPoly f).eval t = LinePoly.eval f t := by
  rw [toPoly, Polynomial.eval_finsetSum, LinePoly.eval]
  exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.eval_monomial]

theorem coeff_toPoly (f : LinePoly F n) (i : Fin (n + 1)) :
    (toPoly f).coeff (i : ℕ) = f i := by
  classical
  rw [toPoly, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single_of_mem i (mem_univ i) fun j _ hji => ?_]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · rw [Polynomial.coeff_monomial, if_neg fun h => hji (Fin.ext h)]

theorem toPoly_injective : Function.Injective (toPoly : LinePoly F n → Polynomial F) := by
  intro f g h
  funext i
  rw [← coeff_toPoly f i, ← coeff_toPoly g i, h]

/-- **Two distinct line polynomials of degree at most `n` agree at at most `n` parameters.** The
collision bound the pasting lemma asks of the outcome map, for the map that evaluates a line
polynomial at the parameter of the sampled point. -/
theorem card_agree_linePoly_le {f g : LinePoly F n} (h : f ≠ g) :
    #{t ∈ (univ : Finset F) | LinePoly.eval f t = LinePoly.eval g t} ≤ n := by
  refine le_trans (le_of_eq (congrArg Finset.card (Finset.filter_congr fun t _ => ?_)))
    (MIPRE.LowDegree.card_agree_le_of_natDegree
      (fun he => h (toPoly_injective he))
      (natDegree_toPoly_le f) (natDegree_toPoly_le g))
  rw [eval_toPoly, eval_toPoly]

end Poly

/-! ## The parameter of a shifted point -/

section Shift

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-- **Shifting a point along the direction moves its parameter by the shift.** -/
theorem lineParam_add_smul {w : Point F m} (hw : ∃ j, w j ≠ 0) (u₀ x : Point F m) (t : F) :
    MIPRE.LIDT.CL.lineParam u₀ w (x + t • w) = MIPRE.LIDT.CL.lineParam u₀ w x + t := by
  simp only [MIPRE.LIDT.CL.lineParam, dif_pos hw]
  set j := Fin.find (fun j => w j ≠ 0) hw with hj
  have hwj : w j ≠ 0 := Fin.find_spec hw
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **The canonical representative does not see a shift along the direction**: the shifted point is
on the same line. -/
theorem rep_add_smul (w x : Point F m) (t : F) :
    MIPRE.LIDT.CL.rep w (x + t • w) = MIPRE.LIDT.CL.rep w x := by
  rw [MIPRE.LIDT.CL.rep, MIPRE.LIDT.CL.rep, map_add,
    show (MIPRE.CL.canonLin (Submodule.span F {w})) (t • w) = 0 from by
      rw [← LinearMap.mem_ker, MIPRE.CL.ker_canonLin]
      exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self w),
    add_zero]

end Shift

/-! ## Shifting the content's point along its line

The pasting lemma's collision term needs the point to be uniform on its line once the line is
fixed. The content determines both, so the factorization is produced by *shifting*: for each fixed
shift `t` the map `c |-> c + t . dir(c)` on the `W`-point is a bijection of contents, so averaging
over contents and averaging over `(c, t)` give the same thing; the line data is invariant under it;
and the parameter of the point moves by exactly `t`. -/

section ContentShift

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ} [NeZero m]

/-- Adding a vector to the content's `W`-point, leaving everything else alone. -/
def Content.shiftPt (W : Bas) (w : Point F m) (c : Content F m) : Content F m :=
  match W with
  | .X => { c with uX := c.uX + w }
  | .Z => { c with uZ := c.uZ + w }

@[simp] theorem Content.shiftPt_s (W : Bas) (w : Point F m) (c : Content F m) :
    (Content.shiftPt W w c).s = c.s := by cases W <;> rfl

@[simp] theorem Content.shiftPt_v (W : Bas) (w : Point F m) (c : Content F m) :
    (Content.shiftPt W w c).v = c.v := by cases W <;> rfl

@[simp] theorem Content.shiftPt_pt (W : Bas) (w : Point F m) (c : Content F m) :
    (Content.shiftPt W w c).pt W = c.pt W + w := by cases W <;> rfl

@[simp] theorem Content.shiftPt_pt_X_Z (w : Point F m) (c : Content F m) :
    (Content.shiftPt .X w c).pt .Z = c.pt .Z := rfl

@[simp] theorem Content.shiftPt_pt_Z_X (w : Point F m) (c : Content F m) :
    (Content.shiftPt .Z w c).pt .X = c.pt .X := rfl

@[simp] theorem Content.shiftPt_zero (W : Bas) (c : Content F m) :
    Content.shiftPt W 0 c = c := by
  cases W <;> · rw [Content.shiftPt, add_zero]

theorem Content.shiftPt_shiftPt (W : Bas) (w w' : Point F m) (c : Content F m) :
    Content.shiftPt W w' (Content.shiftPt W w c) = Content.shiftPt W (w + w') c := by
  cases W <;> · rw [Content.shiftPt, Content.shiftPt, Content.shiftPt]; congr 1; rw [add_assoc]

/-- The content shifted along a direction it determines itself. -/
def Content.shiftAlong (W : Bas) (dir : Content F m → Point F m) (t : F) (c : Content F m) :
    Content F m :=
  Content.shiftPt W (t • dir c) c

/-- **For each fixed shift, shifting is a bijection of contents.** Its inverse shifts by `-t`,
which is where the invariance of the direction is used. -/
theorem bijective_shiftAlong (W : Bas) {dir : Content F m → Point F m}
    (hdir : ∀ (c : Content F m) (w : Point F m), dir (Content.shiftPt W w c) = dir c) (t : F) :
    Function.Bijective (Content.shiftAlong W dir t) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨Content.shiftAlong W dir (-t), fun c => ?_,
    fun c => ?_⟩
  · rw [Content.shiftAlong, Content.shiftAlong, hdir, Content.shiftPt_shiftPt,
      show t • dir c + (-t) • dir c = 0 from by module, Content.shiftPt_zero]
  · rw [Content.shiftAlong, Content.shiftAlong, hdir, Content.shiftPt_shiftPt,
      show (-t) • dir c + t • dir c = 0 from by module, Content.shiftPt_zero]

theorem card_content_pos : 0 < Fintype.card (Content F m) :=
  Fintype.card_pos_iff.mpr ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- **The change of variables.** Averaging a quantity over contents is averaging it over
`(content, shift)` pairs with the point shifted --- the content average is the product of the line
average and the uniform average of the point on its line, without any quotient being formed. -/
theorem sum_content_shiftAlong (W : Bas) {dir : Content F m → Point F m}
    (hdir : ∀ (c : Content F m) (w : Point F m), dir (Content.shiftPt W w c) = dir c)
    (g : Content F m → ℝ) :
    ∑ i : Content F m × F, ((Fintype.card (Content F m) : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * g (Content.shiftAlong W dir i.2 i.1)
      = ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * g c := by
  classical
  have hF : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← sum_prod_eq fun (c : Content F m) (t : F) =>
    ((Fintype.card (Content F m) : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
      * g (Content.shiftAlong W dir t c), Finset.sum_comm]
  have hstep : ∀ t : F, ∑ c : Content F m,
      ((Fintype.card (Content F m) : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * g (Content.shiftAlong W dir t c)
      = (Fintype.card F : ℝ)⁻¹ * ∑ c : Content F m,
          (Fintype.card (Content F m) : ℝ)⁻¹ * g c := by
    intro t
    rw [Finset.mul_sum]
    refine Fintype.sum_bijective (Content.shiftAlong W dir t) (bijective_shiftAlong W hdir t)
      _ _ fun c => ?_
    ring
  rw [Finset.sum_congr rfl fun t (_ : t ∈ univ) => hstep t, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hF, one_mul]

end ContentShift

/-! ## What the shift leaves alone

The line a content presents --- its question, its base point and its direction --- is invariant
under shifting the point along that direction, and so therefore is the line measurement. The point's
parameter is the only thing that moves. -/

section Invariance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- The other basis. -/
def Bas.other : Bas → Bas
  | .X => .Z
  | .Z => .X

@[simp] theorem Content.shiftPt_pt_other (W : Bas) (w : Point F m) (c : Content F m) :
    (Content.shiftPt W w c).pt W.other = c.pt W.other := by cases W <;> rfl

@[simp] theorem Content.shiftPt_other_pt (W : Bas) (w : Point F m) (c : Content F m) :
    (Content.shiftPt W.other w c).pt W = c.pt W := by cases W <;> rfl

theorem Content.shiftAlong_eq (W : Bas) (dir : Content F m → Point F m) (t : F)
    (c : Content F m) :
    Content.shiftAlong W dir t c = Content.shiftPt W (t • dir c) c := rfl

theorem dirOf_shiftPt (hm : m ∣ Fintype.card F) (W : Bas) (w : Point F m) (c : Content F m) :
    dirOf hm (Content.shiftPt W w c) = dirOf hm c := by
  rw [dirOf, dirOf, Content.shiftPt_s]

theorem ddirOf_shiftPt (hm : m ∣ Fintype.card F) (W : Bas) (w : Point F m) (c : Content F m) :
    ddirOf hm (Content.shiftPt W w c) = ddirOf hm c := by
  rw [ddirOf, ddirOf, Content.shiftPt_s, Content.shiftPt_v]

theorem abaseOf_shiftAlong (hm : m ∣ Fintype.card F) (W : Bas) (t : F) (c : Content F m) :
    abaseOf hm W (Content.shiftAlong W (dirOf hm) t c) = abaseOf hm W c := by
  rw [abaseOf, abaseOf, Content.shiftAlong, dirOf_shiftPt, Content.shiftPt_pt, rep_add_smul]

theorem dbaseOf_shiftAlong (hm : m ∣ Fintype.card F) (W : Bas) (t : F) (c : Content F m) :
    dbaseOf hm W (Content.shiftAlong W (ddirOf hm) t c) = dbaseOf hm W c := by
  rw [dbaseOf, dbaseOf, Content.shiftAlong, ddirOf_shiftPt, Content.shiftPt_pt, rep_add_smul]

theorem question_aline_shiftAlong (hm : m ∣ Fintype.card F) (W : Bas) (t : F) (c : Content F m) :
    (Content.shiftAlong W (dirOf hm) t c).question hm (.aline W) = c.question hm (.aline W) := by
  rw [Content.question, Content.question, Content.shiftAlong, Content.shiftPt_s,
    Content.shiftPt_pt, dirOf]
  congr 1
  exact rep_add_smul _ _ _

theorem question_dline_shiftAlong (hm : m ∣ Fintype.card F) (W : Bas) (t : F) (c : Content F m) :
    (Content.shiftAlong W (ddirOf hm) t c).question hm (.dline W) = c.question hm (.dline W) := by
  rw [Content.question, Content.question, Content.shiftAlong, Content.shiftPt_s,
    Content.shiftPt_v, Content.shiftPt_pt, ddirOf]
  congr 1
  exact rep_add_smul _ _ _

theorem question_aline_shiftPt_other (hm : m ∣ Fintype.card F) (W : Bas) (w : Point F m)
    (c : Content F m) :
    (Content.shiftPt W.other w c).question hm (.aline W) = c.question hm (.aline W) := by
  cases W <;> rfl

theorem question_dline_shiftPt_other (hm : m ∣ Fintype.card F) (W : Bas) (w : Point F m)
    (c : Content F m) :
    (Content.shiftPt W.other w c).question hm (.dline W) = c.question hm (.dline W) := by
  cases W <;> rfl

/-- **The line measurement depends on the content only through the line.** -/
theorem hatLinePOVM_congr {d' : Type} [Fintype d'] [DecidableEq d'] {n : ℕ}
    (hm : m ∣ Fintype.card F) (M : Question F m → POVM (Answer F m d) d') (W : Bas) (ty : Ty)
    (base dir : Content F m → Point F m) {c c' : Content F m}
    (hq : c.question hm ty = c'.question hm ty) (hb : base c = base c') (hd : dir c = dir c') :
    hatLinePOVM n hm M W ty base dir c = hatLinePOVM n hm M W ty base dir c' := by
  rw [hatLinePOVM, hatLinePOVM, lineAnsPOVM, lineAnsPOVM, hq, hb, hd]

end Invariance

/-! ## The line presentations, and the measurements they carry

A *line presentation* on one side is the question type the line is asked at together with its base
point and direction as functions of the content, and the six invariances the shift argument needs:
shifting either point along the relevant direction changes neither the direction, nor the base
point, nor the question. Both line types of both sides are presentations, and the pairs-of-lines
lemma is proved once for any pair of them. -/

section Pres

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- A line presentation: what the content tells a player about the line on side `W`. -/
structure LinePres (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    (m : ℕ) [NeZero m] (hm : m ∣ Fintype.card F) (W : Bas) where
  /-- The question type the line is asked at. -/
  ty : Ty
  /-- The base point of the line. -/
  base : Content F m → Point F m
  /-- The direction of the line. -/
  dir : Content F m → Point F m
  /-- Shifting the side's own point along the direction does not change the direction. -/
  dir_shift : ∀ (c : Content F m) (w : Point F m), dir (Content.shiftPt W w c) = dir c
  /-- ... nor the base point. -/
  base_shift : ∀ (c : Content F m) (t : F),
    base (Content.shiftPt W (t • dir c) c) = base c
  /-- ... nor the question. -/
  question_shift : ∀ (c : Content F m) (t : F),
    (Content.shiftPt W (t • dir c) c).question hm ty = c.question hm ty
  /-- Shifting the *other* side's point changes none of the three. -/
  dir_shift_other : ∀ (c : Content F m) (w : Point F m),
    dir (Content.shiftPt W.other w c) = dir c
  base_shift_other : ∀ (c : Content F m) (w : Point F m),
    base (Content.shiftPt W.other w c) = base c
  question_shift_other : ∀ (c : Content F m) (w : Point F m),
    (Content.shiftPt W.other w c).question hm ty = c.question hm ty

namespace LinePres

variable {hm : m ∣ Fintype.card F} {W : Bas}

/-- The parameter of the sampled point on the line. -/
def param (P : LinePres F m hm W) (c : Content F m) : F :=
  MIPRE.LIDT.CL.lineParam (P.base c) (P.dir c) (c.pt W)

/-- **The parameter of the shifted point is the parameter plus the shift**, when the line is not
degenerate. -/
theorem param_shiftAlong (P : LinePres F m hm W) {c : Content F m}
    (hdeg : ∃ j, P.dir c j ≠ 0) (t : F) :
    P.param (Content.shiftAlong W P.dir t c) = P.param c + t := by
  rw [param, param, Content.shiftAlong_eq, P.base_shift, P.dir_shift, Content.shiftPt_pt,
    lineParam_add_smul hdeg]

/-- A degenerate line is not moved at all. -/
theorem param_shiftAlong_of_deg (P : LinePres F m hm W) {c : Content F m}
    (hdeg : P.dir c = 0) (t : F) :
    P.param (Content.shiftAlong W P.dir t c) = P.param c := by
  rw [param, param, Content.shiftAlong_eq, P.base_shift, P.dir_shift, Content.shiftPt_pt, hdeg,
    smul_zero, add_zero]

/-- The expanded line measurement the presentation carries, as a family of matrices. -/
def lineMats {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W) (d : ℕ)
    (M : Question F m → POVM (Answer F m d) d') (c : Content F m) :
    LinePoly F (m * d) → Matrix (d' × Anc F m) (d' × Anc F m) ℂ :=
  fun f => (((hatLinePOVM (m * d) hm M W P.ty P.base P.dir c).mats f).val)

/-- The same measurement, coarse-grained by evaluation at the sampled point's parameter. -/
def lineEvalMats {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W) (d : ℕ)
    (M : Question F m → POVM (Answer F m d) d') (c : Content F m) :
    F → Matrix (d' × Anc F m) (d' × Anc F m) ℂ :=
  fun a => ((((hatLinePOVM (m * d) hm M W P.ty P.base P.dir c).map
    fun f => LinePoly.eval f (P.param c)).mats a).val)

theorem isPVM_lineMats {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W) (d : ℕ)
    {M : Question F m → POVM (Answer F m d) d'}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (c : Content F m) :
    IsPVM (P.lineMats d M c) :=
  isPVM_hatLinePOVM (hM (c.question hm P.ty))

theorem isPVM_lineEvalMats {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W) (d : ℕ)
    {M : Question F m → POVM (Answer F m d) d'}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (c : Content F m) :
    IsPVM (P.lineEvalMats d M c) :=
  isPVM_povm_map _ (isPVM_hatLinePOVM (hM (c.question hm P.ty))) _

/-- The coarse-graining, as a fibre sum --- the shape the pasting lemma states its hypotheses
in. -/
theorem lineEvalMats_eq_fibSum {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W)
    (d : ℕ) (M : Question F m → POVM (Answer F m d) d') (c : Content F m) (a : F) :
    P.lineEvalMats d M c a = fibSum (P.lineMats d M c) (fun f => LinePoly.eval f (P.param c)) a :=
  AddSubmonoidClass.coe_finsetSum _ _

/-- **The line measurement is invariant under the shift**, the presentation's three invariances
being exactly what the measurement reads. -/
theorem lineMats_shiftAlong {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W) (d : ℕ)
    (M : Question F m → POVM (Answer F m d) d') (c : Content F m) (t : F) :
    P.lineMats d M (Content.shiftAlong W P.dir t c) = P.lineMats d M c :=
  congrArg (fun Q : POVM (LinePoly F (m * d)) (d' × Anc F m) => fun f => ((Q.mats f).val))
    (hatLinePOVM_congr hm M W P.ty P.base P.dir (P.question_shift c t) (P.base_shift c t)
      (P.dir_shift _ _))

/-- The same, for a shift of the other side's point. -/
theorem lineMats_shiftPt_other {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W)
    (d : ℕ) (M : Question F m → POVM (Answer F m d) d') (c : Content F m) (w : Point F m) :
    P.lineMats d M (Content.shiftPt W.other w c) = P.lineMats d M c :=
  congrArg (fun Q : POVM (LinePoly F (m * d)) (d' × Anc F m) => fun f => ((Q.mats f).val))
    (hatLinePOVM_congr hm M W P.ty P.base P.dir (P.question_shift_other c w)
      (P.base_shift_other c w) (P.dir_shift_other c w))

theorem param_shiftPt_other (P : LinePres F m hm W) (c : Content F m) (w : Point F m) :
    P.param (Content.shiftPt W.other w c) = P.param c := by
  rw [param, param, P.base_shift_other, P.dir_shift_other, Content.shiftPt_other_pt]

theorem lineEvalMats_shiftPt_other {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W)
    (d : ℕ) (M : Question F m → POVM (Answer F m d) d') (c : Content F m) (w : Point F m) :
    P.lineEvalMats d M (Content.shiftPt W.other w c) = P.lineEvalMats d M c := by
  have hQ : hatLinePOVM (m * d) hm M W P.ty P.base P.dir (Content.shiftPt W.other w c)
      = hatLinePOVM (m * d) hm M W P.ty P.base P.dir c :=
    hatLinePOVM_congr hm M W P.ty P.base P.dir (P.question_shift_other c w)
      (P.base_shift_other c w) (P.dir_shift_other c w)
  have hp : P.param (Content.shiftPt W.other w c) = P.param c := P.param_shiftPt_other c w
  show (fun a => ((((hatLinePOVM (m * d) hm M W P.ty P.base P.dir
      (Content.shiftPt W.other w c)).map
        fun f => LinePoly.eval f (P.param (Content.shiftPt W.other w c))).mats a).val)) = _
  rw [hQ, hp]
  rfl

end LinePres

/-! ### The four presentations, and the collision count -/

variable {hm : m ∣ Fintype.card F}

/-- The axis-parallel line presentation on side `W`. -/
def aPres (hm : m ∣ Fintype.card F) (W : Bas) : LinePres F m hm W where
  ty := .aline W
  base := abaseOf hm W
  dir := dirOf hm
  dir_shift c w := dirOf_shiftPt hm W w c
  base_shift c t := abaseOf_shiftAlong hm W t c
  question_shift c t := question_aline_shiftAlong hm W t c
  dir_shift_other c w := dirOf_shiftPt hm W.other w c
  base_shift_other c w := by rw [abaseOf, abaseOf, dirOf_shiftPt, Content.shiftPt_other_pt]
  question_shift_other c w := question_aline_shiftPt_other hm W w c

/-- The diagonal line presentation on side `W`. -/
def dPres (hm : m ∣ Fintype.card F) (W : Bas) : LinePres F m hm W where
  ty := .dline W
  base := dbaseOf hm W
  dir := ddirOf hm
  dir_shift c w := ddirOf_shiftPt hm W w c
  base_shift c t := dbaseOf_shiftAlong hm W t c
  question_shift c t := question_dline_shiftAlong hm W t c
  dir_shift_other c w := ddirOf_shiftPt hm W.other w c
  base_shift_other c w := by rw [dbaseOf, dbaseOf, ddirOf_shiftPt, Content.shiftPt_other_pt]
  question_shift_other c w := question_dline_shiftPt_other hm W w c

/-- **The axis-parallel direction is never degenerate**: it is a standard basis vector. -/
theorem aPres_dir_ne_zero (hm : m ∣ Fintype.card F) (W : Bas) (c : Content F m) :
    ∃ j, (aPres hm W).dir c j ≠ 0 := by
  refine ⟨MIPRE.LIDT.CL.chi hm c.s, ?_⟩
  show (dirOf hm c) (MIPRE.LIDT.CL.chi hm c.s) ≠ 0
  rw [dirOf, Pi.single_eq_same]
  exact one_ne_zero

/-- The collision probability of a presentation: the fraction of parameters at which two distinct
line polynomials of degree at most `m d` can agree. It is `m d / q` unless the line is degenerate,
and then the outcome map separates nothing. -/
def collProb (P : LinePres F m hm W) (d : ℕ) (c : Content F m) : ℝ :=
  if ∃ j, P.dir c j ≠ 0 then (m * d : ℝ) / (Fintype.card F : ℝ) else 1

theorem collProb_nonneg (P : LinePres F m hm W) (d : ℕ) (c : Content F m) :
    0 ≤ collProb P d c := by
  rw [collProb]
  split
  · positivity
  · exact zero_le_one

/-- **The collision count.** Two distinct line polynomials agree, along the shifted point's
parameter, at at most `collProb` of the shifts. -/
theorem card_collide_le (P : LinePres F m hm W) (d : ℕ) (c : Content F m)
    {f f' : LinePoly F (m * d)} (hne : f' ≠ f) :
    ((univ.filter fun t : F =>
        LinePoly.eval f' (P.param (Content.shiftAlong W P.dir t c))
          = LinePoly.eval f (P.param (Content.shiftAlong W P.dir t c))).card : ℝ)
      ≤ collProb P d c * (Fintype.card F : ℝ) := by
  classical
  have hF : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [collProb]
  split
  · rename_i hdeg
    rw [div_mul_cancel₀ _ hF]
    have hset : (univ.filter fun t : F =>
          LinePoly.eval f' (P.param (Content.shiftAlong W P.dir t c))
            = LinePoly.eval f (P.param (Content.shiftAlong W P.dir t c))).card
        = (univ.filter fun t : F =>
          LinePoly.eval f' (P.param c + t) = LinePoly.eval f (P.param c + t)).card := by
      refine congrArg Finset.card (Finset.filter_congr fun t _ => ?_)
      rw [P.param_shiftAlong hdeg t]
    rw [hset]
    have hcard : (univ.filter fun t : F =>
          LinePoly.eval f' (P.param c + t) = LinePoly.eval f (P.param c + t)).card
        = (univ.filter fun t : F => LinePoly.eval f' t = LinePoly.eval f t).card := by
      refine Finset.card_equiv (Equiv.addLeft (P.param c)) fun t => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addLeft]
    rw [hcard]
    exact_mod_cast card_agree_linePoly_le hne
  · rw [one_mul]
    exact_mod_cast le_trans (Finset.card_filter_le _ _) (le_of_eq Finset.card_univ)

end Pres

/-! ## The two sides, uniformly

Both sides of the pairs-of-lines lemma are proved by the same argument, so the side is a parameter
and the `(X, Z)` outcome pair is read through it. -/

section Sides

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- The value of an `(X, Z)` outcome pair on side `W`. -/
def valOf (W : Bas) (p : F × F) : F :=
  match W with
  | .X => p.1
  | .Z => p.2

/-- Reading an `(X, Z)` outcome pair as (this side, the other side). -/
def pairEquiv (W : Bas) : F × F ≃ F × F :=
  match W with
  | .X => Equiv.refl _
  | .Z => Equiv.prodComm F F

@[simp] theorem valOf_pairEquiv (W : Bas) (r : F × F) : valOf W (pairEquiv W r) = r.1 := by
  cases W <;> rfl

@[simp] theorem valOf_other_pairEquiv (W : Bas) (r : F × F) :
    valOf W.other (pairEquiv W r) = r.2 := by
  cases W <;> rfl

end Sides

/-! ## The hypotheses of the pasting lemma, at the line measurements -/

section Pairs

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ} {ε : ℝ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}

@[simp] theorem aPres_ty (hm : m ∣ Fintype.card F) (W : Bas) :
    (aPres (F := F) (m := m) hm W).ty = .aline W := rfl

@[simp] theorem aPres_base (hm : m ∣ Fintype.card F) (W : Bas) :
    (aPres (F := F) (m := m) hm W).base = abaseOf hm W := rfl

@[simp] theorem aPres_dir (hm : m ∣ Fintype.card F) (W : Bas) :
    (aPres (F := F) (m := m) hm W).dir = dirOf hm := rfl

@[simp] theorem dPres_ty (hm : m ∣ Fintype.card F) (W : Bas) :
    (dPres (F := F) (m := m) hm W).ty = .dline W := rfl

@[simp] theorem dPres_base (hm : m ∣ Fintype.card F) (W : Bas) :
    (dPres (F := F) (m := m) hm W).base = dbaseOf hm W := rfl

@[simp] theorem dPres_dir (hm : m ∣ Fintype.card F) (W : Bas) :
    (dPres (F := F) (m := m) hm W).dir = ddirOf hm := rfl

/-- **Bob's point measurement against Bob's own line measurement.** Alice's point measurement is the
bridge: her copy is consistent with both --- with Bob's point measurement by the expansion stage's
self-consistency, with Bob's line measurement by its consistency with the points --- so a triangle
inequality gives the same-side bound at four times the input. -/
theorem sum_content_normSq_point_line_le (W : Bas) (P : LinePres F m hm W)
    (hpt : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
          (hatMats MB W (c.pt W) a) ≤ 172 * ε)
    (hline : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
          (P.lineEvalMats d MB c a) ≤ 172 * ε) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        ‖stateVecB (hatVec (F := F) (m := m) ψ)
          (hatMats MB W (c.pt W) a - P.lineEvalMats d MB c a)‖ ^ 2
      ≤ 2 * (172 * ε) + 2 * (172 * ε) := by
  classical
  have hstep : ∀ c : Content F m, (∑ a : F, ‖stateVecB (hatVec (F := F) (m := m) ψ)
        (hatMats MB W (c.pt W) a - P.lineEvalMats d MB c a)‖ ^ 2)
      ≤ 2 * (∑ a : F, xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
            (hatMats MB W (c.pt W) a))
        + 2 * ∑ a : F, xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
            (P.lineEvalMats d MB c a) := by
    intro c
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ =>
      normSq_stateVecB_sub_le (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a) _ _
  calc ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
          ‖stateVecB (hatVec (F := F) (m := m) ψ)
            (hatMats MB W (c.pt W) a - P.lineEvalMats d MB c a)‖ ^ 2
      ≤ ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
          (2 * (∑ a : F, xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
              (hatMats MB W (c.pt W) a))
            + 2 * ∑ a : F, xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
              (P.lineEvalMats d MB c a)) :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hstep c) (by positivity)
    _ = 2 * (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
            xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
              (hatMats MB W (c.pt W) a))
          + 2 * ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
            xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
              (P.lineEvalMats d MB c a) := by
        rw [sum_weighted_add, sum_weighted_const_mul, sum_weighted_const_mul]
    _ ≤ 2 * (172 * ε) + 2 * (172 * ε) := by linarith

/-- The state the dilated joint point measurement acts on: the expanded state with one
`F_q x F_q` register adjoined to each party. -/
def extHat (ψ : dA × dB → ℂ) :
    ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ :=
  extVec2 (hatVec (F := F) (m := m) ψ) ((0 : F), (0 : F)) ((0 : F), (0 : F))

/-- **The marginal step at the QLD point measurements**, at one content: the joint measurement's
`W`-marginal is consistent with Bob's `W`-point measurement. -/
theorem sum_xSqNorm_marg_point_le (W : Bas) (c : Content F m)
    {QA : Content F m → F × F → Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ}
    (hQA : ∀ c, IsPVM (QA c))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) :
    (∑ a : F, xSqNorm (extHat (m := m) ψ) (∑ q : F, QA c (pairEquiv W (a, q)))
        (aOp (hatMats MB W (c.pt W) a)))
      ≤ 10 * ∑ p : F × F, xSqNorm (extHat (m := m) ψ) (QA c p)
          (aOp (hatMats MB W.other (c.pt W.other) (valOf W.other p)
            * hatMats MB W (c.pt W) (valOf W p))) := by
  classical
  refine le_trans (sum_xSqNorm_marg_le' (ψ := extHat (m := m) ψ)
    (Q := fun r : F × F => QA c (pairEquiv W r))
    (Z := fun q : F => (aOp (hatMats MB W.other (c.pt W.other) q)
      : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ))
    (fun a : F => (aOp (hatMats MB W (c.pt W) a)
      : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ))
    ((hQA c).comp_equiv (pairEquiv W))
    (IsPVM.aOp (isPVM_hatMats hprojB W.other (c.pt W.other)))) (le_of_eq ?_)
  refine congrArg (fun t : ℝ => 10 * t) ?_
  refine Fintype.sum_equiv (pairEquiv W) _ _ fun r => ?_
  rw [← aOp_mul, valOf_pairEquiv, valOf_other_pairEquiv]

/-- **Replacing Bob's point measurement by his line measurement**, at one content: the transport of
the same-side deviation to the enlarged space, and one triangle inequality. -/
theorem sum_xSqNorm_marg_line_le_aux (W : Bas) (P : LinePres F m hm W) (c : Content F m)
    {QA : Content F m → F × F → Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ} :
    (∑ a : F, xSqNorm (extHat (m := m) ψ) (∑ q : F, QA c (pairEquiv W (a, q)))
        (aOp (P.lineEvalMats d MB c a)))
      ≤ 2 * (∑ a : F, xSqNorm (extHat (m := m) ψ) (∑ q : F, QA c (pairEquiv W (a, q)))
          (aOp (hatMats MB W (c.pt W) a)))
        + 2 * ∑ a : F, ‖stateVecB (hatVec (F := F) (m := m) ψ)
          (hatMats MB W (c.pt W) a - P.lineEvalMats d MB c a)‖ ^ 2 := by
  classical
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  refine le_trans (xSqNorm_le_of_stateVecB (extHat (m := m) ψ)
    (∑ q : F, QA c (pairEquiv W (a, q))) (aOp (hatMats MB W (c.pt W) a))
    (aOp (P.lineEvalMats d MB c a))) (le_of_eq ?_)
  rw [← aOp_sub, extHat, normSq_stateVecB_extVec2_aOp]

/-- **The joint measurement's marginal against the line measurement**, on average over the
content. -/
theorem sum_content_marg_line_le (W : Bas) (P : LinePres F m hm W) {κ η : ℝ}
    {QA : Content F m → F × F → Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ}
    (hQA : ∀ c, IsPVM (QA c))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
    (hord : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
        xSqNorm (extHat (m := m) ψ) (QA c p)
          (aOp (hatMats MB W.other (c.pt W.other) (valOf W.other p)
            * hatMats MB W (c.pt W) (valOf W p))) ≤ κ)
    (hptline : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        ‖stateVecB (hatVec (F := F) (m := m) ψ)
          (hatMats MB W (c.pt W) a - P.lineEvalMats d MB c a)‖ ^ 2 ≤ η) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (extHat (m := m) ψ) (∑ q : F, QA c (pairEquiv W (a, q)))
          (aOp (P.lineEvalMats d MB c a))
      ≤ 2 * (10 * κ) + 2 * η := by
  classical
  have h1 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (extHat (m := m) ψ) (∑ q : F, QA c (pairEquiv W (a, q)))
          (aOp (hatMats MB W (c.pt W) a))
      ≤ 10 * κ := by
    refine le_trans (Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
      (sum_xSqNorm_marg_point_le W c hQA hprojB) (by positivity)) ?_
    rw [sum_weighted_const_mul]
    linarith
  refine le_trans (Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
    (sum_xSqNorm_marg_line_le_aux W P c (QA := QA)) (by positivity)) ?_
  rw [sum_weighted_add, sum_weighted_const_mul, sum_weighted_const_mul]
  linarith

end Pairs

end MIPRE.QLD

end
