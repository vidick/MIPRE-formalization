/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Combined
public import MIPRE.Foundations.Pasting

@[expose] public section

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
* **The extended space.** The joint measurement lives on each player's algebra enlarged by one
  dilation register (`extHat`, the model `BipartiteModel.jointModel` of
  `MIPRE/Background/QLD/Combined.lean`); the line measurements live on the unenlarged ones, and
  enter the enlarged model with the register inert (`smulKron X 1`), which changes none of their
  estimates (`BipartiteModel.jointModel_xSqNorm_smulKron_one`).
* **The probe.** The pasting lemma's collision term needs the point to be uniform on its line once
  the line is fixed. Here the content determines both, so the factorization is produced by
  *shifting the point along the direction the content itself carries*: for each fixed shift the map
  is a bijection of contents, the line data is invariant under it, and the parameter of the point
  moves by exactly the shift.

## In a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The strategies are families of
projective measurements `PA`, `PB` in the players' algebras, the expanded model is
`M.reg (Anc F m)`, and the line measurements (`LinePres.lineMats`) and the pasted line measurement
(`pasteLine`) are elements of the register's matrices over a player's algebra. The pasting lemma is
the generic one (`BipartiteModel.one_sub_sum_bornProb_pasteJ_le`), applied on the model of the
dilated joint measurement of `combined_points_dilated`, which must be projective. The dilation is
kept inside the proofs of the consequences from the game: the pasted line measurement does not see
the dilation register and the dilated measurement compresses to the sandwich
`M-hat^{Z,z}_b M-hat^{X,x}_a M-hat^{Z,z}_b` (`BipartiteModel.jointModel_bornProb`), so
`pairs_of_lines_of_items` and `qld_pairs_of_lines` are agreement bounds of the **sandwich**
against the pasted line measurement in the expanded model `M.reg (Anc F m)`. Every constant is the
matrix statement's. On a unit vector `ψ : dA × dB → ℂ` the statements are read at the
tensor-product model `BipartiteModel.tensor ψ` with the families `POVM.toIn`.
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

/-- Adding a vector to the content's diagonal direction, leaving everything else alone. The other
shift the argument needs: it is what makes a *degenerate* diagonal line rare. -/
def Content.shiftV (w : Point F m) (c : Content F m) : Content F m := { c with v := c.v + w }

@[simp] theorem Content.shiftV_s (w : Point F m) (c : Content F m) :
    (Content.shiftV w c).s = c.s := rfl

@[simp] theorem Content.shiftV_v (w : Point F m) (c : Content F m) :
    (Content.shiftV w c).v = c.v + w := rfl

@[simp] theorem Content.shiftV_zero (c : Content F m) : Content.shiftV 0 c = c := by
  rw [Content.shiftV, add_zero]

theorem Content.shiftV_shiftV (w w' : Point F m) (c : Content F m) :
    Content.shiftV w' (Content.shiftV w c) = Content.shiftV (w + w') c := by
  rw [Content.shiftV, Content.shiftV, Content.shiftV]
  congr 1
  rw [add_assoc]

/-- **For each fixed shift, shifting is a bijection of contents.** Its inverse shifts by `-t`,
which is where the invariance of the direction is used. -/
theorem bijective_shift {α : Type*} {V : Type*} [AddCommGroup V] [Module F V]
    {sh : V → α → α} (hzero : ∀ a, sh 0 a = a)
    (hadd : ∀ (w w' : V) (a : α), sh w' (sh w a) = sh (w + w') a)
    {dir : α → V} (hdir : ∀ (a : α) (w : V), dir (sh w a) = dir a) (t : F) :
    Function.Bijective fun a => sh (t • dir a) a := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun a => sh ((-t) • dir a) a, fun a => ?_, fun a => ?_⟩
  · show sh ((-t) • dir (sh (t • dir a) a)) (sh (t • dir a) a) = a
    rw [hdir, hadd, show t • dir a + (-t) • dir a = 0 from by module, hzero]
  · show sh (t • dir (sh ((-t) • dir a) a)) (sh ((-t) • dir a) a) = a
    rw [hdir, hadd, show (-t) • dir a + t • dir a = 0 from by module, hzero]

/-- **The change of variables**, for an arbitrary finite sample space: averaging a quantity is
averaging it over (sample, shift) pairs with the shift applied. Nothing here is about contents --- a
finite sample space, a shift action on it, and a direction the shift does not move --- which is what
lets the same device serve a product of two independent line-point laws. -/
theorem sum_shift_gen {α : Type*} [Fintype α] {V : Type*} [AddCommGroup V] [Module F V]
    {sh : V → α → α} (hzero : ∀ a, sh 0 a = a)
    (hadd : ∀ (w w' : V) (a : α), sh w' (sh w a) = sh (w + w') a)
    {dir : α → V} (hdir : ∀ (a : α) (w : V), dir (sh w a) = dir a) (g : α → ℝ) :
    ∑ i : α × F, ((Fintype.card α : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * g (sh (i.2 • dir i.1) i.1)
      = ∑ a : α, (Fintype.card α : ℝ)⁻¹ * g a := by
  classical
  have hF : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← sum_prod_eq fun (a : α) (t : F) =>
    ((Fintype.card α : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) * g (sh (t • dir a) a), Finset.sum_comm]
  have hstep : ∀ t : F, ∑ a : α, ((Fintype.card α : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * g (sh (t • dir a) a)
      = (Fintype.card F : ℝ)⁻¹ * ∑ a : α, (Fintype.card α : ℝ)⁻¹ * g a := by
    intro t
    rw [Finset.mul_sum]
    refine Fintype.sum_bijective (fun a => sh (t • dir a) a)
      (bijective_shift hzero hadd hdir t) _ _ fun a => ?_
    ring
  rw [Finset.sum_congr rfl fun t (_ : t ∈ univ) => hstep t, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hF, one_mul]

/-- The change of variables at the content distribution: the instance of `sum_shift_gen` the Pauli
basis test's own question distribution gives. -/
theorem bijective_shift_gen {sh : Point F m → Content F m → Content F m}
    (hzero : ∀ c, sh 0 c = c)
    (hadd : ∀ (w w' : Point F m) (c : Content F m), sh w' (sh w c) = sh (w + w') c)
    {dir : Content F m → Point F m}
    (hdir : ∀ (c : Content F m) (w : Point F m), dir (sh w c) = dir c) (t : F) :
    Function.Bijective fun c => sh (t • dir c) c :=
  bijective_shift hzero hadd hdir t

instance : Nonempty (Content F m) := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

theorem card_content_pos : 0 < Fintype.card (Content F m) :=
  Fintype.card_pos_iff.mpr ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- **The change of variables.** Averaging a quantity over contents is averaging it over
`(content, shift)` pairs with the shift applied --- the content average is the product of the line
average and the uniform average along the direction, without any quotient being formed. -/
theorem sum_content_shift_gen {sh : Point F m → Content F m → Content F m}
    (hzero : ∀ c, sh 0 c = c)
    (hadd : ∀ (w w' : Point F m) (c : Content F m), sh w' (sh w c) = sh (w + w') c)
    {dir : Content F m → Point F m}
    (hdir : ∀ (c : Content F m) (w : Point F m), dir (sh w c) = dir c) (g : Content F m → ℝ) :
    ∑ i : Content F m × F, ((Fintype.card (Content F m) : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * g (sh (i.2 • dir i.1) i.1)
      = ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * g c :=
  sum_shift_gen hzero hadd hdir g

/-- The change of variables for a shift of the `W`-point. -/
theorem sum_content_shiftAlong (W : Bas) {dir : Content F m → Point F m}
    (hdir : ∀ (c : Content F m) (w : Point F m), dir (Content.shiftPt W w c) = dir c)
    (g : Content F m → ℝ) :
    ∑ i : Content F m × F, ((Fintype.card (Content F m) : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * g (Content.shiftAlong W dir i.2 i.1)
      = ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * g c :=
  sum_content_shift_gen (Content.shiftPt_zero W) (Content.shiftPt_shiftPt W) hdir g

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
theorem hatLinePOVM_congr {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    [PartialOrder R] [StarOrderedRing R] [StarProper R] {n : ℕ}
    (hm : m ∣ Fintype.card F) (S : Question F m → POVMIn (Answer F m d) R) (W : Bas) (ty : Ty)
    (base dir : Content F m → Point F m) {c c' : Content F m}
    (hq : c.question hm ty = c'.question hm ty) (hb : base c = base c') (hd : dir c = dir c') :
    hatLinePOVM n hm S W ty base dir c = hatLinePOVM n hm S W ty base dir c' := by
  have hsyn : synLinePOVM n W (base c) (dir c) = synLinePOVM n W (base c') (dir c') := by
    rw [hb, hd]
  rw [hatLinePOVM, hatLinePOVM, lineAnsPOVM, lineAnsPOVM, hq,
    kronIn_congr _ hsyn _ (isPVM_synLinePOVM n W _ _)]

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

section Ops

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
  [StarOrderedRing R] [StarProper R]

/-- The expanded line measurement the presentation carries, as a family of elements of the
register's matrices over the player's algebra. -/
def lineMats (P : LinePres F m hm W) (d : ℕ) (S : Question F m → POVMIn (Answer F m d) R)
    (c : Content F m) : LinePoly F (m * d) → Matrix (Anc F m) (Anc F m) R :=
  (hatLinePOVM (m * d) hm S W P.ty P.base P.dir c).op

/-- The same measurement, coarse-grained by evaluation at the sampled point's parameter. -/
def lineEvalMats (P : LinePres F m hm W) (d : ℕ) (S : Question F m → POVMIn (Answer F m d) R)
    (c : Content F m) : F → Matrix (Anc F m) (Anc F m) R :=
  ((hatLinePOVM (m * d) hm S W P.ty P.base P.dir c).map
    fun f => LinePoly.eval f (P.param c)).op

theorem isPVM_lineMats (P : LinePres F m hm W) (d : ℕ)
    {S : Question F m → POVMIn (Answer F m d) R} (hS : ∀ q, IsPVMIn (S q).op)
    (c : Content F m) : IsPVMIn (P.lineMats d S c) :=
  isPVM_hatLinePOVM (hS (c.question hm P.ty))

theorem isPVM_lineEvalMats (P : LinePres F m hm W) (d : ℕ)
    {S : Question F m → POVMIn (Answer F m d) R} (hS : ∀ q, IsPVMIn (S q).op)
    (c : Content F m) : IsPVMIn (P.lineEvalMats d S c) :=
  POVMIn.isPVMIn_map (isPVM_hatLinePOVM (hS (c.question hm P.ty))) _

/-- The coarse-graining, as a fibre sum --- the shape the pasting lemma states its hypotheses
in. -/
theorem lineEvalMats_eq_fibSum (P : LinePres F m hm W) (d : ℕ)
    (S : Question F m → POVMIn (Answer F m d) R) (c : Content F m) (a : F) :
    P.lineEvalMats d S c a
      = fibSumIn (P.lineMats d S c) (fun f => LinePoly.eval f (P.param c)) a :=
  POVMIn.map_op _ _ _

/-- **The line measurement is invariant under the shift**, the presentation's three invariances
being exactly what the measurement reads. -/
theorem lineMats_shiftAlong (P : LinePres F m hm W) (d : ℕ)
    (S : Question F m → POVMIn (Answer F m d) R) (c : Content F m) (t : F) :
    P.lineMats d S (Content.shiftAlong W P.dir t c) = P.lineMats d S c :=
  congrArg POVMIn.op
    (hatLinePOVM_congr hm S W P.ty P.base P.dir (P.question_shift c t) (P.base_shift c t)
      (P.dir_shift _ _))

/-- The same, for a shift of the other side's point. -/
theorem lineMats_shiftPt_other (P : LinePres F m hm W) (d : ℕ)
    (S : Question F m → POVMIn (Answer F m d) R) (c : Content F m) (w : Point F m) :
    P.lineMats d S (Content.shiftPt W.other w c) = P.lineMats d S c :=
  congrArg POVMIn.op
    (hatLinePOVM_congr hm S W P.ty P.base P.dir (P.question_shift_other c w)
      (P.base_shift_other c w) (P.dir_shift_other c w))

end Ops

theorem param_shiftPt_other (P : LinePres F m hm W) (c : Content F m) (w : Point F m) :
    P.param (Content.shiftPt W.other w c) = P.param c := by
  rw [param, param, P.base_shift_other, P.dir_shift_other, Content.shiftPt_other_pt]

theorem lineEvalMats_shiftPt_other {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    [StarModule ℂ R] [PartialOrder R] [StarOrderedRing R] [StarProper R]
    (P : LinePres F m hm W) (d : ℕ) (S : Question F m → POVMIn (Answer F m d) R)
    (c : Content F m) (w : Point F m) :
    P.lineEvalMats d S (Content.shiftPt W.other w c) = P.lineEvalMats d S c := by
  have hQ : hatLinePOVM (m * d) hm S W P.ty P.base P.dir (Content.shiftPt W.other w c)
      = hatLinePOVM (m * d) hm S W P.ty P.base P.dir c :=
    hatLinePOVM_congr hm S W P.ty P.base P.dir (P.question_shift_other c w)
      (P.base_shift_other c w) (P.dir_shift_other c w)
  have hp : P.param (Content.shiftPt W.other w c) = P.param c := P.param_shiftPt_other c w
  rw [lineEvalMats, lineEvalMats, hQ, hp]

end LinePres

/-! ### The four presentations, and the collision count -/

variable {hm : m ∣ Fintype.card F} {W : Bas}

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

/-! ## Operators with an inert register

The joint point measurement of `lem:qld-combined-points` lives on each player's algebra enlarged
by one dilation register; the line measurements do not see that register, so they enter the
enlarged model as `X ⊗ 1` (`smulKron X 1`). Three facts about such operators are all that is
needed: projectivity survives, coarse-graining commutes with the embedding, and so does the pasted
sandwich. -/

section Inert

variable {R : Type*} [Ring R] [Algebra ℂ R] {α : Type*} [Fintype α] [DecidableEq α]

/-- **A projective measurement with an inert register is projective.** -/
theorem isPVMIn_smulKron_one_right [StarRing R] {ι : Type*} [Fintype ι] {P : ι → R}
    (hP : IsPVMIn P) : IsPVMIn fun i => smulKron (P i) (1 : Matrix α α ℂ) where
  star_eq i := by rw [star_smulKron_one, hP.star_eq]
  idem i := by rw [smulKron_mul, hP.idem, Matrix.one_mul]
  sum_eq_one := by rw [← smulKron_sum_left, hP.sum_eq_one, smulKron_one_one]
  orthogonal hij := by rw [smulKron_mul, hP.orthogonal hij, smulKron_zero_left]

/-- Coarse-graining commutes with adjoining an inert register. -/
theorem fibSum_aOp {ι κ : Type*} [Fintype ι] [DecidableEq κ] (G : ι → R) (e : ι → κ) (k : κ) :
    fibSumIn (fun i => smulKron (G i) (1 : Matrix α α ℂ)) e k = smulKron (fibSumIn G e k) 1 := by
  rw [fibSumIn, fibSumIn, smulKron_sum_left]

/-- The pasted sandwich of two families with an inert register is the pasted sandwich of the
families, with the register adjoined. -/
theorem pasteJ_smulKron_one {R1 R2 K : Type*} [DecidableEq R2] [Fintype K] (Rf : R1 → R)
    (G : K → R) (e : K → R2) (p : R1 × R2) :
    pasteJ (fun a => smulKron (Rf a) (1 : Matrix α α ℂ)) (fun g => smulKron (G g) 1) e p
      = smulKron (pasteJ Rf G e p) 1 := by
  rw [pasteJ, pasteJ, smulKron_sum_left]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [smulKron_mul, smulKron_mul, Matrix.one_mul, Matrix.one_mul]

end Inert

/-- **A cross-party deviation through the second player's state norm**, in any bipartite model:
the model form of the matrix `xSqNorm_le_of_stateVecB`. -/
theorem xSqNorm_le_two_mul_add {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞']
    [Ring 𝒜'] [StarRing 𝒜'] [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']
    (N : BipartiteModel 𝒞' 𝒜' ℬ') (a : 𝒜') (b₁ b₂ : ℬ') :
    N.xSqNorm a b₂ ≤ 2 * N.xSqNorm a b₁ + 2 * N.swap.stateSqNorm (b₁ - b₂) := by
  have htri : N.xNorm a b₂ ≤ N.xNorm a b₁ + N.swap.stateNorm (b₁ - b₂) := by
    show N.snorm (N.πA a - N.πB b₂) ≤ N.snorm (N.πA a - N.πB b₁) + N.snorm (N.πB (b₁ - b₂))
    rw [show N.πA a - N.πB b₂ = (N.πA a - N.πB b₁) + N.πB (b₁ - b₂) from by
      rw [map_sub]; abel]
    exact N.snorm_add_le _ _
  have h0 := N.xNorm_nonneg a b₂
  have h1 := N.xNorm_nonneg a b₁
  have h2 := N.swap.stateNorm_nonneg (b₁ - b₂)
  rw [BipartiteModel.xSqNorm_eq_sq, BipartiteModel.xSqNorm_eq_sq]
  show N.xNorm a b₂ ^ 2 ≤ 2 * N.xNorm a b₁ ^ 2 + 2 * N.swap.stateNorm (b₁ - b₂) ^ 2
  nlinarith [sq_nonneg (N.xNorm a b₁ - N.swap.stateNorm (b₁ - b₂))]

/-! ## The model of the dilated joint measurement -/

section ExtHat

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} {𝒞 𝒜 ℬ : Type*} [Ring 𝒞]
  [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ]
  [Algebra ℂ ℬ]

/-- **The model the dilated joint point measurement acts on**: the expanded model
`M.reg (Anc F m)` with one dilation register `(F × F) ⊕ (F × F)` adjoined to each player, in the
basis state `|inl (0, 0)⟩` (`BipartiteModel.jointModel`). The model form of the matrix route's
twice-extended expanded state. -/
abbrev extHat (M : BipartiteModel 𝒞 𝒜 ℬ) :=
  (M.reg (Anc F m)).jointModel ((0 : F), (0 : F))

end ExtHat

/-! ## The hypotheses of the pasting lemma, at the line measurements -/

section Pairs

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {ε : ℝ} {PA : Question F m → POVMIn (Answer F m d) 𝒜}
  {PB : Question F m → POVMIn (Answer F m d) ℬ}

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
theorem sum_content_normSq_point_line_le [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
    [StarProper ℬ] (W : Bas) (P : LinePres F m hm W)
    (hpt : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        (M.reg (Anc F m)).xSqNorm (hatMats PA W (c.pt W) a) (hatMats PB W (c.pt W) a)
          ≤ 172 * ε)
    (hline : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        (M.reg (Anc F m)).xSqNorm (hatMats PA W (c.pt W) a) (P.lineEvalMats d PB c a)
          ≤ 172 * ε) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        (M.reg (Anc F m)).swap.stateSqNorm (hatMats PB W (c.pt W) a - P.lineEvalMats d PB c a)
      ≤ 2 * (172 * ε) + 2 * (172 * ε) := by
  classical
  have hstep : ∀ c : Content F m, (∑ a : F, (M.reg (Anc F m)).swap.stateSqNorm
        (hatMats PB W (c.pt W) a - P.lineEvalMats d PB c a))
      ≤ 2 * (∑ a : F, (M.reg (Anc F m)).xSqNorm (hatMats PA W (c.pt W) a)
            (hatMats PB W (c.pt W) a))
        + 2 * ∑ a : F, (M.reg (Anc F m)).xSqNorm (hatMats PA W (c.pt W) a)
            (P.lineEvalMats d PB c a) := by
    intro c
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ =>
      (M.reg (Anc F m)).swap_stateSqNorm_sub_le (hatMats PA W (c.pt W) a) _ _
  calc ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
          (M.reg (Anc F m)).swap.stateSqNorm
            (hatMats PB W (c.pt W) a - P.lineEvalMats d PB c a)
      ≤ ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
          (2 * (∑ a : F, (M.reg (Anc F m)).xSqNorm (hatMats PA W (c.pt W) a)
              (hatMats PB W (c.pt W) a))
            + 2 * ∑ a : F, (M.reg (Anc F m)).xSqNorm (hatMats PA W (c.pt W) a)
              (P.lineEvalMats d PB c a)) :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hstep c) (by positivity)
    _ = 2 * (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
            (M.reg (Anc F m)).xSqNorm (hatMats PA W (c.pt W) a) (hatMats PB W (c.pt W) a))
          + 2 * ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
            (M.reg (Anc F m)).xSqNorm (hatMats PA W (c.pt W) a)
              (P.lineEvalMats d PB c a) := by
        rw [sum_weighted_add, sum_weighted_const_mul, sum_weighted_const_mul]
    _ ≤ 2 * (172 * ε) + 2 * (172 * ε) := by linarith

/-- **The marginal step at the QLD point measurements**, at one content: the joint measurement's
`W`-marginal is consistent with Bob's `W`-point measurement, on the model of the dilation, where
Bob's operators carry an inert dilation register. -/
theorem sum_xSqNorm_marg_point_le [StarModule ℂ ℬ] [StarProper ℬ] (W : Bas) (c : Content F m)
    {QA : Content F m → F × F →
      Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) (Matrix (Anc F m) (Anc F m) 𝒜)}
    (hQA : ∀ c, IsPVMIn (QA c)) (hPB : ∀ q, IsPVMIn (PB q).op) :
    (∑ a : F, (extHat (F := F) (m := m) M).xSqNorm (∑ q : F, QA c (pairEquiv W (a, q)))
        (smulKron (hatMats PB W (c.pt W) a) 1))
      ≤ 10 * ∑ p : F × F, (extHat (F := F) (m := m) M).xSqNorm (QA c p)
          (smulKron (hatMats PB W.other (c.pt W.other) (valOf W.other p)
            * hatMats PB W (c.pt W) (valOf W p)) 1) := by
  classical
  refine le_trans ((extHat (F := F) (m := m) M).sum_xSqNorm_marg_le'
    (Q := fun r : F × F => QA c (pairEquiv W r))
    (Z := fun q : F => smulKron (hatMats PB W.other (c.pt W.other) q)
      (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
    (fun a : F => smulKron (hatMats PB W (c.pt W) a)
      (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
    ((hQA c).comp_equiv (pairEquiv W))
    (isPVMIn_smulKron_one_right (isPVM_hatMats hPB W.other (c.pt W.other)))) (le_of_eq ?_)
  refine congrArg (fun t : ℝ => 10 * t) ?_
  refine Fintype.sum_equiv (pairEquiv W) _ _ fun r => ?_
  rw [smulKron_mul, Matrix.one_mul, valOf_pairEquiv, valOf_other_pairEquiv]

/-- **Replacing Bob's point measurement by his line measurement**, at one content: one triangle
inequality on the model of the dilation, and the same-side deviation read back on the expanded
model, the dilation register being inert. -/
theorem sum_xSqNorm_marg_line_le_aux [StarModule ℂ ℬ] [StarProper ℬ] (W : Bas)
    (P : LinePres F m hm W) (c : Content F m)
    {QA : Content F m → F × F →
      Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) (Matrix (Anc F m) (Anc F m) 𝒜)} :
    (∑ a : F, (extHat (F := F) (m := m) M).xSqNorm (∑ q : F, QA c (pairEquiv W (a, q)))
        (smulKron (P.lineEvalMats d PB c a) 1))
      ≤ 2 * (∑ a : F, (extHat (F := F) (m := m) M).xSqNorm
            (∑ q : F, QA c (pairEquiv W (a, q))) (smulKron (hatMats PB W (c.pt W) a) 1))
        + 2 * ∑ a : F, (M.reg (Anc F m)).swap.stateSqNorm
          (hatMats PB W (c.pt W) a - P.lineEvalMats d PB c a) := by
  classical
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  refine le_trans (xSqNorm_le_two_mul_add (extHat (F := F) (m := m) M)
    (∑ q : F, QA c (pairEquiv W (a, q))) (smulKron (hatMats PB W (c.pt W) a) 1)
    (smulKron (P.lineEvalMats d PB c a) 1)) (le_of_eq ?_)
  rw [smulKron_sub_left, BipartiteModel.jointModel_swap_stateSqNorm_smulKron_one]

/-- **The joint measurement's marginal against the line measurement**, on average over the
content. -/
theorem sum_content_marg_line_le [StarModule ℂ ℬ] [StarProper ℬ] (W : Bas) (P : LinePres F m hm W)
    {κ η : ℝ}
    {QA : Content F m → F × F →
      Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) (Matrix (Anc F m) (Anc F m) 𝒜)}
    (hQA : ∀ c, IsPVMIn (QA c)) (hPB : ∀ q, IsPVMIn (PB q).op)
    (hord : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
        (extHat (F := F) (m := m) M).xSqNorm (QA c p)
          (smulKron (hatMats PB W.other (c.pt W.other) (valOf W.other p)
            * hatMats PB W (c.pt W) (valOf W p)) 1) ≤ κ)
    (hptline : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        (M.reg (Anc F m)).swap.stateSqNorm (hatMats PB W (c.pt W) a - P.lineEvalMats d PB c a)
          ≤ η) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        (extHat (F := F) (m := m) M).xSqNorm (∑ q : F, QA c (pairEquiv W (a, q)))
          (smulKron (P.lineEvalMats d PB c a) 1)
      ≤ 2 * (10 * κ) + 2 * η := by
  classical
  have h1 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        (extHat (F := F) (m := m) M).xSqNorm (∑ q : F, QA c (pairEquiv W (a, q)))
          (smulKron (hatMats PB W (c.pt W) a) 1)
      ≤ 10 * κ := by
    refine le_trans (Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
      (sum_xSqNorm_marg_point_le W c hQA hPB) (by positivity)) ?_
    rw [sum_weighted_const_mul]
    linarith
  refine le_trans (Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
    (sum_xSqNorm_marg_line_le_aux W P c (QA := QA)) (by positivity)) ?_
  rw [sum_weighted_add, sum_weighted_const_mul, sum_weighted_const_mul]
  linarith

/-! ## The pasted line measurement -/

section Paste

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
  [StarOrderedRing R] [StarProper R]

/-- **The pasted line measurement** `T^{l_X, l_Z}_{f_X, f_Z}`: a player's `X`-line measurement
sandwiching the same player's `Z`-line measurement, in the register's matrices over the player's
algebra.

The two lines are read off **two** contents, one per side. On the Pauli basis test's own question
distribution they are the same content, which is how `lem:qld-pairs-of-lines` uses this; the
combining stage needs them independent, and then they are not. Nothing in the pasting lemma forces
them to agree --- none of its hypotheses involves both lines --- which is why one definition serves
both. -/
def pasteLine (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (d : ℕ)
    (S : Question F m → POVMIn (Answer F m d) R) (cX cZ : Content F m)
    (q : LinePoly F (m * d) × LinePoly F (m * d)) : Matrix (Anc F m) (Anc F m) R :=
  PX.lineMats d S cX q.1 * PZ.lineMats d S cZ q.2 * PX.lineMats d S cX q.1

/-- **The pasted family, coarse-grained by the two evaluations, is the pasting lemma's sandwich.**
Only the distributivity of the sandwich over the inner family's fibre, and the regrouping of a pair
of fibres into a fibre of pairs. -/
theorem pasteJ_eq_pasteLine (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (d : ℕ)
    (S : Question F m → POVMIn (Answer F m d) R) (cX cZ : Content F m) (p : F × F) :
    pasteJ (PZ.lineEvalMats d S cZ) (PX.lineMats d S cX)
        (fun f => LinePoly.eval f (PX.param cX)) p
      = ∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
            LinePoly.eval q.1 (PX.param cX) = p.2 ∧ LinePoly.eval q.2 (PZ.param cZ) = p.1,
          pasteLine PX PZ d S cX cZ q := by
  classical
  rw [pasteJ]
  rw [show (univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
        LinePoly.eval q.1 (PX.param cX) = p.2 ∧ LinePoly.eval q.2 (PZ.param cZ) = p.1)
      = (univ.filter fun f : LinePoly F (m * d) => LinePoly.eval f (PX.param cX) = p.2)
        ×ˢ (univ.filter fun g : LinePoly F (m * d) => LinePoly.eval g (PZ.param cZ) = p.1) from by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product],
    Finset.sum_product]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [LinePres.lineEvalMats_eq_fibSum, fibSumIn, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [pasteLine]

end Paste

/-! ## The lemma -/

set_option maxHeartbeats 1600000 in
/-- **`lem:qld-pairs-of-lines`, over an arbitrary question distribution.** The sample space is any
finite nonempty `iota` carrying a content for each side --- `kX` presenting the `X` line, `kZ` the
`Z` line --- together with a shift that moves the `X` point and that both contents see as such.
Alice's joint point measurement, a projective measurement on the model of the dilation, agrees with
the pasted line measurement (with an inert dilation register), coarse-grained by evaluating each
line polynomial at the parameter of the point of its own side, up to
`delta/2 + sqrt(delta/2) + sqrt(32 delta + 4 sqrt(eta) + 2 eps_c)`.

The three inputs are the two marginal consistencies, the `X`-line measurement's cross-party
self-consistency at the fine level (on the expanded model, the dilation register being inert),
and the average collision probability of the `X`-side outcome map --- and the shift is what turns
the question distribution into the product the collision bound needs.

**Why two contents, and why nothing forces them to agree.** Each of the pasting lemma's hypotheses
involves *one* line and the two points; none involves both lines. So the `X` line may be read off
one content and the `Z` line off another, and the two need share nothing. At `kX = kZ = id` this is
`pairs_of_lines`, on the Pauli basis test's own distribution, where they are the same content and
the two lines are therefore dependent; at a pair of line-point data it is the product form
`lem:qld-padded-lines` needs, where they are independent. -/
theorem pairs_of_lines_gen [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (kX kZ : ι → Content F m)
    {sh : Point F m → ι → ι} (hzero : ∀ a, sh 0 a = a)
    (hadd : ∀ (w w' : Point F m) (a : ι), sh w' (sh w a) = sh (w + w') a)
    (hkX : ∀ (w : Point F m) (a : ι), kX (sh w a) = Content.shiftPt .X w (kX a))
    (hkZ : ∀ (w : Point F m) (a : ι), kZ (sh w a) = Content.shiftPt .X w (kZ a))
    {QA : ι → F × F →
      Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) (Matrix (Anc F m) (Anc F m) 𝒜)}
    (hQA : ∀ a, IsPVMIn (QA a)) (hM : ‖M.ψ‖ = 1)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op) {δ η εc : ℝ}
    (hmargX : ∑ a : ι, (Fintype.card ι : ℝ)⁻¹ * ∑ x : F,
        (extHat (F := F) (m := m) M).xSqNorm (∑ q : F, QA a (x, q))
          (smulKron (PX.lineEvalMats d PB (kX a) x) 1) ≤ δ)
    (hmargZ : ∑ a : ι, (Fintype.card ι : ℝ)⁻¹ * ∑ b : F,
        (extHat (F := F) (m := m) M).xSqNorm (∑ q : F, QA a (q, b))
          (smulKron (PZ.lineEvalMats d PB (kZ a) b) 1) ≤ δ)
    (hselfX : ∑ a : ι, (Fintype.card ι : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        (M.reg (Anc F m)).xSqNorm (PX.lineMats d PA (kX a) f) (PX.lineMats d PB (kX a) f) ≤ η)
    (hcoll : ∑ a : ι, (Fintype.card ι : ℝ)⁻¹ * collProb PX d (kX a) ≤ εc) :
    1 - ∑ a : ι, (Fintype.card ι : ℝ)⁻¹ * ∑ p : F × F,
        (extHat (F := F) (m := m) M).bornProb (QA a p)
          (smulKron (∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
              LinePoly.eval q.1 (PX.param (kX a)) = p.1
                ∧ LinePoly.eval q.2 (PZ.param (kZ a)) = p.2,
            pasteLine PX PZ d PB (kX a) (kZ a) q) 1)
      ≤ δ / 2 + Real.sqrt (δ / 2) + Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * εc) := by
  classical
  set N := extHat (F := F) (m := m) M with hN
  have hunit : ‖N.ψ‖ = 1 := by
    rw [hN, BipartiteModel.norm_jointModel_ψ]
    exact hatVec_unit hM
  have hι1 : ∑ _a : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  have hw0 : ∀ _i : ι × F, (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹ :=
    fun _ => by positivity
  have hw1 : ∑ _i : ι × F, (Fintype.card ι : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹ = 1 :=
    sum_prod_uniform_one (Y := F) hι1
  -- the shift, as the two contents see it
  have hdirI : ∀ (a : ι) (w : Point F m), PX.dir (kX (sh w a)) = PX.dir (kX a) := fun a w => by
    rw [hkX, PX.dir_shift]
  have hshX : ∀ (a : ι) (t : F),
      kX (sh (t • PX.dir (kX a)) a) = Content.shiftAlong .X PX.dir t (kX a) := fun a t => by
    rw [hkX, Content.shiftAlong_eq]
  -- the four families, and their projectivity
  have hA : ∀ i : ι × F, IsPVMIn fun r : F × F =>
      QA (sh (i.2 • PX.dir (kX i.1)) i.1) (r.2, r.1) := fun i =>
    (hQA _).comp_equiv (Equiv.prodComm F F)
  have hR : ∀ a : ι, IsPVMIn fun b : F => smulKron (PZ.lineEvalMats d PB (kZ a) b)
      (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ) := fun a =>
    isPVMIn_smulKron_one_right (PZ.isPVM_lineEvalMats d hPB (kZ a))
  have hG : ∀ a : ι, IsPVMIn fun f : LinePoly F (m * d) => smulKron (PX.lineMats d PB (kX a) f)
      (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ) := fun a =>
    isPVMIn_smulKron_one_right (PX.isPVM_lineMats d hPB (kX a))
  have hGa : ∀ a : ι, IsPVMIn fun f : LinePoly F (m * d) => smulKron (PX.lineMats d PA (kX a) f)
      (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ) := fun a =>
    isPVMIn_smulKron_one_right (PX.isPVM_lineMats d hPA (kX a))
  -- the `Z`-side marginal hypothesis
  have hP1 : ∑ i : ι × F,
        ((Fintype.card ι : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) * ∑ b : F,
          N.xSqNorm (∑ x : F, QA (sh (i.2 • PX.dir (kX i.1)) i.1) (x, b))
            (smulKron (PZ.lineEvalMats d PB (kZ i.1) b) 1) ≤ δ := by
    refine le_trans (le_of_eq ?_) hmargZ
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
      (sum_shift_gen (dir := fun a => PX.dir (kX a)) hzero hadd hdirI fun a => ∑ b : F,
        N.xSqNorm (∑ x : F, QA a (x, b)) (smulKron (PZ.lineEvalMats d PB (kZ a) b) 1))
    refine congrArg (fun t : ℝ => ((Fintype.card ι : ℝ)⁻¹
      * (Fintype.card F : ℝ)⁻¹) * t) (Finset.sum_congr rfl fun b _ => ?_)
    rw [hkZ,
      show PZ.lineEvalMats d PB (Content.shiftPt .X (i.2 • PX.dir (kX i.1)) (kZ i.1))
          = PZ.lineEvalMats d PB (kZ i.1) from
        PZ.lineEvalMats_shiftPt_other d PB (kZ i.1) (i.2 • PX.dir (kX i.1))]
  -- the `X`-side marginal hypothesis
  have hP2 : ∑ i : ι × F,
        ((Fintype.card ι : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) * ∑ x : F,
          N.xSqNorm (∑ b : F, QA (sh (i.2 • PX.dir (kX i.1)) i.1) (x, b))
            (fibSumIn (fun f : LinePoly F (m * d) => smulKron (PX.lineMats d PB (kX i.1) f)
                (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
              (fun f => LinePoly.eval f
                (PX.param (kX (sh (i.2 • PX.dir (kX i.1)) i.1)))) x) ≤ δ := by
    refine le_trans (le_of_eq ?_) hmargX
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
      (sum_shift_gen (dir := fun a => PX.dir (kX a)) hzero hadd hdirI fun a => ∑ x : F,
        N.xSqNorm (∑ q : F, QA a (x, q)) (smulKron (PX.lineEvalMats d PB (kX a) x) 1))
    refine congrArg (fun t : ℝ => ((Fintype.card ι : ℝ)⁻¹
      * (Fintype.card F : ℝ)⁻¹) * t) (Finset.sum_congr rfl fun x _ => ?_)
    rw [fibSum_aOp, hshX i.1 i.2, ← PX.lineMats_shiftAlong d PB (kX i.1) i.2,
      ← PX.lineEvalMats_eq_fibSum d PB (Content.shiftAlong .X PX.dir i.2 (kX i.1)) x]
  -- the fine self-consistency, the dilation register being inert
  have hP4 : ∑ i : ι × F,
        ((Fintype.card ι : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
          ∑ f : LinePoly F (m * d), N.xSqNorm
            (smulKron (PX.lineMats d PA (kX i.1) f)
              (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
            (smulKron (PX.lineMats d PB (kX i.1) f) 1) ≤ η := by
    refine le_trans (le_of_eq ?_) hselfX
    refine Eq.trans (sum_prod_uniform (Y := F) (fun _ => (Fintype.card ι : ℝ)⁻¹)
      fun a => ∑ f : LinePoly F (m * d), N.xSqNorm
        (smulKron (PX.lineMats d PA (kX a) f)
          (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
        (smulKron (PX.lineMats d PB (kX a) f) 1)) ?_
    refine Finset.sum_congr rfl fun a _ =>
      congrArg (fun t : ℝ => (Fintype.card ι : ℝ)⁻¹ * t) (Finset.sum_congr rfl fun f _ => ?_)
    exact (M.reg (Anc F m)).jointModel_xSqNorm_smulKron_one _
      ((PX.isPVM_lineMats d hPA (kX a)).star_eq f) _
  have hCT : ∑ i : ι × F,
        ((Fintype.card ι : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
          N.collisionTerm
            (fun b : F => smulKron (PZ.lineEvalMats d PB (kZ i.1) b)
              (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
            (fun f : LinePoly F (m * d) => smulKron (PX.lineMats d PB (kX i.1) f)
              (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
            (fun f : LinePoly F (m * d) => smulKron (PX.lineMats d PA (kX i.1) f)
              (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
            (fun f => LinePoly.eval f
              (PX.param (kX (sh (i.2 • PX.dir (kX i.1)) i.1)))) ≤ εc := by
    refine le_trans (N.sum_collisionTerm_le (Y := F) (Z := ι)
      (ν := fun _ : ι => (Fintype.card ι : ℝ)⁻¹)
      (R := fun a : ι => fun b : F => smulKron (PZ.lineEvalMats d PB (kZ a) b)
        (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
      (G := fun a : ι => fun f : LinePoly F (m * d) => smulKron (PX.lineMats d PB (kX a) f)
        (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
      (Ga := fun a : ι => fun f : LinePoly F (m * d) => smulKron (PX.lineMats d PA (kX a) f)
        (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
      (εz := fun a : ι => collProb PX d (kX a)) hunit (fun _ => by positivity) hR hG hGa
      (fun (a : ι) (t : F) (f : LinePoly F (m * d)) =>
        LinePoly.eval f (PX.param (kX (sh (t • PX.dir (kX a)) a))))
      (fun a => collProb_nonneg PX d (kX a))
      (fun a f f' hne => by
        simp only [hshX]
        exact card_collide_le PX d (kX a) hne)) hcoll
  -- the pasting lemma
  have key := N.one_sub_sum_bornProb_pasteJ_le hunit hw0 hw1
    (A := fun i : ι × F => fun r : F × F =>
      QA (sh (i.2 • PX.dir (kX i.1)) i.1) (r.2, r.1))
    (R := fun i : ι × F => fun b : F => smulKron (PZ.lineEvalMats d PB (kZ i.1) b)
      (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
    (G := fun i : ι × F => fun f : LinePoly F (m * d) => smulKron (PX.lineMats d PB (kX i.1) f)
      (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
    (Ga := fun i : ι × F => fun f : LinePoly F (m * d) => smulKron (PX.lineMats d PA (kX i.1) f)
      (1 : Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) ℂ))
    (fun i => fun f => LinePoly.eval f (PX.param (kX (sh (i.2 • PX.dir (kX i.1)) i.1))))
    hA (fun i => hR i.1) (fun i => hG i.1) (fun i => hGa i.1) hP1 hP2 hP4 hCT
  -- and the conclusion, read back at the question distribution
  refine le_trans (le_of_eq (congrArg (fun t : ℝ => 1 - t) ?_)) key
  refine Eq.trans (sum_shift_gen (dir := fun a => PX.dir (kX a))
      hzero hadd hdirI (fun a => ∑ p : F × F,
      N.bornProb (QA a p)
        (smulKron (∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
            LinePoly.eval q.1 (PX.param (kX a)) = p.1
              ∧ LinePoly.eval q.2 (PZ.param (kZ a)) = p.2,
          pasteLine PX PZ d PB (kX a) (kZ a) q) 1))).symm
    (Finset.sum_congr rfl fun i _ => congrArg (fun t : ℝ => ((Fintype.card ι : ℝ)⁻¹
      * (Fintype.card F : ℝ)⁻¹) * t) ?_)
  refine (Fintype.sum_equiv (Equiv.prodComm F F) _ _ fun p => ?_).symm
  rw [pasteJ_smulKron_one,
    show PZ.lineEvalMats d PB (kZ i.1)
        = PZ.lineEvalMats d PB (kZ (sh (i.2 • PX.dir (kX i.1)) i.1)) from by
      rw [hkZ]
      exact (PZ.lineEvalMats_shiftPt_other d PB (kZ i.1) (i.2 • PX.dir (kX i.1))).symm,
    show PX.lineMats d PB (kX i.1) = PX.lineMats d PB (kX (sh (i.2 • PX.dir (kX i.1)) i.1)) from by
      rw [hshX i.1 i.2, PX.lineMats_shiftAlong d PB (kX i.1) i.2],
    pasteJ_eq_pasteLine]
  rfl

/-- **`lem:qld-pairs-of-lines`**, on the Pauli basis test's own question distribution: the instance
of `pairs_of_lines_gen` at one content per sample, the same one on both sides. -/
theorem pairs_of_lines [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    {QA : Content F m → F × F →
      Matrix ((F × F) ⊕ (F × F)) ((F × F) ⊕ (F × F)) (Matrix (Anc F m) (Anc F m) 𝒜)}
    (hQA : ∀ c, IsPVMIn (QA c)) (hM : ‖M.ψ‖ = 1)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op) {δ η εc : ℝ}
    (hmargX : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        (extHat (F := F) (m := m) M).xSqNorm (∑ q : F, QA c (a, q))
          (smulKron (PX.lineEvalMats d PB c a) 1) ≤ δ)
    (hmargZ : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ b : F,
        (extHat (F := F) (m := m) M).xSqNorm (∑ q : F, QA c (q, b))
          (smulKron (PZ.lineEvalMats d PB c b) 1) ≤ δ)
    (hselfX : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ f : LinePoly F (m * d),
          (M.reg (Anc F m)).xSqNorm (PX.lineMats d PA c f) (PX.lineMats d PB c f) ≤ η)
    (hcoll : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * collProb PX d c ≤ εc) :
    1 - ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
        (extHat (F := F) (m := m) M).bornProb (QA c p)
          (smulKron (∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
              LinePoly.eval q.1 (PX.param c) = p.1 ∧ LinePoly.eval q.2 (PZ.param c) = p.2,
            pasteLine PX PZ d PB c c q) 1)
      ≤ δ / 2 + Real.sqrt (δ / 2) + Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * εc) :=
  pairs_of_lines_gen PX PZ id id (Content.shiftPt_zero .X) (Content.shiftPt_shiftPt .X)
    (fun _ _ => rfl) (fun _ _ => rfl) hQA hM hPA hPB hmargX hmargZ hselfX hcoll

/-! ## The lemma, from the game -/

/-- The larger of the two ordered-product constants of `lem:qld-combined-points`. -/
def kappaPairs (ε : ℝ) : ℝ := 4 * deltaQ ε + 461411328 * ε

/-- The marginal consistency the pasting lemma is fed. -/
def deltaPairsD (ε : ℝ) : ℝ :=
  2 * (10 * kappaPairs ε) + 2 * (2 * (172 * ε) + 2 * (172 * ε))

/-- **The error of `lem:qld-pairs-of-lines`**, the paper's `delta_P`: `poly(eps, eps_c)` with
`eps_c` the average collision probability of the outcome map, which for an axis-parallel line is
`m d / q`. -/
def deltaPairs (ε εc : ℝ) : ℝ :=
  deltaPairsD ε / 2 + Real.sqrt (deltaPairsD ε / 2)
    + Real.sqrt (32 * deltaPairsD ε + 4 * Real.sqrt (172 * ε) + 2 * εc)

set_option maxHeartbeats 1600000 in
/-- **`lem:qld-pairs-of-lines`**, from the game: a winning strategy's combined point measurement
agrees with the pasted line measurement of any pair of line presentations, up to `deltaPairs`.
The three inputs are the two items of `lem:qld-expanded-lines` on the `X` side, its second item on
the `Z` side, and the average collision probability.

The combined point measurement is the *dilated* one of `combined_points_dilated`, projective on
the model of the dilation, which is what the pasting lemma needs; its compression to the expanded
model is the sandwich `M-hat^{Z,z}_b M-hat^{X,x}_a M-hat^{Z,z}_b`, and the pasted line measurement
does not see the dilation register (`BipartiteModel.jointModel_bornProb`), so the conclusion is
an agreement bound of the **sandwich** in the expanded model `M.reg (Anc F m)`, with the dilation
kept inside the proof. -/
theorem pairs_of_lines_of_items [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]
    (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op)
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    (hX1 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        (M.reg (Anc F m)).xSqNorm (PX.lineMats d PA c f) (PX.lineMats d PB c f) ≤ 172 * ε)
    (hX2 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        (M.reg (Anc F m)).xSqNorm (hatMats PA .X (c.pt .X) a) (PX.lineEvalMats d PB c a)
          ≤ 172 * ε)
    (hZ2 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ b : F,
        (M.reg (Anc F m)).xSqNorm (hatMats PA .Z (c.pt .Z) b) (PZ.lineEvalMats d PB c b)
          ≤ 172 * ε)
    {εc : ℝ} (hcoll : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
      collProb PX d c ≤ εc) :
    1 - ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
        (M.reg (Anc F m)).bornProb (sand (hatMats PA .X c.uX) (hatMats PA .Z c.uZ) p)
          (∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
              LinePoly.eval q.1 (PX.param c) = p.1 ∧ LinePoly.eval q.2 (PZ.param c) = p.2,
            pasteLine PX PZ d PB c c q)
      ≤ deltaPairs ε εc := by
  classical
  have hε0 : 0 ≤ ε := le_trans (by
    rw [M.one_sub_povmValue_eq]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg ((qldGame hm).μ_nonneg x y) (M.condFail_nonneg hM x y)) hfail
  obtain ⟨QA, -, hQA, -, hkA, -, -, h6, h7⟩ :=
    combined_points_dilated (PA := PA) (PB := PB) hM hfail hPA hPB
  -- Bob's point measurement against his own line measurement, on each side
  have hptX := sum_content_normSq_point_line_le (PA := PA) .X PX
    (sum_content_hatMats_consistency (PB := PB) hM hfail .X) hX2
  have hptZ := sum_content_normSq_point_line_le (PA := PA) .Z PZ
    (sum_content_hatMats_consistency (PB := PB) hM hfail .Z) hZ2
  -- the two marginal consistencies
  have hmargX := sum_content_marg_line_le (PB := PB) .X PX hQA hPB
    (κ := kappaPairs ε) (η := 2 * (172 * ε) + 2 * (172 * ε))
    (le_trans h6 (by rw [kappaPairs]; nlinarith)) hptX
  have hmargZ := sum_content_marg_line_le (PB := PB) .Z PZ hQA hPB
    (κ := kappaPairs ε) (η := 2 * (172 * ε) + 2 * (172 * ε))
    (le_trans h7 (le_of_eq (show 4 * deltaQ ε + 461411328 * ε = kappaPairs ε from by
      rw [kappaPairs]))) hptZ
  -- the pasting lemma at the two presentations, read back on the expanded model
  refine le_trans (le_of_eq (congrArg (fun t : ℝ => 1 - t) ?_))
    (le_trans (pairs_of_lines PX PZ hQA hM hPA hPB hmargX hmargZ hX1 hcoll)
      (le_of_eq (by rw [deltaPairs, deltaPairsD])))
  refine Finset.sum_congr rfl fun c _ => congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹
    * t) (Finset.sum_congr rfl fun p _ => ?_)
  rw [BipartiteModel.jointModel_bornProb, smulKron_apply, Matrix.one_apply_eq, one_smul, hkA]

/-- **A degenerate diagonal line is rare.** Shifting the content's raw direction along the seed's
own pivot coordinate moves the diagonal direction's pivot coordinate by the shift, so at most one
shift in `q` makes that direction vanish --- and the same change of variables that produced the
point's uniformity on its line gives the bound. -/
theorem sum_content_degenerate_le (hm : m ∣ Fintype.card F) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        (if ∃ j, ddirOf hm c j ≠ 0 then (0 : ℝ) else 1)
      ≤ (Fintype.card F : ℝ)⁻¹ := by
  classical
  have hF : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hdir : ∀ (c : Content F m) (w : Point F m), dirOf hm (Content.shiftV w c) = dirOf hm c :=
    fun c w => by rw [dirOf, dirOf, Content.shiftV_s]
  -- the pivot coordinate of the shifted direction
  have hpivot : ∀ (c : Content F m) (x : F),
      ddirOf hm (Content.shiftV (x • dirOf hm c) c) (MIPRE.LIDT.CL.chi hm c.s)
        = c.v (MIPRE.LIDT.CL.chi hm c.s) + x := by
    intro c x
    rw [ddirOf, Content.shiftV_s, Content.shiftV_v, MIPRE.LIDT.CL.zeroBelow,
      if_neg (lt_irrefl _), dirOf]
    show c.v (MIPRE.LIDT.CL.chi hm c.s)
      + (x • (Pi.single (MIPRE.LIDT.CL.chi hm c.s) (1 : F))) (MIPRE.LIDT.CL.chi hm c.s) = _
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  -- at one content, at most one shift is degenerate
  have hinner : ∀ c : Content F m,
      (∑ x : F, (if ∃ j, ddirOf hm (Content.shiftV (x • dirOf hm c) c) j ≠ 0 then (0 : ℝ) else 1))
        ≤ 1 := by
    intro c
    have hsub : (univ.filter fun x : F =>
          ¬ ∃ j, ddirOf hm (Content.shiftV (x • dirOf hm c) c) j ≠ 0)
        ⊆ {(-(c.v (MIPRE.LIDT.CL.chi hm c.s)))} := by
      intro x hx
      obtain ⟨-, hx⟩ := Finset.mem_filter.mp hx
      have h0 : ddirOf hm (Content.shiftV (x • dirOf hm c) c)
          (MIPRE.LIDT.CL.chi hm c.s) = 0 := not_not.mp fun h => hx ⟨_, h⟩
      rw [hpivot c x] at h0
      rw [Finset.mem_singleton]
      linear_combination h0
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
      mul_one]
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card hsub)) ?_
    rw [Finset.card_singleton, Nat.cast_one]
  -- the change of variables
  rw [← sum_content_shift_gen Content.shiftV_zero Content.shiftV_shiftV hdir
    (fun c => if ∃ j, ddirOf hm c j ≠ 0 then (0 : ℝ) else 1),
    ← sum_prod_eq fun (c : Content F m) (x : F) =>
      ((Fintype.card (Content F m) : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        (if ∃ j, ddirOf hm (Content.shiftV (x • dirOf hm c) c) j ≠ 0 then (0 : ℝ) else 1)]
  refine le_trans (Finset.sum_le_sum fun c _ => ?_)
    (le_of_eq (show ∑ _c : Content F m, ((Fintype.card (Content F m) : ℝ)⁻¹
        * (Fintype.card F : ℝ)⁻¹) = (Fintype.card F : ℝ)⁻¹ from by
      rw [← Finset.sum_mul, sum_uniform_content, one_mul]))
  rw [← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left (hinner c) (by positivity)) ?_
  rw [mul_one]

/-- **The diagonal collision probability**: `m d / q` on the non-degenerate lines, and the
degenerate ones contribute at most another `1/q`. -/
theorem sum_content_collProb_dPres (hm : m ∣ Fintype.card F) (W : Bas) (d : ℕ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * collProb (dPres hm W) d c
      ≤ (m * d : ℝ) / (Fintype.card F : ℝ) + (Fintype.card F : ℝ)⁻¹ := by
  classical
  have hterm : ∀ c : Content F m, collProb (dPres hm W) d c
      ≤ (m * d : ℝ) / (Fintype.card F : ℝ)
        + (if ∃ j, ddirOf hm c j ≠ 0 then (0 : ℝ) else 1) := by
    intro c
    rw [collProb]
    by_cases hdeg : ∃ j, (dPres hm W).dir c j ≠ 0
    · rw [if_pos hdeg, if_pos (show ∃ j, ddirOf hm c j ≠ 0 from hdeg), add_zero]
    · rw [if_neg hdeg, if_neg (show ¬ ∃ j, ddirOf hm c j ≠ 0 from hdeg)]
      have : (0 : ℝ) ≤ (m * d : ℝ) / (Fintype.card F : ℝ) := by positivity
      linarith
  refine le_trans (Finset.sum_le_sum fun c _ =>
    mul_le_mul_of_nonneg_left (hterm c) (by positivity)) ?_
  rw [sum_weighted_add]
  have h1 : ∑ _c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹
      * ((m * d : ℝ) / (Fintype.card F : ℝ)) = (m * d : ℝ) / (Fintype.card F : ℝ) := by
    rw [← Finset.sum_mul, sum_uniform_content, one_mul]
  rw [h1]
  have h2 := sum_content_degenerate_le (F := F) (m := m) hm
  linarith

/-- **The axis-parallel collision probability is `m d / q`**, the direction being a standard basis
vector and so never degenerate. -/
theorem sum_content_collProb_aPres (hm : m ∣ Fintype.card F) (W : Bas) (d : ℕ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * collProb (aPres hm W) d c
      = (m * d : ℝ) / (Fintype.card F : ℝ) := by
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => show
      (Fintype.card (Content F m) : ℝ)⁻¹ * collProb (aPres hm W) d c
        = (Fintype.card (Content F m) : ℝ)⁻¹ * ((m * d : ℝ) / (Fintype.card F : ℝ)) from by
    rw [collProb, if_pos (aPres_dir_ne_zero hm W c)], ← Finset.sum_mul, sum_uniform_content,
    one_mul]


/-! ### The items of `lem:qld-expanded-lines`, in the shape the assembly wants -/

/-- The two items for an axis-parallel presentation. -/
theorem aPres_items [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ] (hd : 1 ≤ d)
    (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) :
    (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        (M.reg (Anc F m)).xSqNorm ((aPres hm W).lineMats d PA c f)
          ((aPres hm W).lineMats d PB c f) ≤ 172 * ε)
      ∧ ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
          (M.reg (Anc F m)).xSqNorm (hatMats PA W (c.pt W) a)
            ((aPres hm W).lineEvalMats d PB c a) ≤ 172 * ε := by
  obtain ⟨h1, h2⟩ := expanded_lines_aline (PB := PB) hd hM hfail W
  refine ⟨h1, le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
    congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
      (Finset.sum_congr rfl fun a _ => ?_))) h2⟩
  rw [← hatPOVM_mats_eq hm PA W c a]
  rfl

/-- The two items for a diagonal presentation. -/
theorem dPres_items [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ] (hd : 1 ≤ d)
    (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) :
    (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        (M.reg (Anc F m)).xSqNorm ((dPres hm W).lineMats d PA c f)
          ((dPres hm W).lineMats d PB c f) ≤ 172 * ε)
      ∧ ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
          (M.reg (Anc F m)).xSqNorm (hatMats PA W (c.pt W) a)
            ((dPres hm W).lineEvalMats d PB c a) ≤ 172 * ε := by
  obtain ⟨h1, h2⟩ := expanded_lines_dline (PB := PB) hd hM hfail W
  refine ⟨h1, le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
    congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
      (Finset.sum_congr rfl fun a _ => ?_))) h2⟩
  rw [← hatPOVM_mats_eq hm PA W c a]
  rfl

set_option maxHeartbeats 1600000 in
/-- **`lem:qld-pairs-of-lines`** at the axis-parallel line of each side, with every input
discharged from the game: for a projective strategy that wins the Pauli basis test with
probability `1 - eps`, the sandwich of its expanded point measurements --- the compression of the
combined point measurement --- agrees with the pasted line measurement at
`deltaPairs eps (m d / q)`.

The other three pairs of line types are the same three lines of proof, with `dPres_items` in place
of `aPres_items` on the side that changes and `sum_content_collProb_dPres` in place of
`sum_content_collProb_aPres` when the `X` side is the diagonal one. -/
theorem qld_pairs_of_lines [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]
    (hd : 1 ≤ d) (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op) :
    1 - ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
        (M.reg (Anc F m)).bornProb (sand (hatMats PA .X c.uX) (hatMats PA .Z c.uZ) p)
          (∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
              LinePoly.eval q.1 ((aPres hm .X).param c) = p.1
                ∧ LinePoly.eval q.2 ((aPres hm .Z).param c) = p.2,
            pasteLine (aPres hm .X) (aPres hm .Z) d PB c c q)
      ≤ deltaPairs ε ((m * d : ℝ) / (Fintype.card F : ℝ)) :=
  pairs_of_lines_of_items hM hfail hPA hPB (aPres hm .X) (aPres hm .Z)
    (aPres_items (PB := PB) hd hM hfail .X).1 (aPres_items (PB := PB) hd hM hfail .X).2
    (aPres_items (PB := PB) hd hM hfail .Z).2
    (le_of_eq (sum_content_collProb_aPres hm .X d))

end Pairs

end MIPRE.QLD

end

end
