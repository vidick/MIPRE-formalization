/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Product

/-!
# The combining map and the padded line measurement

Blueprint `lem:qld-padded-lines`, the definitional half. The pairs-of-lines stage measures a *pair*
of line polynomials, one per basis; the low-degree test over the padded space
`F_q^{4m}` wants a *single* polynomial on a single padded line. The bridge is the paper's combining
map: on the padded point `u = (x, z, alpha, beta, w)` the combined polynomial takes the value

  `alpha * f_X(x) + beta * f_Z(z)`.

Three things have to be said about it, and this file says them.

* **It is a polynomial of degree at most `md + 1` on the padded line.** Restricted to the padded
  line the two evaluations become evaluations of `f_X` and `f_Z` at *affine* functions of the padded
  parameter --- which is exactly Property 2 of `lem:qld-sublines`, made quantitative --- and the
  factors `alpha` and `beta` are affine in it too. So the whole thing is a product of an affine
  polynomial with a degree-`md` one, and `combine` is that polynomial, built through Mathlib's
  `Polynomial` and truncated back to a coefficient vector.
* **On an axis-parallel padded line the degree drops to `d`.** The padded direction is a single
  coordinate, and the case distinction is the one `padCase` already makes: in the `X` and `Z` blocks
  `alpha` and `beta` are constant along the line, so the degree is that of `f_X` and `f_Z`; at
  `alpha`, `beta` or a dummy coordinate *both* blocks are constant along the line, so the combined
  polynomial is affine. The first case needs `f_X` and `f_Z` to have degree `d`, which is
  `lem:qld-axis-degree`; the second needs only `d >= 1`.
* **The measurement.** `padLineMats` is the paper's `Q-hat^l`: the conditional average, over the
  fresh randomness the subline construction draws, of the pasted line measurement
  `T^{l_X,l_Z}`, coarse-grained by the combining map. It is a POVM.

What is *not* here is the consistency bound `delta_combine`; see the blueprint.

## The affine data, and why the whole geometry is in `xBlk_dir_sub`

The one calculation behind the affine substitutions is this. Moving along the padded line moves the
`X` block by `tau * xBlk(dir)`, and `xBlk_dir_sub` says that block is *either* the `X` subline's own
direction *or* zero. In the first case the parameter on the subline moves by exactly `tau`, in the
second it does not move at all --- so in both cases it is `p0 + c * tau` with `c` one or zero, and
`subAff` is that pair. Nothing else about the construction is used.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

/-! ## Affine maps of the line parameter -/

section Aff

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- An affine map `t |-> a.1 + a.2 * t` of the line parameter, as the pair of its coefficients. -/
def affEval (a : F × F) (t : F) : F := a.1 + a.2 * t

theorem affEval_of_snd_eq_zero {a : F × F} (h : a.2 = 0) (t : F) : affEval a t = a.1 := by
  rw [affEval, h, zero_mul, add_zero]

/-- The degree-one polynomial an affine map is. -/
def affPoly (a : F × F) : Polynomial F := Polynomial.C a.1 + Polynomial.C a.2 * Polynomial.X

theorem eval_affPoly (a : F × F) (t : F) : (affPoly a).eval t = affEval a t := by
  rw [affPoly, affEval, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

theorem natDegree_affPoly_le (a : F × F) : (affPoly a).natDegree ≤ 1 := by
  rw [affPoly]
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  rw [max_le_iff]
  exact ⟨le_trans (le_of_eq (Polynomial.natDegree_C a.1)) (Nat.zero_le 1),
    le_trans (Polynomial.natDegree_C_mul_le a.2 Polynomial.X)
      (le_of_eq Polynomial.natDegree_X)⟩

/-- A constant affine map is a constant polynomial. -/
theorem affPoly_of_snd_eq_zero {a : F × F} (h : a.2 = 0) : affPoly a = Polynomial.C a.1 := by
  rw [affPoly, h, map_zero, zero_mul, add_zero]

theorem natDegree_affPoly_eq_zero {a : F × F} (h : a.2 = 0) : (affPoly a).natDegree = 0 := by
  rw [affPoly_of_snd_eq_zero h, Polynomial.natDegree_C]

/-! ## Coefficient vectors and polynomials, the other way

`toPoly` (in `Lines.lean`) reads a coefficient vector as a polynomial; `ofPoly` truncates a
polynomial to a coefficient vector, and agrees with it in value as soon as the degree fits. -/

/-- The coefficient vector of degree at most `n` a polynomial truncates to. -/
def ofPoly (n : ℕ) (p : Polynomial F) : LinePoly F n := fun i => p.coeff (i : ℕ)

theorem eval_ofPoly {p : Polynomial F} (hp : p.natDegree ≤ n) (t : F) :
    LinePoly.eval (ofPoly n p) t = p.eval t := by
  rw [LinePoly.eval, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp),
    ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i * t ^ i) (n + 1)]
  rfl

/-- **Degree at most `k`**, as a predicate on coefficient vectors: everything above `k` vanishes.
The answer alphabet is `LinePoly F (m d)` throughout, so a sharper degree bound on an
axis-parallel line is a property of the vector rather than a change of type. -/
def DegLE (f : LinePoly F n) (k : ℕ) : Prop := ∀ i : Fin (n + 1), k < (i : ℕ) → f i = 0

theorem DegLE.mono {f : LinePoly F n} {k k' : ℕ} (h : DegLE f k) (hk : k ≤ k') :
    DegLE f k' := fun i hi => h i (lt_of_le_of_lt hk hi)

theorem degLE_ofPoly {k : ℕ} {p : Polynomial F} (h : p.natDegree ≤ k) : DegLE (ofPoly n p) k :=
  fun _i hi => Polynomial.natDegree_le_iff_coeff_eq_zero.mp h _ hi

theorem natDegree_toPoly_le_of_degLE {f : LinePoly F n} {k : ℕ} (h : DegLE f k) :
    (toPoly f).natDegree ≤ k := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  by_cases hNn : N < n + 1
  · rw [show N = ((⟨N, hNn⟩ : Fin (n + 1)) : ℕ) from rfl, coeff_toPoly]
    exact h ⟨N, hNn⟩ hN
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_toPoly_le f) (by omega))

/-! ## The combining map -/

/-- The polynomial `alpha(t) f_X(x(t)) + beta(t) f_Z(z(t))` with all four substitutions affine. -/
def combinePoly (aAff bAff xAff zAff : F × F) (fX fZ : LinePoly F n) : Polynomial F :=
  affPoly aAff * (toPoly fX).comp (affPoly xAff)
    + affPoly bAff * (toPoly fZ).comp (affPoly zAff)

theorem natDegree_comp_affPoly_le {k : ℕ} (a : F × F) {f : LinePoly F n}
    (hf : (toPoly f).natDegree ≤ k) : ((toPoly f).comp (affPoly a)).natDegree ≤ k :=
  le_trans Polynomial.natDegree_comp_le
    (le_trans (Nat.mul_le_mul hf (natDegree_affPoly_le a)) (le_of_eq (mul_one k)))

theorem natDegree_combinePoly_le (aAff bAff xAff zAff : F × F) (fX fZ : LinePoly F n) :
    (combinePoly aAff bAff xAff zAff fX fZ).natDegree ≤ n + 1 := by
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  rw [max_le_iff]
  constructor
  · refine le_trans (Polynomial.natDegree_mul_le) ?_
    exact le_trans (Nat.add_le_add (natDegree_affPoly_le aAff)
      (natDegree_comp_affPoly_le xAff (natDegree_toPoly_le fX))) (by omega)
  · refine le_trans (Polynomial.natDegree_mul_le) ?_
    exact le_trans (Nat.add_le_add (natDegree_affPoly_le bAff)
      (natDegree_comp_affPoly_le zAff (natDegree_toPoly_le fZ))) (by omega)

/-- **The combining map.** The four affine maps are, in order: `alpha` and `beta` along the padded
line, and the parameter of the `X` and `Z` blocks on their sublines. -/
def combine (aAff bAff xAff zAff : F × F) (fX fZ : LinePoly F n) : LinePoly F (n + 1) :=
  ofPoly (n + 1) (combinePoly aAff bAff xAff zAff fX fZ)

/-- **The defining property of the combining map**: at the padded parameter `t` its value is
`alpha(t) f_X(x(t)) + beta(t) f_Z(z(t))`. -/
theorem eval_combine (aAff bAff xAff zAff : F × F) (fX fZ : LinePoly F n) (t : F) :
    LinePoly.eval (combine aAff bAff xAff zAff fX fZ) t
      = affEval aAff t * LinePoly.eval fX (affEval xAff t)
        + affEval bAff t * LinePoly.eval fZ (affEval zAff t) := by
  rw [combine, eval_ofPoly (natDegree_combinePoly_le aAff bAff xAff zAff fX fZ), combinePoly,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_comp, eval_affPoly, eval_affPoly, eval_affPoly, eval_affPoly, eval_toPoly,
    eval_toPoly]

/-- **When both blocks are constant along the padded line the combined polynomial is affine.** This
is the case of a padded direction in the `alpha`, `beta` or dummy block. -/
theorem degLE_combine_of_blocks_const {aAff bAff xAff zAff : F × F} (fX fZ : LinePoly F n)
    (hx : xAff.2 = 0) (hz : zAff.2 = 0) :
    DegLE (combine aAff bAff xAff zAff fX fZ) 1 := by
  refine degLE_ofPoly (le_trans (Polynomial.natDegree_add_le _ _) ?_)
  rw [max_le_iff]
  have hcomp : ∀ (a : F × F) (f : LinePoly F n), a.2 = 0 →
      ((toPoly f).comp (affPoly a)).natDegree = 0 := fun a f ha => by
    rw [affPoly_of_snd_eq_zero ha, Polynomial.comp_C, Polynomial.natDegree_C]
  constructor
  · exact le_trans Polynomial.natDegree_mul_le
      (le_trans (Nat.add_le_add (natDegree_affPoly_le aAff)
        (le_of_eq (hcomp xAff fX hx))) (by omega))
  · exact le_trans Polynomial.natDegree_mul_le
      (le_trans (Nat.add_le_add (natDegree_affPoly_le bAff)
        (le_of_eq (hcomp zAff fZ hz))) (by omega))

/-- **When `alpha` and `beta` are constant along the padded line the combined polynomial inherits
the degree of the two inputs.** This is the case of a padded direction in the `X` or `Z` block. -/
theorem degLE_combine_of_ab_const {aAff bAff xAff zAff : F × F} {fX fZ : LinePoly F n} {k : ℕ}
    (ha : aAff.2 = 0) (hb : bAff.2 = 0) (hX : DegLE fX k) (hZ : DegLE fZ k) :
    DegLE (combine aAff bAff xAff zAff fX fZ) k := by
  refine degLE_ofPoly (le_trans (Polynomial.natDegree_add_le _ _) ?_)
  rw [max_le_iff]
  constructor
  · exact le_trans Polynomial.natDegree_mul_le
      (le_trans (Nat.add_le_add (le_of_eq (natDegree_affPoly_eq_zero ha))
        (natDegree_comp_affPoly_le xAff (natDegree_toPoly_le_of_degLE hX))) (by omega))
  · exact le_trans Polynomial.natDegree_mul_le
      (le_trans (Nat.add_le_add (le_of_eq (natDegree_affPoly_eq_zero hb))
        (natDegree_comp_affPoly_le zAff (natDegree_toPoly_le_of_degLE hZ))) (by omega))

end Aff

/-! ## The affine substitution a subline induces -/

section SubAff

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
  [NeZero m]

/-- A degenerate line assigns every point the parameter zero. -/
theorem lineParam_dir_zero (u₀ y : Point F m) : CL.lineParam u₀ (0 : Point F m) y = 0 := by
  rw [CL.lineParam, dif_neg]
  exact fun h => h.choose_spec rfl

/-- The base point has parameter zero. -/
theorem lineParam_self (u₀ w : Point F m) : CL.lineParam u₀ w u₀ = 0 := by
  rw [CL.lineParam]
  split
  · rw [sub_self, zero_div]
  · rfl

/-- **The affine substitution the subline's parametrization induces.** The constant term is the
parameter of the unshifted block, and the linear term is `1` exactly when the padded direction moves
the block along a nondegenerate subline. -/
def subAff (W w x : Point F m) : F × F :=
  (CL.lineParam (CL.rep W x) W x, if w = W ∧ W ≠ 0 then 1 else 0)

theorem subAff_snd_of_eq_zero (W x : Point F m) : (subAff W (0 : Point F m) x).2 = 0 := by
  rw [subAff]
  split
  · rename_i h
    exact absurd h.1.symm h.2
  · rfl

/-- **The shifted block lies on the subline at the affine parameter.** -/
theorem on_line_affEval {W w : Point F m} (h : w = W ∨ w = 0) (x : Point F m) (tau : F) :
    x + tau • w = CL.rep W x + affEval (subAff W w x) tau • W := by
  have hx : CL.rep W x + (CL.lineParam (CL.rep W x) W x) • W = x := rep_add_lineParam_smul W x
  have haff : affEval (subAff W w x) tau
      = CL.lineParam (CL.rep W x) W x + (if w = W ∧ W ≠ 0 then 1 else 0) * tau := rfl
  by_cases hc : w = W ∧ W ≠ 0
  · rw [haff, if_pos hc, one_mul, add_smul, ← add_assoc, hx, hc.1]
  · rw [haff, if_neg hc, zero_mul, add_zero, hx]
    rcases h with h | h
    · rw [h, show W = 0 from by by_contra hW; exact hc ⟨h, hW⟩, smul_zero, add_zero]
    · rw [h, smul_zero, add_zero]

/-- **The parameter of the shifted block on the subline is affine in the padded parameter.** -/
theorem lineParam_affEval {W w : Point F m} (h : w = W ∨ w = 0) (x : Point F m) (tau : F) :
    CL.lineParam (CL.rep W x) W (x + tau • w) = affEval (subAff W w x) tau := by
  rw [on_line_affEval h x tau]
  by_cases hW : ∃ j, W j ≠ 0
  · rw [lineParam_add_smul hW, lineParam_self, zero_add]
  · have hW0 : W = 0 := by
      funext j
      by_contra hj
      exact hW ⟨j, hj⟩
    rw [hW0, lineParam_dir_zero, affEval, subAff]
    show (0 : F) = CL.lineParam (CL.rep (0 : Point F m) x) 0 x + _ * tau
    rw [lineParam_dir_zero, zero_add, if_neg (fun hc => hc.2 rfl), zero_mul]

end SubAff

/-! ## The affine data of a padded line and its sublines -/

section Padded

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- The `alpha` coordinate of a single coordinate vector away from `alpha` vanishes. -/
theorem alph_single_of_ne {j : Fin (4 * m)} (h : j ≠ aIdx m) (c : F) :
    alph (Pi.single j c) = 0 := by
  rw [alph, Pi.single_eq_of_ne (Ne.symm h)]

theorem bet_single_of_ne {j : Fin (4 * m)} (h : j ≠ bIdx m) (c : F) :
    bet (Pi.single j c) = 0 := by
  rw [bet, Pi.single_eq_of_ne (Ne.symm h)]

/-- The direction a data presents does not depend on its point. -/
theorem LPData.dir_congr (hm : m ∣ Fintype.card F) (ty : CL.Ty) {c c' : LPData F m}
    (hs : c.s = c'.s) (hr : c.raw = c'.raw) : c.dir hm ty = c'.dir hm ty := by
  cases ty
  · rw [LPData.dir_point, LPData.dir_point]
  · rw [LPData.dir_aline, LPData.dir_aline, hs]
  · rw [LPData.dir_dline, LPData.dir_dline, hs, hr]

/-- Moving the padded point along the padded line by `tau`. -/
def padShift (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty) (tau : F) (P : LPData F (4 * m)) :
    LPData F (4 * m) := ⟨P.pt + tau • P.dir hm4 ty, P.s, P.raw⟩

@[simp] theorem padShift_pt (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty) (tau : F)
    (P : LPData F (4 * m)) : (padShift hm4 ty tau P).pt = P.pt + tau • P.dir hm4 ty := rfl

@[simp] theorem padShift_s (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty) (tau : F)
    (P : LPData F (4 * m)) : (padShift hm4 ty tau P).s = P.s := rfl

@[simp] theorem padShift_raw (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty) (tau : F)
    (P : LPData F (4 * m)) : (padShift hm4 ty tau P).raw = P.raw := rfl

variable (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)

/-- **The subline data is unchanged by the padded shift except in its point**, because the seed and
the raw direction it reads are. -/
theorem subX_padShift (ty : CL.Ty) (tau : F) (P : LPData F (4 * m)) (e : F × Point F m) :
    subX hm4 hm (padShift hm4 ty tau P) e
      = { subX hm4 hm P e with pt := xBlk (padShift hm4 ty tau P).pt } := by
  simp only [subX, padShift_s]
  rcases h : padCase (chi hm4 P.s) with i | i | _ | _ <;> rfl

theorem subZ_padShift (ty ty' : CL.Ty) (tau : F) (P : LPData F (4 * m)) (e : F × Point F m) :
    subZ hm4 hm ty' (padShift hm4 ty tau P) e
      = { subZ hm4 hm ty' P e with pt := zBlk (padShift hm4 ty tau P).pt } := by
  simp only [subZ, padShift_s]
  rcases h : padCase (chi hm4 P.s) with i | i | _ | _ <;> cases ty' <;> rfl

theorem subX_padShift_dir (ty ty' : CL.Ty) (tau : F) (P : LPData F (4 * m))
    (e : F × Point F m) :
    (subX hm4 hm (padShift hm4 ty tau P) e).dir hm ty' = (subX hm4 hm P e).dir hm ty' := by
  refine LPData.dir_congr hm ty' ?_ ?_ <;> rw [subX_padShift]

theorem subZ_padShift_dir (ty ty' : CL.Ty) (tau : F) (P : LPData F (4 * m))
    (e : F × Point F m) :
    (subZ hm4 hm ty' (padShift hm4 ty tau P) e).dir hm ty'
      = (subZ hm4 hm ty' P e).dir hm ty' := by
  refine LPData.dir_congr hm ty' ?_ ?_ <;> rw [subZ_padShift]

/-- **The subline's base point is unchanged by the padded shift**, which is where the containment
of `lem:qld-sublines` is used: the block either moves along the subline or does not move. -/
theorem rep_xBlk_padShift (ty : CL.Ty) (tau : F) (P : LPData F (4 * m)) (e : F × Point F m) :
    CL.rep ((subX hm4 hm P e).dir hm ty) (xBlk (padShift hm4 ty tau P).pt)
      = CL.rep ((subX hm4 hm P e).dir hm ty) (xBlk P.pt) := by
  rw [padShift_pt, xBlk_add_smul]
  rcases xBlk_dir_sub hm4 hm ty P e with h | h
  · rw [h, rep_add_smul]
  · rw [h, smul_zero, add_zero]

theorem rep_zBlk_padShift (ty : CL.Ty) (tau : F) (P : LPData F (4 * m)) (e : F × Point F m) :
    CL.rep ((subZ hm4 hm ty P e).dir hm ty) (zBlk (padShift hm4 ty tau P).pt)
      = CL.rep ((subZ hm4 hm ty P e).dir hm ty) (zBlk P.pt) := by
  rw [padShift_pt, zBlk_add_smul]
  rcases zBlk_dir_sub hm4 hm ty P e with h | h
  · rw [h, rep_add_smul]
  · rw [h, smul_zero, add_zero]

/-! ### The four affine maps -/

/-- `alpha` along the padded line. -/
def aAffOf (ty : CL.Ty) (P : LPData F (4 * m)) : F × F := (alph P.pt, alph (P.dir hm4 ty))

/-- `beta` along the padded line. -/
def bAffOf (ty : CL.Ty) (P : LPData F (4 * m)) : F × F := (bet P.pt, bet (P.dir hm4 ty))

/-- The parameter of the `X` block on the `X` subline, along the padded line. -/
def xAffOf (ty : CL.Ty) (P : LPData F (4 * m)) (e : F × Point F m) : F × F :=
  subAff ((subX hm4 hm P e).dir hm ty) (xBlk (P.dir hm4 ty)) (xBlk P.pt)

/-- The parameter of the `Z` block on the `Z` subline, along the padded line. -/
def zAffOf (ty : CL.Ty) (P : LPData F (4 * m)) (e : F × Point F m) : F × F :=
  subAff ((subZ hm4 hm ty P e).dir hm ty) (zBlk (P.dir hm4 ty)) (zBlk P.pt)

theorem affEval_aAffOf (ty : CL.Ty) (P : LPData F (4 * m)) (tau : F) :
    affEval (aAffOf hm4 ty P) tau = alph (padShift hm4 ty tau P).pt := by
  show alph P.pt + alph (P.dir hm4 ty) * tau = alph (P.pt + tau • P.dir hm4 ty)
  rw [alph_add, alph_smul]
  ring

theorem affEval_bAffOf (ty : CL.Ty) (P : LPData F (4 * m)) (tau : F) :
    affEval (bAffOf hm4 ty P) tau = bet (padShift hm4 ty tau P).pt := by
  show bet P.pt + bet (P.dir hm4 ty) * tau = bet (P.pt + tau • P.dir hm4 ty)
  rw [bet_add, bet_smul]
  ring

/-! ### The parameter identity

A line presentation reads the subline data through `ofLPX` / `ofLPZ`; the two hypotheses say it reads
it as the seeded test does --- the base point is the canonical representative of the point in the
direction, and the direction is the one the data presents. Both hold for `aPres` and `dPres` by
`rfl`. -/

theorem aPres_base_eq (W : Bas) (c : Content F m) :
    (aPres hm W).base c = CL.rep ((aPres hm W).dir c) (c.pt W) := rfl

theorem dPres_base_eq (W : Bas) (c : Content F m) :
    (dPres hm W).base c = CL.rep ((dPres hm W).dir c) (c.pt W) := rfl

theorem aPres_dir_ofLPX (D : LPData F m) (u : Point F m) :
    (aPres hm .X).dir (ofLPX D u) = D.dir hm .aline := rfl

theorem aPres_dir_ofLPZ (D : LPData F m) (u : Point F m) :
    (aPres hm .Z).dir (ofLPZ D u) = D.dir hm .aline := rfl

theorem dPres_dir_ofLPX (D : LPData F m) (u : Point F m) :
    (dPres hm .X).dir (ofLPX D u) = D.dir hm .dline := rfl

theorem dPres_dir_ofLPZ (D : LPData F m) (u : Point F m) :
    (dPres hm .Z).dir (ofLPZ D u) = D.dir hm .dline := rfl

/-- **The `X` subline parameter of the shifted point is `xAffOf` at the padded parameter.** -/
theorem param_subX_padShift (ty : CL.Ty) (PX : LinePres F m hm .X)
    (hbase : ∀ c : Content F m, PX.base c = CL.rep (PX.dir c) (c.pt .X))
    (hdir : ∀ (D : LPData F m) (u : Point F m), PX.dir (ofLPX D u) = D.dir hm ty)
    (P : LPData F (4 * m)) (e : F × Point F m) (u : Point F m) (tau : F) :
    PX.param (ofLPX (subX hm4 hm (padShift hm4 ty tau P) e) u)
      = affEval (xAffOf hm4 hm ty P e) tau := by
  rw [LinePres.param, hbase, hdir, subX_padShift_dir]
  show CL.lineParam (CL.rep ((subX hm4 hm P e).dir hm ty)
      (subX hm4 hm (padShift hm4 ty tau P) e).pt)
      ((subX hm4 hm P e).dir hm ty) (subX hm4 hm (padShift hm4 ty tau P) e).pt = _
  rw [subX_pt, rep_xBlk_padShift, padShift_pt, xBlk_add_smul, xAffOf]
  exact lineParam_affEval (xBlk_dir_sub hm4 hm ty P e) (xBlk P.pt) tau

/-- **The `Z` subline parameter of the shifted point is `zAffOf` at the padded parameter.** -/
theorem param_subZ_padShift (ty : CL.Ty) (PZ : LinePres F m hm .Z)
    (hbase : ∀ c : Content F m, PZ.base c = CL.rep (PZ.dir c) (c.pt .Z))
    (hdir : ∀ (D : LPData F m) (u : Point F m), PZ.dir (ofLPZ D u) = D.dir hm ty)
    (P : LPData F (4 * m)) (e : F × Point F m) (u : Point F m) (tau : F) :
    PZ.param (ofLPZ (subZ hm4 hm ty (padShift hm4 ty tau P) e) u)
      = affEval (zAffOf hm4 hm ty P e) tau := by
  rw [LinePres.param, hbase, hdir, subZ_padShift_dir]
  show CL.lineParam (CL.rep ((subZ hm4 hm ty P e).dir hm ty)
      (subZ hm4 hm ty (padShift hm4 ty tau P) e).pt)
      ((subZ hm4 hm ty P e).dir hm ty) (subZ hm4 hm ty (padShift hm4 ty tau P) e).pt = _
  rw [subZ_pt, rep_zBlk_padShift, padShift_pt, zBlk_add_smul, zAffOf]
  exact lineParam_affEval (zBlk_dir_sub hm4 hm ty P e) (zBlk P.pt) tau

/-! ### The padded combining map -/

/-- **The combining map at a padded line and its two sublines.** -/
def padCombine (ty : CL.Ty) (d : ℕ) (P : LPData F (4 * m)) (eX eZ : F × Point F m)
    (q : LinePoly F (m * d) × LinePoly F (m * d)) : LinePoly F (m * d + 1) :=
  combine (aAffOf hm4 ty P) (bAffOf hm4 ty P) (xAffOf hm4 hm ty P eX) (zAffOf hm4 hm ty P eZ)
    q.1 q.2

/-- **The paper's defining property of the combining map**: at the padded parameter `tau` the
combined polynomial takes the value `alpha * f_X(x) + beta * f_Z(z)` at the corresponding point of
the padded line, `x` and `z` being read on their own sublines. -/
theorem eval_padCombine (ty : CL.Ty) (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    (hbaseX : ∀ c : Content F m, PX.base c = CL.rep (PX.dir c) (c.pt .X))
    (hdirX : ∀ (D : LPData F m) (u : Point F m), PX.dir (ofLPX D u) = D.dir hm ty)
    (hbaseZ : ∀ c : Content F m, PZ.base c = CL.rep (PZ.dir c) (c.pt .Z))
    (hdirZ : ∀ (D : LPData F m) (u : Point F m), PZ.dir (ofLPZ D u) = D.dir hm ty)
    (P : LPData F (4 * m)) (eX eZ : F × Point F m)
    (q : LinePoly F (m * d) × LinePoly F (m * d)) (uZ uX : Point F m) (tau : F) :
    LinePoly.eval (padCombine hm4 hm ty d P eX eZ q) tau
      = alph (padShift hm4 ty tau P).pt
          * LinePoly.eval q.1 (PX.param (ofLPX (subX hm4 hm (padShift hm4 ty tau P) eX) uZ))
        + bet (padShift hm4 ty tau P).pt
          * LinePoly.eval q.2 (PZ.param (ofLPZ (subZ hm4 hm ty (padShift hm4 ty tau P) eZ) uX)) := by
  rw [padCombine, eval_combine, affEval_aAffOf, affEval_bAffOf,
    param_subX_padShift hm4 hm ty PX hbaseX hdirX P eX uZ tau,
    param_subZ_padShift hm4 hm ty PZ hbaseZ hdirZ P eZ uX tau]

/-! ### The degree bound on an axis-parallel padded line -/

/-- **On an axis-parallel padded line the combined polynomial has degree at most `d`.** The three
branches are the paper's: a direction in the `X` or the `Z` block leaves `alpha` and `beta` constant,
and a direction at `alpha`, `beta` or a dummy coordinate leaves both blocks constant, which gives
degree at most one. -/
theorem degLE_padCombine_aline (hd : 1 ≤ d) (P : LPData F (4 * m)) (eX eZ : F × Point F m)
    (q : LinePoly F (m * d) × LinePoly F (m * d))
    (hX : DegLE q.1 d) (hZ : DegLE q.2 d) :
    DegLE (padCombine hm4 hm .aline d P eX eZ q) d := by
  have hdir : P.dir hm4 .aline = Pi.single (chi hm4 P.s) 1 := LPData.dir_aline hm4 P
  rcases h : padCase (chi hm4 P.s) with i | i | _ | _
  · -- a direction in the `X` block: `alpha` and `beta` are constant along the line
    refine degLE_combine_of_ab_const ?_ ?_ hX hZ
    · rw [aAffOf, hdir, padCase_eq_xc h]
      exact alph_single_of_ne (xIdx_ne_aIdx i) 1
    · rw [bAffOf, hdir, padCase_eq_xc h]
      exact bet_single_of_ne (xIdx_ne_bIdx i) 1
  · -- a direction in the `Z` block
    refine degLE_combine_of_ab_const ?_ ?_ hX hZ
    · rw [aAffOf, hdir, padCase_eq_zc h]
      exact alph_single_of_ne (zIdx_ne_aIdx i) 1
    · rw [bAffOf, hdir, padCase_eq_zc h]
      exact bet_single_of_ne (zIdx_ne_bIdx i) 1
  all_goals
    -- a direction at `alpha`, `beta` or a dummy coordinate: both blocks are constant
    refine DegLE.mono (degLE_combine_of_blocks_const q.1 q.2 ?_ ?_) hd
    · rw [xAffOf, show xBlk (P.dir hm4 .aline) = (0 : Point F m) from by
        rw [hdir]
        first
          | exact xBlk_single_of_le (le_trans (by omega) (le_of_padCase_ab h)) 1
          | exact xBlk_single_of_le (le_trans (by omega) (le_of_padCase_dum h)) 1]
      exact subAff_snd_of_eq_zero _ _
    · rw [zAffOf, show zBlk (P.dir hm4 .aline) = (0 : Point F m) from by
        rw [hdir]
        first
          | exact zBlk_single_of_ge (le_of_padCase_ab h) 1
          | exact zBlk_single_of_ge (le_of_padCase_dum h) 1]
      exact subAff_snd_of_eq_zero _ _

end Padded

/-! ## The padded line measurement

The paper's `Q-hat^l_f` is the conditional average, over the sublines the construction of
`lem:qld-sublines` draws for the given padded line, of the pasted line measurement
`T^{l_X,l_Z}_{f_X,f_Z}`, coarse-grained by the combining map. Conditioning on the padded line means
averaging over the fresh randomness the construction draws --- a seed and a raw direction per side
--- and nothing else, so the conditional average is a plain uniform average over `SubRand`. -/

section POVM

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dB : Type} [Fintype dB] [DecidableEq dB] {hm : m ∣ Fintype.card F}
  {M : Question F m → POVM (Answer F m d) dB}

/-- **The pasted line measurement is a POVM**: a sandwich of projectors is positive, and the pairs
of line polynomials exhaust it. -/
theorem sum_pasteLine (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (cX cZ : Content F m) :
    ∑ q : LinePoly F (m * d) × LinePoly F (m * d),
        (pasteLine PX PZ d M cX cZ q
          : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ) = 1 := by
  have hA : IsPVM fun f : LinePoly F (m * d) =>
      (aOp (PX.lineMats d M cX f)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ) :=
    IsPVM.aOp (PX.isPVM_lineMats d hM cX)
  have hB : IsPVM fun f : LinePoly F (m * d) =>
      (aOp (PZ.lineMats d M cZ f)
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ) :=
    IsPVM.aOp (PZ.isPVM_lineMats d hM cZ)
  rw [Finset.sum_congr rfl fun q
      (_ : q ∈ (univ : Finset (LinePoly F (m * d) × LinePoly F (m * d)))) =>
    show (pasteLine PX PZ d M cX cZ q
          : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ)
        = aOp (PX.lineMats d M cX q.1) * aOp (PZ.lineMats d M cZ q.2)
            * aOp (PX.lineMats d M cX q.1) from by
      rw [pasteLine, aOp_mul, aOp_mul]]
  exact (Fintype.sum_equiv (Equiv.prodComm (LinePoly F (m * d)) (LinePoly F (m * d))) _ _
    fun q => rfl).trans (sum_sandOpG hB hA)

theorem posSemidef_pasteLine (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (cX cZ : Content F m)
    (q : LinePoly F (m * d) × LinePoly F (m * d)) :
    (pasteLine PX PZ d M cX cZ q
      : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ).PosSemidef := by
  rw [pasteLine, aOp_mul, aOp_mul]
  exact sandOpG_posSemidef (IsPVM.aOp (PZ.isPVM_lineMats d hM cZ))
    (IsPVM.aOp (PX.isPVM_lineMats d hM cX)) q.2 q.1

/-- The fresh randomness the subline construction draws: a seed and a raw direction per side. -/
abbrev SubRand (F : Type*) (m : ℕ) := (F × Point F m) × (F × Point F m)

/-- The pair of subline data a padded line and the fresh randomness produce --- the sample the
product form of `lem:qld-pairs-of-lines` is stated over. -/
def subPair (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (ty : CL.Ty)
    (P : LPData F (4 * m)) (e : SubRand F m) : LPData F m × LPData F m :=
  (subX hm4 hm P e.1, subZ hm4 hm ty P e.2)

/-- **The padded line measurement `Q-hat^l`.** Its outcomes are line polynomials of degree at most
`md + 1` on the padded line, and on an axis-parallel padded line `degLE_padCombine_aline` sharpens
that to `d`. -/
def padLineMats (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty) (PX : LinePres F m hm .X)
    (PZ : LinePres F m hm .Z) (M : Question F m → POVM (Answer F m d) dB)
    (P : LPData F (4 * m)) (f : LinePoly F (m * d + 1)) :
    Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ :=
  ((Fintype.card (SubRand F m) : ℝ))⁻¹ • ∑ e : SubRand F m,
    ∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
        padCombine hm4 hm ty d P e.1 e.2 q = f,
      pasteLine PX PZ d M (pairCX (subPair hm4 hm ty P e)) (pairCZ (subPair hm4 hm ty P e)) q

/-- **The padded line measurement is complete.** The fibres of the combining map partition the pairs
of line polynomials, so the outcome sum is the pasted measurement's own. -/
theorem sum_padLineMats (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty) (PX : LinePres F m hm .X)
    (PZ : LinePres F m hm .Z) (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (P : LPData F (4 * m)) :
    ∑ f : LinePoly F (m * d + 1), padLineMats hm4 ty PX PZ M P f = 1 := by
  classical
  have hcard : (Fintype.card (SubRand F m) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hinner : ∀ e : SubRand F m,
      ∑ f : LinePoly F (m * d + 1),
        ∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
            padCombine hm4 hm ty d P e.1 e.2 q = f,
          (pasteLine PX PZ d M (pairCX (subPair hm4 hm ty P e))
              (pairCZ (subPair hm4 hm ty P e)) q
            : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ) = 1 := by
    intro e
    rw [← sum_fiber (fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
        padCombine hm4 hm ty d P e.1 e.2 q)
      fun _ q => (pasteLine PX PZ d M (pairCX (subPair hm4 hm ty P e))
          (pairCZ (subPair hm4 hm ty P e)) q
        : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ)]
    exact sum_pasteLine hM PX PZ _ _
  simp only [padLineMats]
  rw [← Finset.smul_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun e (_ : e ∈ (univ : Finset (SubRand F m))) => hinner e,
    Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- **Each outcome of the padded line measurement is positive.** -/
theorem posSemidef_padLineMats (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty)
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (P : LPData F (4 * m))
    (f : LinePoly F (m * d + 1)) :
    (padLineMats hm4 ty PX PZ M P f).PosSemidef := by
  refine Matrix.PosSemidef.smul ?_ (by positivity)
  refine Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero
    fun e _ => ?_
  exact Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero
    fun q _ => posSemidef_pasteLine hM PX PZ _ _ q

/-- **Coarse-graining a fibre sum again**: summing the fibres of `g` over a set of values is summing
over the preimage of that set. -/
theorem sum_filter_fiber {α β N : Type*} [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid N]
    (g : α → β) (p : β → Prop) [DecidablePred p] (T : α → N) :
    ∑ b ∈ univ.filter p, ∑ a ∈ univ.filter fun a => g a = b, T a
      = ∑ a ∈ univ.filter fun a => p (g a), T a := by
  classical
  refine Eq.trans (Finset.sum_congr rfl fun b hb => ?_)
    (Finset.sum_fiberwise_of_maps_to (s := univ.filter fun a => p (g a)) (t := univ.filter p)
      (fun a ha => Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp ha).2⟩) T)
  refine Finset.sum_congr ?_ fun _ _ => rfl
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun a _ => ?_
  exact ⟨fun h => ⟨by rw [h]; exact (Finset.mem_filter.mp hb).2, h⟩, fun h => h.2⟩

/-- **The padded line measurement, coarse-grained by evaluation at the sampled padded point, is the
pasted line measurement coarse-grained by the combined evaluation.** This is the data-processing step
the paper's proof of `lem:qld-padded-lines` ends with, and it is the form in which
`pairs_of_lines_prod` applies: on the right each side's polynomial is read at the parameter of its
*own* subline, which is the outcome map the product form of the pairs-of-lines lemma bounds. -/
theorem sum_filter_padLineMats (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty)
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    (hbaseX : ∀ c : Content F m, PX.base c = CL.rep (PX.dir c) (c.pt .X))
    (hdirX : ∀ (D : LPData F m) (u : Point F m), PX.dir (ofLPX D u) = D.dir hm ty)
    (hbaseZ : ∀ c : Content F m, PZ.base c = CL.rep (PZ.dir c) (c.pt .Z))
    (hdirZ : ∀ (D : LPData F m) (u : Point F m), PZ.dir (ofLPZ D u) = D.dir hm ty)
    (P : LPData F (4 * m)) (tau a : F) :
    ∑ f ∈ univ.filter fun f : LinePoly F (m * d + 1) => LinePoly.eval f tau = a,
        padLineMats hm4 ty PX PZ M P f
      = ((Fintype.card (SubRand F m) : ℝ))⁻¹ • ∑ e : SubRand F m,
          ∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
              alph (padShift hm4 ty tau P).pt
                    * LinePoly.eval q.1
                        (PX.param (pairCX (subPair hm4 hm ty (padShift hm4 ty tau P) e)))
                  + bet (padShift hm4 ty tau P).pt
                    * LinePoly.eval q.2
                        (PZ.param (pairCZ (subPair hm4 hm ty (padShift hm4 ty tau P) e))) = a,
            pasteLine PX PZ d M (pairCX (subPair hm4 hm ty P e))
              (pairCZ (subPair hm4 hm ty P e)) q := by
  classical
  simp only [padLineMats]
  rw [← Finset.smul_sum, Finset.sum_comm]
  refine congrArg (fun A => ((Fintype.card (SubRand F m) : ℝ))⁻¹ • A)
    (Finset.sum_congr rfl fun e _ => ?_)
  rw [sum_filter_fiber (fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
    padCombine hm4 hm ty d P e.1 e.2 q) (fun f => LinePoly.eval f tau = a)]
  refine Finset.sum_congr (Finset.filter_congr fun q _ => ?_) fun _ _ => rfl
  rw [eval_padCombine hm4 hm ty PX PZ hbaseX hdirX hbaseZ hdirZ P e.1 e.2 q
    (subZ hm4 hm ty (padShift hm4 ty tau P) e.2).pt
    (subX hm4 hm (padShift hm4 ty tau P) e.1).pt tau]
  exact Iff.rfl

end POVM

end MIPRE.QLD
