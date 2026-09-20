/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Padded

/-!
# A content, and a product of two independent line-point pairs

`lem:qld-pairs-of-lines` is proved on the Pauli basis test's own question distribution: one
`Content`, carrying both sides' points but a **single** seed and a **single** raw direction, so the
`X` line and the `Z` line it presents are not independent. `lem:qld-padded-lines` needs the same
conclusion on a **product** of two independent line-point laws, which is what `lem:qld-sublines`
delivers.

The transfer is available, and the reason is worth stating before the machinery: **no hypothesis of
the pasting lemma involves both lines.** Each marginal consistency involves one line and the two
points; the fine self-consistency and the collision term involve one line only. So the only laws
that have to agree are

* one side's line-point data on its own,
* one side's line-point data together with the *other side's point*,
* the two points.

and each of those has the same law under a content as under a product, because a content's two
points and its seed and raw direction are independent and uniform. This file says that three times,
and each proof is one line on top of `MIPRE.avg_comp_equiv_fst`: exhibit the splitting of each
sample space that isolates the part the quantity depends on, and the marginals match.

What the file does *not* claim is that the two laws agree on anything involving both lines --- they
do not, and that is the content of the paper's restriction to product distributions.
-/

noncomputable section

namespace MIPRE.QLD

open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]

instance : Nonempty (Content F m) := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩
instance : Nonempty (LPData F m) := ⟨⟨0, 0, 0⟩⟩

/-! ## Reading a content as line-point data, and back -/

/-- The `X`-side line-point data a content carries: its `X` point, its seed, its raw direction. -/
def Content.lpX (c : Content F m) : LPData F m := ⟨c.uX, c.s, c.v⟩

/-- The `Z`-side line-point data a content carries: the **same** seed and raw direction, with the
`Z` point. That sharing is exactly why a content is not a product of two independent line-point
pairs. -/
def Content.lpZ (c : Content F m) : LPData F m := ⟨c.uZ, c.s, c.v⟩

/-- A content assembled from `X`-side line-point data and a `Z` point. The probe registers are
irrelevant to every line quantity, so they are set to zero. -/
def ofLPX (d : LPData F m) (uZ : Point F m) : Content F m := ⟨d.pt, uZ, d.s, d.raw, 0, 0⟩

/-- A content assembled from `Z`-side line-point data and an `X` point. -/
def ofLPZ (d : LPData F m) (uX : Point F m) : Content F m := ⟨uX, d.pt, d.s, d.raw, 0, 0⟩

@[simp] theorem lpX_ofLPX (d : LPData F m) (uZ : Point F m) : (ofLPX d uZ).lpX = d := rfl
@[simp] theorem lpZ_ofLPZ (d : LPData F m) (uX : Point F m) : (ofLPZ d uX).lpZ = d := rfl
@[simp] theorem uZ_ofLPX (d : LPData F m) (uZ : Point F m) : (ofLPX d uZ).uZ = uZ := rfl
@[simp] theorem uX_ofLPX (d : LPData F m) (uZ : Point F m) : (ofLPX d uZ).uX = d.pt := rfl
@[simp] theorem uX_ofLPZ (d : LPData F m) (uX : Point F m) : (ofLPZ d uX).uX = uX := rfl
@[simp] theorem uZ_ofLPZ (d : LPData F m) (uX : Point F m) : (ofLPZ d uX).uZ = d.pt := rfl

/-! ## The three splittings, on each of the two sample spaces

Each pair of equivalences isolates the same part of the sample --- the part a hypothesis of the
pasting lemma can depend on --- on the content side and on the product side. `avg_comp_equiv_fst`
then says both uniform averages equal the uniform average over that part. -/

/-- A content splits as (its `X` data, its `Z` point) and its probes. -/
def contentSplitX : Content F m ≃ (LPData F m × Point F m) × (F × F) where
  toFun c := ((c.lpX, c.uZ), (c.rX, c.rZ))
  invFun p := ⟨p.1.1.pt, p.1.2, p.1.1.s, p.1.1.raw, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A pair of line-point data splits as (the `X` one, the `Z` one's point) and the `Z` one's line. -/
def pairSplitX : LPData F m × LPData F m ≃ (LPData F m × Point F m) × (F × Point F m) where
  toFun p := ((p.1, p.2.pt), (p.2.s, p.2.raw))
  invFun q := (q.1.1, ⟨q.1.2, q.2.1, q.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The mirror of `contentSplitX`. -/
def contentSplitZ : Content F m ≃ (LPData F m × Point F m) × (F × F) where
  toFun c := ((c.lpZ, c.uX), (c.rX, c.rZ))
  invFun p := ⟨p.1.2, p.1.1.pt, p.1.1.s, p.1.1.raw, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The mirror of `pairSplitX`. -/
def pairSplitZ : LPData F m × LPData F m ≃ (LPData F m × Point F m) × (F × Point F m) where
  toFun p := ((p.2, p.1.pt), (p.1.s, p.1.raw))
  invFun q := (⟨q.1.2, q.2.1, q.2.2⟩, q.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A content splits as its two points and everything else. -/
def contentSplitPts :
    Content F m ≃ (Point F m × Point F m) × (F × Point F m × F × F) where
  toFun c := ((c.uX, c.uZ), (c.s, c.v, c.rX, c.rZ))
  invFun p := ⟨p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A pair of line-point data splits as its two points and the two lines. -/
def pairSplitPts : LPData F m × LPData F m
    ≃ (Point F m × Point F m) × ((F × Point F m) × (F × Point F m)) where
  toFun p := ((p.1.pt, p.2.pt), ((p.1.s, p.1.raw), (p.2.s, p.2.raw)))
  invFun q := (⟨q.1.1, q.2.1.1, q.2.1.2⟩, ⟨q.1.2, q.2.2.1, q.2.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## The three laws that agree -/

/-- **One side's data together with the other side's point has the same law under a content as
under a product.** The `X` version: every marginal consistency and every collision term of the
pasting lemma at the `X` line is a quantity of this shape. -/
theorem avg_content_eq_pair_X (H : LPData F m → Point F m → ℝ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * H c.lpX c.uZ
      = ∑ p : LPData F m × LPData F m,
          (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * H p.1 p.2.pt :=
  (avg_comp_equiv_fst contentSplitX (fun q => H q.1 q.2)).trans
    (avg_comp_equiv_fst pairSplitX (fun q => H q.1 q.2)).symm

/-- The `Z` version. -/
theorem avg_content_eq_pair_Z (H : LPData F m → Point F m → ℝ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * H c.lpZ c.uX
      = ∑ p : LPData F m × LPData F m,
          (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * H p.2 p.1.pt :=
  (avg_comp_equiv_fst contentSplitZ (fun q => H q.1 q.2)).trans
    (avg_comp_equiv_fst pairSplitZ (fun q => H q.1 q.2)).symm

/-- **The two points have the same law under a content as under a product.** This is what carries
the combined point measurement's consistency across. -/
theorem avg_content_eq_pair_pts (H : Point F m → Point F m → ℝ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * H c.uX c.uZ
      = ∑ p : LPData F m × LPData F m,
          (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * H p.1.pt p.2.pt :=
  (avg_comp_equiv_fst contentSplitPts (fun q => H q.1 q.2)).trans
    (avg_comp_equiv_fst pairSplitPts (fun q => H q.1 q.2)).symm

/-- One side's data on its own, as the special case that ignores the other side's point. -/
theorem avg_content_eq_pair_X' (H : LPData F m → ℝ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * H c.lpX
      = ∑ p : LPData F m × LPData F m,
          (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * H p.1 :=
  avg_content_eq_pair_X (fun d _ => H d)

theorem avg_content_eq_pair_Z' (H : LPData F m → ℝ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * H c.lpZ
      = ∑ p : LPData F m × LPData F m,
          (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * H p.2 :=
  avg_content_eq_pair_Z (fun d _ => H d)

/-! ## The change of variables, at the product

`sum_content_shift_gen` is the device that makes the point uniform on its line without forming a
conditional distribution, and nothing in it is about contents: it needs a finite nonempty sample
space, a shift action on it, and a direction the shift does not move. Stated that way it applies to a
*pair* of line-point data with the shift acting on the `X` side only, which is what the product form
of the pasting lemma's collision term needs.
-/

section Shift

variable {α : Type*} [Fintype α] [Nonempty α] {V : Type*} [AddCommGroup V] [Module F V]

/-- **Shifting along a direction the shift does not move is a bijection**, with the opposite shift
as inverse. -/
theorem bijective_shift {sh : V → α → α} (hzero : ∀ a, sh 0 a = a)
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
averaging it over (sample, shift) pairs with the shift applied. -/
theorem sum_shift_gen {sh : V → α → α} (hzero : ∀ a, sh 0 a = a)
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

end Shift

/-! ### The shift on a pair, and what it leaves alone -/

variable [Algebra (ZMod 2) F] {hm : m ∣ Fintype.card F}

/-- The shift on a pair of line-point data: move the `X` side's point, leave the `Z` side alone. -/
def pairShift (w : Point F m) (p : LPData F m × LPData F m) : LPData F m × LPData F m :=
  (⟨p.1.pt + w, p.1.s, p.1.raw⟩, p.2)

/-- The `X` line's direction, read off a pair through the content the `X` side presents. -/
def pairDirX (PX : LinePres F m hm .X) (p : LPData F m × LPData F m) : Point F m :=
  PX.dir (ofLPX p.1 p.2.pt)

/-- Shifting the pair shifts the `X` side's content, which is what the `LinePres` invariances are
stated about. -/
theorem ofLPX_pairShift (w : Point F m) (p : LPData F m × LPData F m) :
    ofLPX (pairShift w p).1 (pairShift w p).2.pt
      = Content.shiftPt .X w (ofLPX p.1 p.2.pt) := rfl

/-- The same shift moves the `Z` side's content only in its *other* point, which the `_other`
invariances say changes nothing on the `Z` line. -/
theorem ofLPZ_pairShift (w : Point F m) (p : LPData F m × LPData F m) :
    ofLPZ (pairShift w p).2 (pairShift w p).1.pt
      = Content.shiftPt .X w (ofLPZ p.2 p.1.pt) := rfl

@[simp] theorem pairShift_zero (p : LPData F m × LPData F m) : pairShift 0 p = p := by
  rw [pairShift, add_zero]

theorem pairShift_add (w w' : Point F m) (p : LPData F m × LPData F m) :
    pairShift w' (pairShift w p) = pairShift (w + w') p := by
  rw [pairShift, pairShift, pairShift, add_assoc]

theorem pairDirX_shift (PX : LinePres F m hm .X) (p : LPData F m × LPData F m) (w : Point F m) :
    pairDirX PX (pairShift w p) = pairDirX PX p := by
  rw [pairDirX, pairDirX, ofLPX_pairShift, PX.dir_shift]

/-- **The change of variables at the product**: averaging over pairs is averaging over
(pair, shift), the shift moving the `X` point along the `X` line. -/
theorem sum_pair_shift (PX : LinePres F m hm .X) (g : LPData F m × LPData F m → ℝ) :
    ∑ i : (LPData F m × LPData F m) × F,
        ((Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
          * g (pairShift (i.2 • pairDirX PX i.1) i.1)
      = ∑ p : LPData F m × LPData F m,
          (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * g p :=
  sum_shift_gen pairShift_zero pairShift_add (fun p w => pairDirX_shift PX p w) g

end MIPRE.QLD
