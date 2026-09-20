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

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]

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

`MIPRE.QLD.sum_shift_gen` (in `Lines.lean`, where the content instance of it lives) needs only a
finite sample space, a shift action on it, and a direction the shift does not move. So it applies to a
*pair* of line-point data with the shift acting on the `X` side only, which is what the product form
of the pasting lemma's collision term needs; all that is required here is the action and its three
properties.
-/


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

/-! ## `lem:qld-pairs-of-lines`, at a product of two independent line-point pairs

`pairs_of_lines_gen` asks for a content per side and a shift both sides see as a shift of the `X`
point. A pair of line-point data supplies exactly that: each side's content is its own point, seed
and raw direction, with the *other* side's point filled in as the content's other point --- which no
quantity of that side's line depends on --- and `pairShift` moves the `X` point. So the product form
is an instance, with nothing to prove beyond the two `rfl`s below.
-/

/-- The `X`-side content a pair of line-point data presents: the `X` side's own line-point data, with
the `Z` side's point as the content's other point. -/
def pairCX (p : LPData F m × LPData F m) : Content F m := ofLPX p.1 p.2.pt

/-- The `Z`-side content. Its seed and raw direction are the `Z` side's own, independent of the `X`
side's --- which is the whole difference from a single content. -/
def pairCZ (p : LPData F m × LPData F m) : Content F m := ofLPZ p.2 p.1.pt

@[simp] theorem pairDirX_eq (PX : LinePres F m hm .X) (p : LPData F m × LPData F m) :
    pairDirX PX p = PX.dir (pairCX p) := rfl

@[simp] theorem pairCX_pairShift (w : Point F m) (p : LPData F m × LPData F m) :
    pairCX (pairShift w p) = Content.shiftPt .X w (pairCX p) := rfl

@[simp] theorem pairCZ_pairShift (w : Point F m) (p : LPData F m × LPData F m) :
    pairCZ (pairShift w p) = Content.shiftPt .X w (pairCZ p) := rfl

variable {d : ℕ} {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {ε : ℝ}

/-! ### The combined point measurement, indexed by the pair of points

`lem:qld-combined-points` is stated over the Pauli basis test's own contents, and the measurement it
produces is indexed by them. Every quantity it is bounded against depends on the content only through
its **two points**, so the same construction runs at the pair of points and gives a measurement that
any sample space carrying two points can use --- in particular a pair of line-point data, where the
content-indexed version would have to be fed contents with zeroed probes and the averages would not
match. -/

theorem sum_uniform_pts :
    ∑ _x : Point F m × Point F m, (Fintype.card (Point F m × Point F m) : ℝ)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/-- **A quantity of the two points has the same law under a content as under a uniform pair of
points.** -/
theorem avg_content_eq_pts (H : Point F m → Point F m → ℝ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * H c.uX c.uZ
      = ∑ x : Point F m × Point F m, (Fintype.card (Point F m × Point F m) : ℝ)⁻¹ * H x.1 x.2 :=
  avg_comp_equiv_fst contentSplitPts (fun q => H q.1 q.2)

set_option maxHeartbeats 1600000 in
/-- **`lem:qld-combined-points`, indexed by the pair of points.** Verbatim the content-indexed
statement with the content replaced by the two points it contributes, which is all four inputs of
the joint-measurement construction see. -/
theorem combined_points_pts (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) :
    ∃ (QA : Point F m × Point F m → F × F →
        Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ)
      (QB : Point F m × Point F m → F × F →
        Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ),
      (∀ x, IsPVM (QA x)) ∧ (∀ x, IsPVM (QB x))
      ∧ (∀ x p, (ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))ᴴ
            * (QA x p * ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))
          = sand (hatMats MA .X x.1) (hatMats MA .Z x.2) p)
      ∧ (∀ x p, (ancillaEmbed (dB × Anc F m) ((0 : F), (0 : F)))ᴴ
            * (QB x p * ancillaEmbed (dB × Anc F m) ((0 : F), (0 : F)))
          = sand (hatMats MB .X x.1) (hatMats MB .Z x.2) p)
      ∧ (∑ x : Point F m × Point F m, (Fintype.card (Point F m × Point F m) : ℝ)⁻¹ *
            ∑ p : F × F, xSqNorm (extHat (m := m) ψ) (QA x p) (QB x p)
          ≤ 2 * deltaQ ε)
      ∧ (∑ x : Point F m × Point F m, (Fintype.card (Point F m × Point F m) : ℝ)⁻¹ *
            ∑ p : F × F, xSqNorm (extHat (m := m) ψ) (QA x p)
              (aOp (hatMats MB .Z x.2 p.2 * hatMats MB .X x.1 p.1))
          ≤ 4 * deltaQ ε + 115352832 * ε)
      ∧ (∑ x : Point F m × Point F m, (Fintype.card (Point F m × Point F m) : ℝ)⁻¹ *
            ∑ p : F × F, xSqNorm (extHat (m := m) ψ) (QA x p)
              (aOp (hatMats MB .X x.1 p.1 * hatMats MB .Z x.2 p.2))
          ≤ 4 * deltaQ ε + 461411328 * ε) := by
  classical
  have hΓ : Real.sqrt (57676416 * ε) + Real.sqrt (57676416 * ε) + Real.sqrt (172 * ε / 2)
      + 172 * ε / 2 = deltaQ ε := by
    rw [deltaQ, show (172 : ℝ) * ε / 2 = 86 * ε from by ring]
    ring
  obtain ⟨QA, QB, hPA, hPB, hkA, hkB, h1, h2, h3⟩ :=
    exists_projective_joint (A := F) (ι := Point F m × Point F m)
      (w := fun _ : Point F m × Point F m => (Fintype.card (Point F m × Point F m) : ℝ)⁻¹)
      (fun _ => by positivity) sum_uniform_pts (hatVec_unit hψ) ((0 : F), (0 : F))
      (X := fun x : Point F m × Point F m => hatMats MA .X x.1)
      (Z := fun x : Point F m × Point F m => hatMats MA .Z x.2)
      (X' := fun x : Point F m × Point F m => hatMats MB .X x.1)
      (Z' := fun x : Point F m × Point F m => hatMats MB .Z x.2)
      (fun x => isPVM_hatMats hprojA .X x.1) (fun x => isPVM_hatMats hprojA .Z x.2)
      (fun x => isPVM_hatMats hprojB .X x.1) (fun x => isPVM_hatMats hprojB .Z x.2)
      (cA := 57676416 * ε) (cB := 57676416 * ε) (α := 172 * ε) (β := 172 * ε)
      (le_trans (le_of_eq (avg_content_eq_pts (F := F) (m := m) fun x z =>
        ∑ p : F × F, stateSqNorm (hatVec (F := F) (m := m) ψ) (hatComm MA x z p.1 p.2)).symm)
        (sum_content_hatComm_le (MB := MB) hψ hfail))
      (le_trans (le_of_eq (avg_content_eq_pts (F := F) (m := m) fun x z =>
        ∑ p : F × F, ‖stateVecB (hatVec (F := F) (m := m) ψ) (hatComm MB x z p.1 p.2)‖ ^ 2).symm)
        (sum_content_hatComm_le_B (MA := MA) hψ hfail))
      (le_trans (le_of_eq (avg_content_eq_pts (F := F) (m := m) fun x _ =>
        ∑ a : F, xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA .X x a)
          (hatMats MB .X x a)).symm)
        (sum_content_hatMats_consistency (MB := MB) hψ hfail .X))
      (le_trans (le_of_eq (avg_content_eq_pts (F := F) (m := m) fun _ z =>
        ∑ b : F, xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA .Z z b)
          (hatMats MB .Z z b)).symm)
        (sum_content_hatMats_consistency (MB := MB) hψ hfail .Z))
  refine ⟨QA, QB, hPA, hPB, hkA, hkB, ?_, ?_, ?_⟩
  · rw [extHat, ← hΓ]; exact h1
  · rw [extHat, ← hΓ, show (115352832 : ℝ) * ε = 2 * (57676416 * ε) from by ring]; exact h2
  · rw [extHat, ← hΓ, show (461411328 : ℝ) * ε = 8 * (57676416 * ε) from by ring]; exact h3

/-- **`lem:qld-pairs-of-lines`, on a product of two independent line-point laws.** The instance of
`pairs_of_lines_gen` at `kX = pairCX`, `kZ = pairCZ`, `sh = pairShift`: this is the form
`lem:qld-padded-lines` needs, where the `X` line and the `Z` line are drawn independently. -/
theorem pairs_of_lines_prod (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    {QA : LPData F m × LPData F m → F × F →
      Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ}
    (hQA : ∀ p, IsPVM (QA p)) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) {δ η εc : ℝ}
    (hmargX : ∑ p : LPData F m × LPData F m,
        (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ x : F,
          xSqNorm (extHat (m := m) ψ) (∑ q : F, QA p (x, q))
            (aOp (PX.lineEvalMats d MB (pairCX p) x)) ≤ δ)
    (hmargZ : ∑ p : LPData F m × LPData F m,
        (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ b : F,
          xSqNorm (extHat (m := m) ψ) (∑ q : F, QA p (q, b))
            (aOp (PZ.lineEvalMats d MB (pairCZ p) b)) ≤ δ)
    (hselfX : ∑ p : LPData F m × LPData F m,
        (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ *
          ∑ f : LinePoly F (m * d), xSqNorm (extHat (m := m) ψ)
            (aOp (PX.lineMats d MA (pairCX p) f)) (aOp (PX.lineMats d MB (pairCX p) f)) ≤ η)
    (hcoll : ∑ p : LPData F m × LPData F m,
        (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * collProb PX d (pairCX p) ≤ εc) :
    1 - ∑ p : LPData F m × LPData F m,
        (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ r : F × F,
          bornProb (extHat (m := m) ψ) (QA p r)
            (∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
                LinePoly.eval q.1 (PX.param (pairCX p)) = r.1
                  ∧ LinePoly.eval q.2 (PZ.param (pairCZ p)) = r.2,
              pasteLine PX PZ d MB (pairCX p) (pairCZ p) q)
      ≤ δ / 2 + Real.sqrt (δ / 2) + Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * εc) :=
  pairs_of_lines_gen PX PZ pairCX pairCZ (sh := pairShift) pairShift_zero pairShift_add
    pairCX_pairShift pairCZ_pairShift hQA hψ hprojA hprojB hmargX hmargZ hselfX hcoll

/-! ## The line data of one side factors through that side's line-point data

Every quantity of the `X` line --- the measurement, the parameter, the collision probability ---
reads the content only through its `X` point, its seed and its raw direction, which is exactly
`Content.lpX`. Saying so once is what lets a content-level bound be read as a bound on the product,
through `avg_content_eq_pair_X`: the two laws agree on quantities of `(lpX, uZ)`, and this is the
proof that the quantities in question are of that shape.

The hypothesis is the three data a `LinePres` carries. Both line presentations satisfy it by `rfl`:
`dirOf` and `ddirOf` read the seed and the raw direction, the base point is the canonical
representative of the side's own point, and `Content.question` at a line type reads nothing else. -/

section Factor

variable {M : Question F m → POVM (Answer F m d) dB}

/-- `PX` reads the content only through its `X` line-point data. -/
def FactorsX (PX : LinePres F m hm .X) : Prop :=
  ∀ (c : Content F m) (u : Point F m),
    PX.base (ofLPX c.lpX u) = PX.base c ∧ PX.dir (ofLPX c.lpX u) = PX.dir c
      ∧ (ofLPX c.lpX u).question hm PX.ty = c.question hm PX.ty

/-- `PZ` reads the content only through its `Z` line-point data. -/
def FactorsZ (PZ : LinePres F m hm .Z) : Prop :=
  ∀ (c : Content F m) (u : Point F m),
    PZ.base (ofLPZ c.lpZ u) = PZ.base c ∧ PZ.dir (ofLPZ c.lpZ u) = PZ.dir c
      ∧ (ofLPZ c.lpZ u).question hm PZ.ty = c.question hm PZ.ty

theorem factorsX_aPres : FactorsX (aPres hm .X) := fun _ _ => ⟨rfl, rfl, rfl⟩
theorem factorsX_dPres : FactorsX (dPres hm .X) := fun _ _ => ⟨rfl, rfl, rfl⟩
theorem factorsZ_aPres : FactorsZ (aPres hm .Z) := fun _ _ => ⟨rfl, rfl, rfl⟩
theorem factorsZ_dPres : FactorsZ (dPres hm .Z) := fun _ _ => ⟨rfl, rfl, rfl⟩

theorem lineMats_ofLPX {PX : LinePres F m hm .X} (hfac : FactorsX PX) (c : Content F m)
    (u : Point F m) : PX.lineMats d M (ofLPX c.lpX u) = PX.lineMats d M c :=
  congrArg (fun Q : POVM (LinePoly F (m * d)) (dB × Anc F m) => fun f => ((Q.mats f).val))
    (hatLinePOVM_congr hm M .X PX.ty PX.base PX.dir (hfac c u).2.2 (hfac c u).1 (hfac c u).2.1)

theorem param_ofLPX {PX : LinePres F m hm .X} (hfac : FactorsX PX) (c : Content F m)
    (u : Point F m) : PX.param (ofLPX c.lpX u) = PX.param c := by
  rw [LinePres.param, LinePres.param, (hfac c u).1, (hfac c u).2.1]
  rfl

theorem lineEvalMats_ofLPX {PX : LinePres F m hm .X} (hfac : FactorsX PX) (c : Content F m)
    (u : Point F m) : PX.lineEvalMats d M (ofLPX c.lpX u) = PX.lineEvalMats d M c := by
  have hQ : hatLinePOVM (m * d) hm M .X PX.ty PX.base PX.dir (ofLPX c.lpX u)
      = hatLinePOVM (m * d) hm M .X PX.ty PX.base PX.dir c :=
    hatLinePOVM_congr hm M .X PX.ty PX.base PX.dir (hfac c u).2.2 (hfac c u).1 (hfac c u).2.1
  show (fun a => ((((hatLinePOVM (m * d) hm M .X PX.ty PX.base PX.dir (ofLPX c.lpX u)).map
    fun f => LinePoly.eval f (PX.param (ofLPX c.lpX u))).mats a).val)) = _
  rw [hQ, param_ofLPX hfac c u]
  rfl

theorem collProb_ofLPX {PX : LinePres F m hm .X} (hfac : FactorsX PX) (c : Content F m)
    (u : Point F m) : collProb PX d (ofLPX c.lpX u) = collProb PX d c := by
  rw [collProb, collProb, (hfac c u).2.1]

theorem lineMats_ofLPZ {PZ : LinePres F m hm .Z} (hfac : FactorsZ PZ) (c : Content F m)
    (u : Point F m) : PZ.lineMats d M (ofLPZ c.lpZ u) = PZ.lineMats d M c :=
  congrArg (fun Q : POVM (LinePoly F (m * d)) (dB × Anc F m) => fun f => ((Q.mats f).val))
    (hatLinePOVM_congr hm M .Z PZ.ty PZ.base PZ.dir (hfac c u).2.2 (hfac c u).1 (hfac c u).2.1)

theorem param_ofLPZ {PZ : LinePres F m hm .Z} (hfac : FactorsZ PZ) (c : Content F m)
    (u : Point F m) : PZ.param (ofLPZ c.lpZ u) = PZ.param c := by
  rw [LinePres.param, LinePres.param, (hfac c u).1, (hfac c u).2.1]
  rfl

theorem lineEvalMats_ofLPZ {PZ : LinePres F m hm .Z} (hfac : FactorsZ PZ) (c : Content F m)
    (u : Point F m) : PZ.lineEvalMats d M (ofLPZ c.lpZ u) = PZ.lineEvalMats d M c := by
  have hQ : hatLinePOVM (m * d) hm M .Z PZ.ty PZ.base PZ.dir (ofLPZ c.lpZ u)
      = hatLinePOVM (m * d) hm M .Z PZ.ty PZ.base PZ.dir c :=
    hatLinePOVM_congr hm M .Z PZ.ty PZ.base PZ.dir (hfac c u).2.2 (hfac c u).1 (hfac c u).2.1
  show (fun a => ((((hatLinePOVM (m * d) hm M .Z PZ.ty PZ.base PZ.dir (ofLPZ c.lpZ u)).map
    fun f => LinePoly.eval f (PZ.param (ofLPZ c.lpZ u))).mats a).val)) = _
  rw [hQ, param_ofLPZ hfac c u]
  rfl

/-! ### The four bounds, read on the product

Each is the content-level bound with `avg_content_eq_pair_X` or `avg_content_eq_pair_Z` applied and
the factoring lemmas used to put the summand in the shape those identities need. -/

set_option maxHeartbeats 1000000 in
theorem avg_pair_eq_content_X {PX : LinePres F m hm .X} (hfac : FactorsX PX)
    (G : Point F m → Point F m → (F → Matrix (dB × Anc F m) (dB × Anc F m) ℂ) → ℝ) :
    ∑ p : LPData F m × LPData F m, (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ *
        G p.1.pt p.2.pt (PX.lineEvalMats d M (pairCX p))
      = ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        G c.uX c.uZ (PX.lineEvalMats d M c) := by
  have hmid := avg_content_eq_pair_X
    (fun D u => G D.pt u (PX.lineEvalMats d M (ofLPX D 0)))
  have hL : ∀ p : LPData F m × LPData F m,
      (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ *
          G p.1.pt p.2.pt (PX.lineEvalMats d M (pairCX p))
        = (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ *
          G p.1.pt p.2.pt (PX.lineEvalMats d M (ofLPX p.1 0)) := fun p => by
    rw [← lineEvalMats_ofLPX hfac (pairCX p) 0]
    rfl
  have hR : ∀ c : Content F m,
      (Fintype.card (Content F m) : ℝ)⁻¹ *
          G c.lpX.pt c.uZ (PX.lineEvalMats d M (ofLPX c.lpX 0))
        = (Fintype.card (Content F m) : ℝ)⁻¹ * G c.uX c.uZ (PX.lineEvalMats d M c) := fun c => by
    rw [lineEvalMats_ofLPX hfac c 0]
    rfl
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hL p, ← hmid,
    Finset.sum_congr rfl fun c (_ : c ∈ univ) => hR c]

set_option maxHeartbeats 1000000 in
theorem avg_pair_eq_content_Z {PZ : LinePres F m hm .Z} (hfac : FactorsZ PZ)
    (G : Point F m → Point F m → (F → Matrix (dB × Anc F m) (dB × Anc F m) ℂ) → ℝ) :
    ∑ p : LPData F m × LPData F m, (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ *
        G p.1.pt p.2.pt (PZ.lineEvalMats d M (pairCZ p))
      = ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        G c.uX c.uZ (PZ.lineEvalMats d M c) := by
  have hmid := avg_content_eq_pair_Z
    (fun D u => G u D.pt (PZ.lineEvalMats d M (ofLPZ D 0)))
  have hL : ∀ p : LPData F m × LPData F m,
      (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ *
          G p.1.pt p.2.pt (PZ.lineEvalMats d M (pairCZ p))
        = (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ *
          G p.1.pt p.2.pt (PZ.lineEvalMats d M (ofLPZ p.2 0)) := fun p => by
    rw [← lineEvalMats_ofLPZ hfac (pairCZ p) 0]
    rfl
  have hR : ∀ c : Content F m,
      (Fintype.card (Content F m) : ℝ)⁻¹ *
          G c.uX c.lpZ.pt (PZ.lineEvalMats d M (ofLPZ c.lpZ 0))
        = (Fintype.card (Content F m) : ℝ)⁻¹ * G c.uX c.uZ (PZ.lineEvalMats d M c) := fun c => by
    rw [lineEvalMats_ofLPZ hfac c 0]
    rfl
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hL p, ← hmid,
    Finset.sum_congr rfl fun c (_ : c ∈ univ) => hR c]

set_option maxHeartbeats 1000000 in
/-- The fine self-consistency of the `X` line measurement involves no point at all, so the transfer
is the point-free form of the same identity. -/
theorem avg_pair_eq_content_X_self {PX : LinePres F m hm .X} (hfac : FactorsX PX)
    (G : (LinePoly F (m * d) → Matrix (dA × Anc F m) (dA × Anc F m) ℂ) →
      (LinePoly F (m * d) → Matrix (dB × Anc F m) (dB × Anc F m) ℂ) → ℝ) :
    ∑ p : LPData F m × LPData F m, (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ *
        G (PX.lineMats d MA (pairCX p)) (PX.lineMats d MB (pairCX p))
      = ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        G (PX.lineMats d MA c) (PX.lineMats d MB c) := by
  have hmid := avg_content_eq_pair_X'
    (fun D => G (PX.lineMats d MA (ofLPX D 0)) (PX.lineMats d MB (ofLPX D 0)))
  have hL : ∀ p : LPData F m × LPData F m,
      (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ *
          G (PX.lineMats d MA (pairCX p)) (PX.lineMats d MB (pairCX p))
        = (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ *
          G (PX.lineMats d MA (ofLPX p.1 0)) (PX.lineMats d MB (ofLPX p.1 0)) := fun p => by
    rw [← lineMats_ofLPX hfac (pairCX p) 0 (M := MA), ← lineMats_ofLPX hfac (pairCX p) 0 (M := MB)]
    rfl
  have hR : ∀ c : Content F m,
      (Fintype.card (Content F m) : ℝ)⁻¹ *
          G (PX.lineMats d MA (ofLPX c.lpX 0)) (PX.lineMats d MB (ofLPX c.lpX 0))
        = (Fintype.card (Content F m) : ℝ)⁻¹ *
          G (PX.lineMats d MA c) (PX.lineMats d MB c) := fun c => by
    rw [lineMats_ofLPX hfac c 0 (M := MA), lineMats_ofLPX hfac c 0 (M := MB)]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hL p, ← hmid,
    Finset.sum_congr rfl fun c (_ : c ∈ univ) => hR c]

/-- The collision probability reads only the direction, so it transfers the same way. -/
theorem avg_pair_eq_content_X_collProb {PX : LinePres F m hm .X} (hfac : FactorsX PX) :
    ∑ p : LPData F m × LPData F m, (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ *
        collProb PX d (pairCX p)
      = ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * collProb PX d c := by
  have hmid := avg_content_eq_pair_X' (fun D => collProb PX d (ofLPX D 0))
  have hL : ∀ p : LPData F m × LPData F m,
      (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * collProb PX d (pairCX p)
        = (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹
          * collProb PX d (ofLPX p.1 0) := fun p => by
    rw [← collProb_ofLPX hfac (pairCX p) 0]
    rfl
  have hR : ∀ c : Content F m,
      (Fintype.card (Content F m) : ℝ)⁻¹ * collProb PX d (ofLPX c.lpX 0)
        = (Fintype.card (Content F m) : ℝ)⁻¹ * collProb PX d c := fun c => by
    rw [collProb_ofLPX hfac c 0]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hL p, ← hmid,
    Finset.sum_congr rfl fun c (_ : c ∈ univ) => hR c]

end Factor

/-! ## `lem:qld-pairs-of-lines` on the product, from the game

The product form of the pasting conclusion, with only game-level hypotheses on the `X` and `Z` line
presentations. Every input is the content-level one of `pairs_of_lines_of_items`, read on the product
through the four transfer identities above; the combined point measurement is the one indexed by the
pair of points, which is what makes the reading possible. -/

section Game

set_option maxHeartbeats 1600000 in
theorem pairs_of_lines_prod_of_items (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    (hfacX : FactorsX PX) (hfacZ : FactorsZ PZ)
    (hX1 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        xSqNorm (hatVec (F := F) (m := m) ψ) (PX.lineMats d MA c f)
          (PX.lineMats d MB c f) ≤ 172 * ε)
    (hX2 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA .X (c.pt .X) a)
          (PX.lineEvalMats d MB c a) ≤ 172 * ε)
    (hZ2 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ b : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA .Z (c.pt .Z) b)
          (PZ.lineEvalMats d MB c b) ≤ 172 * ε)
    {εc : ℝ} (hcoll : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
      collProb PX d c ≤ εc) :
    ∃ QA : LPData F m × LPData F m → F × F →
        Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ,
      (∀ p, IsPVM (QA p))
      ∧ (∀ p r, (ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))ᴴ
            * (QA p r * ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))
          = sand (hatMats MA .X p.1.pt) (hatMats MA .Z p.2.pt) r)
      ∧ 1 - ∑ p : LPData F m × LPData F m,
          (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ r : F × F,
          bornProb (extHat (m := m) ψ) (QA p r)
            (∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
                LinePoly.eval q.1 (PX.param (pairCX p)) = r.1
                  ∧ LinePoly.eval q.2 (PZ.param (pairCZ p)) = r.2,
              pasteLine PX PZ d MB (pairCX p) (pairCZ p) q)
        ≤ deltaPairs ε εc := by
  classical
  have hε0 : 0 ≤ ε := le_trans (by
    rw [one_sub_povmValue_eq]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg ((qldGame hm).μ_nonneg x y) (condFail_nonneg hψ x y)) hfail
  obtain ⟨QA0, QB0, hPA, hPB, hkA, hkB, h1, h6, h7⟩ :=
    combined_points_pts (MA := MA) (MB := MB) hψ hfail hprojA hprojB
  refine ⟨fun p => QA0 (p.1.pt, p.2.pt), fun p => hPA _, fun p r => hkA (p.1.pt, p.2.pt) r, ?_⟩
  -- the two ordered-product bounds, read back at the content distribution
  have h6c : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ r : F × F,
      xSqNorm (extHat (m := m) ψ) (QA0 (c.uX, c.uZ) r)
        (aOp (hatMats MB .Z c.uZ r.2 * hatMats MB .X c.uX r.1))
      ≤ 4 * deltaQ ε + 115352832 * ε :=
    le_trans (le_of_eq (avg_content_eq_pts (F := F) (m := m) fun x z =>
      ∑ r : F × F, xSqNorm (extHat (m := m) ψ) (QA0 (x, z) r)
        (aOp (hatMats MB .Z z r.2 * hatMats MB .X x r.1)))) h6
  have h7c : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ r : F × F,
      xSqNorm (extHat (m := m) ψ) (QA0 (c.uX, c.uZ) r)
        (aOp (hatMats MB .X c.uX r.1 * hatMats MB .Z c.uZ r.2))
      ≤ 4 * deltaQ ε + 461411328 * ε :=
    le_trans (le_of_eq (avg_content_eq_pts (F := F) (m := m) fun x z =>
      ∑ r : F × F, xSqNorm (extHat (m := m) ψ) (QA0 (x, z) r)
        (aOp (hatMats MB .X x r.1 * hatMats MB .Z z r.2)))) h7
  -- Bob's point measurement against his own line measurement, on each side
  have hptX := sum_content_normSq_point_line_le (MA := MA) .X PX
    (sum_content_hatMats_consistency (MB := MB) hψ hfail .X) hX2
  have hptZ := sum_content_normSq_point_line_le (MA := MA) .Z PZ
    (sum_content_hatMats_consistency (MB := MB) hψ hfail .Z) hZ2
  -- the two marginal consistencies, at the content distribution
  have hmargXc := sum_content_marg_line_le (MB := MB) .X PX
    (QA := fun c : Content F m => QA0 (c.uX, c.uZ)) (fun c => hPA _) hprojB
    (κ := kappaPairs ε) (η := 2 * (172 * ε) + 2 * (172 * ε))
    (le_trans h6c (by rw [kappaPairs]; nlinarith)) hptX
  have hmargZc := sum_content_marg_line_le (MB := MB) .Z PZ
    (QA := fun c : Content F m => QA0 (c.uX, c.uZ)) (fun c => hPA _) hprojB
    (κ := kappaPairs ε) (η := 2 * (172 * ε) + 2 * (172 * ε))
    (le_trans h7c (le_of_eq (show 4 * deltaQ ε + 461411328 * ε = kappaPairs ε from by
      rw [kappaPairs]))) hptZ
  -- ... read on the product
  have hmargX : ∑ p : LPData F m × LPData F m,
      (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (extHat (m := m) ψ) (∑ q : F, QA0 (p.1.pt, p.2.pt) (a, q))
          (aOp (PX.lineEvalMats d MB (pairCX p) a))
      ≤ 2 * (10 * kappaPairs ε) + 2 * (2 * (172 * ε) + 2 * (172 * ε)) :=
    le_trans (le_of_eq (avg_pair_eq_content_X hfacX fun x z A =>
      ∑ a : F, xSqNorm (extHat (m := m) ψ) (∑ q : F, QA0 (x, z) (a, q)) (aOp (A a)))) hmargXc
  have hmargZ : ∑ p : LPData F m × LPData F m,
      (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ b : F,
        xSqNorm (extHat (m := m) ψ) (∑ q : F, QA0 (p.1.pt, p.2.pt) (q, b))
          (aOp (PZ.lineEvalMats d MB (pairCZ p) b))
      ≤ 2 * (10 * kappaPairs ε) + 2 * (2 * (172 * ε) + 2 * (172 * ε)) :=
    le_trans (le_of_eq (avg_pair_eq_content_Z hfacZ fun x z A =>
      ∑ b : F, xSqNorm (extHat (m := m) ψ) (∑ q : F, QA0 (x, z) (q, b)) (aOp (A b)))) hmargZc
  -- the fine self-consistency, transported to the enlarged space and then to the product
  have hselfc : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
      ∑ f : LinePoly F (m * d), xSqNorm (extHat (m := m) ψ) (aOp (PX.lineMats d MA c f))
        (aOp (PX.lineMats d MB c f)) ≤ 172 * ε := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
      congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
        (Finset.sum_congr rfl fun f _ => ?_))) hX1
    rw [extHat, xSqNorm_extVec2_aOp _ _ _
      ((PX.isPVM_lineMats d hprojA c).isSelfAdjoint f)]
  have hself : ∑ p : LPData F m × LPData F m,
      (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        xSqNorm (extHat (m := m) ψ) (aOp (PX.lineMats d MA (pairCX p) f))
          (aOp (PX.lineMats d MB (pairCX p) f)) ≤ 172 * ε :=
    le_trans (le_of_eq (avg_pair_eq_content_X_self hfacX fun A B =>
      ∑ f : LinePoly F (m * d), xSqNorm (extHat (m := m) ψ) (aOp (A f)) (aOp (B f)))) hselfc
  have hcollp : ∑ p : LPData F m × LPData F m,
      (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹ * collProb PX d (pairCX p) ≤ εc :=
    le_trans (le_of_eq (avg_pair_eq_content_X_collProb hfacX)) hcoll
  exact le_trans (pairs_of_lines_prod PX PZ (fun p => hPA _) hψ hprojA hprojB
    hmargX hmargZ hself hcollp) (le_of_eq (by rw [deltaPairs, deltaPairsD]))

end Game

end MIPRE.QLD
