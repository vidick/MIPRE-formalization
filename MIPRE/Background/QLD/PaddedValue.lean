/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.PaddedStrategy

/-!
# The value of the padded strategy

`lem:qld-global-success`: the padded strategy of `PaddedStrategy.lean` wins the seeded low
individual degree test at `(q, 4m, d, 1)` with probability `1 - O(δ_combine + δ_Q + md/q)`.

The failure probability is the average over the verifier's samples of the conditional failure at
the two questions the sample generates (`one_sub_povmValue_clGame`), and the sample splits into the
ordered pair of types and the ambient triple `(u, s, raw)` (`sum_sample_eq`). Each of the nine type
pairs is bounded by an agreement defect of two families of POVMs indexed by the ambient triple,
averaged uniformly:

* a line type against `point`, in either order, by the agreement of the line measurement read at
  the sample's point with the opposite party's padded point measurement, which
  `lem:qld-padded-lines`
  bounds (`one_sub_agreeSum_lineEval_pt_le`, `one_sub_agreeSum_pt_lineEval_le`);
* `point` against `point` by the agreement of the two padded point measurements, which
  `lem:qld-combined-points` bounds through the compressions (`one_sub_agreeSum_pt_pt_le`);
* a line type against itself by polynomial separation
  (`one_sub_sum_bornProb_le_avg_eval`): the two line measurements disagree only if they disagree
  when read at a uniformly random parameter, up to `(md + 1)/q`, and that disagreement is bounded
  through the agreement triangle `fact:triangle-for-simeq` by the three defects above
  (`one_sub_agreeSum_lineEval_lineEval_le`);
* the two cross pairs are always accepted.

The parameter of the sample's point is uniform on the line once the raw direction is fixed, because
translating the point along the line is a bijection of the sample space that fixes the line
(`sum_lineEval_shift`); a degenerate diagonal direction, for which this fails, has probability at
most `1/q`.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)

/-- The verifier's ambient sample: the point, the seed and the raw direction. -/
abbrev Amb (F : Type*) (m : ℕ) := Point F (4 * m) × F × Point F (4 * m)

/-! ## The families of measurements indexed by the ambient sample -/

section Families

variable {d' : Type} [Fintype d'] [DecidableEq d'] {M : Question F m → POVM (Answer F m d) d'}

/-- The padded point measurement at the sample's point. -/
def ptFam (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) :
    Amb F m → POVM F ((d' × Anc F m) × (F × F)) :=
  fun x => padPt hM x.1

/-- The strategy's line measurement of type `ty` at the line the sample generates. -/
def lineFam (ty : CL.Ty) (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) :
    Amb F m → POVM (LinePoly F (m * d + 1)) ((d' × Anc F m) × (F × F)) :=
  fun x => lineMeas hm hm4 ty hM (CL.rep (lineDir hm4 ty x.2.1 x.2.2) x.1) x.2.1
    (rawSet hm4 ty x.2.1 x.2.2)

/-- The line measurement read at the parameter of the sample's point. -/
def lineEvalFam (ty : CL.Ty) (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) :
    Amb F m → POVM F ((d' × Anc F m) × (F × F)) :=
  fun x => (lineFam hm hm4 ty hM x).map fun f => LinePoly.eval f (lineTau hm4 ty x.1 x.2.1 x.2.2)

end Families

/-! ## Averaging over the raw direction

At a diagonal line question the strategy averages the padded line measurement over the fibre of
the truncated direction, and the sample averages over the raw direction; the two together are the
plain average over the raw direction. -/

theorem sum_inv_card_fiber_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (π : α → β)
    (h : α → ℝ) :
    ∑ a, ((univ.filter fun a' => π a' = π a).card : ℝ)⁻¹
        * ∑ a' ∈ univ.filter (fun a' => π a' = π a), h a'
      = ∑ a', h a' := by
  classical
  rw [← Finset.sum_fiberwise univ π (fun a => ((univ.filter fun a' => π a' = π a).card : ℝ)⁻¹
    * ∑ a' ∈ univ.filter (fun a' => π a' = π a), h a'), ← Finset.sum_fiberwise univ π h]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_congr rfl fun a ha => show ((univ.filter fun a' => π a' = π a).card : ℝ)⁻¹
      * ∑ a' ∈ univ.filter (fun a' => π a' = π a), h a'
      = ((univ.filter fun a' => π a' = b).card : ℝ)⁻¹
        * ∑ a' ∈ univ.filter (fun a' => π a' = b), h a' by
    rw [(Finset.mem_filter.mp ha).2]]
  rw [Finset.sum_const, nsmul_eq_mul]
  by_cases hb : (univ.filter fun a' => π a' = b) = ∅
  · rw [hb]
    simp
  · have hcard : ((univ.filter fun a' => π a' = b).card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hb))
    rw [mul_inv_cancel_left₀ hcard]

omit [Algebra (ZMod 2) F] in
/-- The strategy's raw-direction average composed with the sample's is the plain average. -/
theorem sum_rawSet_fiber (ty : CL.Ty) (s : F) (h : Point F (4 * m) → ℝ) :
    ∑ raw : Point F (4 * m), ((rawSet hm4 ty s raw).card : ℝ)⁻¹
        * ∑ raw' ∈ rawSet hm4 ty s raw, h raw'
      = ∑ raw', h raw' := by
  cases ty
  · have huniv : ∀ raw : Point F (4 * m), rawSet hm4 .point s raw
        = univ.filter fun raw' => (fun _ : Point F (4 * m) => ()) raw' = (fun _ => ()) raw :=
      fun raw => (Finset.filter_true_of_mem fun _ _ => rfl).symm
    simp only [huniv]
    exact sum_inv_card_fiber_sum (fun _ => ()) h
  · have huniv : ∀ raw : Point F (4 * m), rawSet hm4 .aline s raw
        = univ.filter fun raw' => (fun _ : Point F (4 * m) => ()) raw' = (fun _ => ()) raw :=
      fun raw => (Finset.filter_true_of_mem fun _ _ => rfl).symm
    simp only [huniv]
    exact sum_inv_card_fiber_sum (fun _ => ()) h
  · exact sum_inv_card_fiber_sum (zeroBelow (chi hm4 s)) h

/-! ## The line-point agreement is the padded consistency quantity -/

section LinePoint

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  (hMA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hMB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
  (Ψ : ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ)

/-- Alice's pasted line measurement at the sample's data, coarse-grained by the combining map at the
sample's point, against Bob's sandwich there, averaged over the fresh randomness. -/
def lineTermL (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d)
    dB)
    (ty : CL.Ty) (u : Point F (4 * m)) (s : F) (raw' : Point F (4 * m)) : ℝ :=
  (Fintype.card (SubRand F m) : ℝ)⁻¹ * ∑ e : SubRand F m, ∑ a : F,
    bornProb Ψ (lineComb (presOf hm ty .X) (presOf hm ty .Z) d MA
        (pairCX (subPair hm4 hm ty ⟨u, s, raw'⟩ e)) (pairCZ (subPair hm4 hm ty ⟨u, s, raw'⟩ e))
        (alph u) (bet u) a)
      (aOp (ptComb (sand (hatMats MB .X (xBlk u)) (hatMats MB .Z (zBlk u))) (alph u) (bet u) a))

/-- The same with the players exchanged: Alice's sandwich against Bob's pasted line. -/
def lineTermR (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d)
    dB)
    (ty : CL.Ty) (u : Point F (4 * m)) (s : F) (raw' : Point F (4 * m)) : ℝ :=
  (Fintype.card (SubRand F m) : ℝ)⁻¹ * ∑ e : SubRand F m, ∑ a : F,
    bornProb Ψ
      (aOp (ptComb (sand (hatMats MA .X (xBlk u)) (hatMats MA .Z (zBlk u))) (alph u) (bet u) a))
      (lineComb (presOf hm ty .X) (presOf hm ty .Z) d MB
        (pairCX (subPair hm4 hm ty ⟨u, s, raw'⟩ e)) (pairCZ (subPair hm4 hm ty ⟨u, s, raw'⟩ e))
        (alph u) (bet u) a)

/-- The summand of `avgSubAB` for Alice's line against Bob's point. -/
def padGL (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d) dB)
    (ty : CL.Ty) (a b : F) (cX cZ : LPData F m) : ℝ :=
  ∑ v : F, bornProb Ψ
    (lineComb (presOf hm ty .X) (presOf hm ty .Z) d MA (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v)
    (aOp (ptComb (sand (hatMats MB .X cX.pt) (hatMats MB .Z cZ.pt)) a b v))

/-- The summand of `avgSubAB` for Alice's point against Bob's line. -/
def padGR (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d) dB)
    (ty : CL.Ty) (a b : F) (cX cZ : LPData F m) : ℝ :=
  ∑ v : F, bornProb Ψ
    (aOp (ptComb (sand (hatMats MA .X cX.pt) (hatMats MA .Z cZ.pt)) a b v))
    (lineComb (presOf hm ty .X) (presOf hm ty .Z) d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v)

theorem sum_bornProb_lineEvalFam_ptFam (ty : CL.Ty) (hty : ty ≠ .point) (x : Amb F m) :
    ∑ a, bornProb Ψ (((lineEvalFam hm hm4 ty hMA x).mats a).val) (((ptFam hMB x).mats a).val)
      = ((rawSet hm4 ty x.2.1 x.2.2).card : ℝ)⁻¹
          * ∑ raw' ∈ rawSet hm4 ty x.2.1 x.2.2, lineTermL hm hm4 Ψ MA MB ty x.1 x.2.1 raw' := by
  obtain ⟨u, s, raw⟩ := x
  simp only [lineEvalFam, lineFam, ptFam, lineMeas_map_eval_mats hm hm4 ty hty hMA, padPt_mats,
    bornProb_smul_left, bornProb_sum_left, lineTermL, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun raw' _ => Finset.sum_comm

theorem sum_bornProb_ptFam_lineEvalFam (ty : CL.Ty) (hty : ty ≠ .point) (x : Amb F m) :
    ∑ a, bornProb Ψ (((ptFam hMA x).mats a).val) (((lineEvalFam hm hm4 ty hMB x).mats a).val)
      = ((rawSet hm4 ty x.2.1 x.2.2).card : ℝ)⁻¹
          * ∑ raw' ∈ rawSet hm4 ty x.2.1 x.2.2, lineTermR hm hm4 Ψ MA MB ty x.1 x.2.1 raw' := by
  obtain ⟨u, s, raw⟩ := x
  simp only [lineEvalFam, lineFam, ptFam, lineMeas_map_eval_mats hm hm4 ty hty hMB, padPt_mats,
    bornProb_smul_right, bornProb_sum_right, lineTermR, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun raw' _ => Finset.sum_comm

omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem card_amb : (Fintype.card (Amb F m) : ℝ)
    = (Fintype.card F : ℝ) ^ (4 * m) * ((Fintype.card F : ℝ) * (Fintype.card F : ℝ) ^ (4 * m)) := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  push_cast
  ring

omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem card_subRand : (Fintype.card (SubRand F m) : ℝ)
    = ((Fintype.card F : ℝ) * (Fintype.card F : ℝ) ^ m)
      * ((Fintype.card F : ℝ) * (Fintype.card F : ℝ) ^ m) := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  push_cast
  ring

/-- The inner sum of `avgSubAB` at a fixed padded point and raw direction, for Alice's line. -/
theorem sum_padGL_eq (ty : CL.Ty) (s : F) (pt raw : Point F (4 * m)) :
    ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
        padGL hm Ψ MA MB ty (alph pt) (bet pt) (subX hm4 hm ⟨pt, s, raw⟩ eX)
          (subZ hm4 hm ty ⟨pt, s, raw⟩ eZ)
      = (Fintype.card (SubRand F m) : ℝ) * lineTermL hm hm4 Ψ MA MB ty pt s raw := by
  have hcard : (Fintype.card (SubRand F m) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [lineTermL, mul_inv_cancel_left₀ hcard]
  set G : SubRand F m → ℝ := fun e => ∑ a : F,
    bornProb Ψ (lineComb (presOf hm ty .X) (presOf hm ty .Z) d MA
        (pairCX (subPair hm4 hm ty ⟨pt, s, raw⟩ e)) (pairCZ (subPair hm4 hm ty ⟨pt, s, raw⟩ e))
        (alph pt) (bet pt) a)
      (aOp (ptComb (sand (hatMats MB .X (xBlk pt)) (hatMats MB .Z (zBlk pt)))
        (alph pt) (bet pt) a)) with hGdef
  have hG : ∀ eX eZ : F × Point F m, padGL hm Ψ MA MB ty (alph pt) (bet pt)
      (subX hm4 hm ⟨pt, s, raw⟩ eX) (subZ hm4 hm ty ⟨pt, s, raw⟩ eZ) = G (eX, eZ) := by
    intro eX eZ
    simp only [hGdef, padGL, subX_pt, subZ_pt, subPair]
  simp only [hG]
  exact (Fintype.sum_prod_type G).symm

theorem sum_padGR_eq (ty : CL.Ty) (s : F) (pt raw : Point F (4 * m)) :
    ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
        padGR hm Ψ MA MB ty (alph pt) (bet pt) (subX hm4 hm ⟨pt, s, raw⟩ eX)
          (subZ hm4 hm ty ⟨pt, s, raw⟩ eZ)
      = (Fintype.card (SubRand F m) : ℝ) * lineTermR hm hm4 Ψ MA MB ty pt s raw := by
  have hcard : (Fintype.card (SubRand F m) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [lineTermR, mul_inv_cancel_left₀ hcard]
  set G : SubRand F m → ℝ := fun e => ∑ a : F,
    bornProb Ψ
      (aOp (ptComb (sand (hatMats MA .X (xBlk pt)) (hatMats MA .Z (zBlk pt)))
        (alph pt) (bet pt) a))
      (lineComb (presOf hm ty .X) (presOf hm ty .Z) d MB
        (pairCX (subPair hm4 hm ty ⟨pt, s, raw⟩ e)) (pairCZ (subPair hm4 hm ty ⟨pt, s, raw⟩ e))
        (alph pt) (bet pt) a) with hGdef
  have hG : ∀ eX eZ : F × Point F m, padGR hm Ψ MA MB ty (alph pt) (bet pt)
      (subX hm4 hm ⟨pt, s, raw⟩ eX) (subZ hm4 hm ty ⟨pt, s, raw⟩ eZ) = G (eX, eZ) := by
    intro eX eZ
    simp only [hGdef, padGR, subX_pt, subZ_pt, subPair]
  simp only [hG]
  exact (Fintype.sum_prod_type G).symm

theorem avgSubAB_padGL (ty : CL.Ty) (s : F) :
    avgSubAB hm4 hm ty s (padGL hm Ψ MA MB ty)
      = ((Fintype.card F : ℝ) ^ (10 * m + 2))⁻¹ * ((Fintype.card (SubRand F m) : ℝ)
          * ∑ pt : Point F (4 * m), ∑ raw : Point F (4 * m), lineTermL hm hm4 Ψ MA MB ty pt s raw)
          := by
  rw [avgSubAB, sumSubAB]
  congr 1
  simp only [sumSubAt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun pt _ => Finset.sum_congr rfl fun raw _ =>
    sum_padGL_eq hm hm4 Ψ ty s pt raw

theorem avgSubAB_padGR (ty : CL.Ty) (s : F) :
    avgSubAB hm4 hm ty s (padGR hm Ψ MA MB ty)
      = ((Fintype.card F : ℝ) ^ (10 * m + 2))⁻¹ * ((Fintype.card (SubRand F m) : ℝ)
          * ∑ pt : Point F (4 * m), ∑ raw : Point F (4 * m), lineTermR hm hm4 Ψ MA MB ty pt s raw)
          := by
  rw [avgSubAB, sumSubAB]
  congr 1
  simp only [sumSubAt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun pt _ => Finset.sum_congr rfl fun raw _ =>
    sum_padGR_eq hm hm4 Ψ ty s pt raw

omit [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The normalizations agree: the uniform average over the ambient sample is the average over the
seed of the padded average `avgSubAB`. -/
theorem inv_card_amb_eq :
    (Fintype.card (Amb F m) : ℝ)⁻¹
      = (Fintype.card F : ℝ)⁻¹ * (((Fintype.card F : ℝ) ^ (10 * m + 2))⁻¹
          * (Fintype.card (SubRand F m) : ℝ)) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [card_amb, card_subRand]
  field_simp
  ring

/-- **The agreement of Alice's line read at the sample's point with Bob's padded point measurement
is the seed-average of the padded consistency quantity.** -/
theorem agreeSum_lineEvalFam_ptFam (ty : CL.Ty) (hty : ty ≠ .point) :
    agreeSum (uniform (Amb F m)) Ψ (lineEvalFam hm hm4 ty hMA) (ptFam hMB)
      = (Fintype.card F : ℝ)⁻¹ * ∑ s : F, avgSubAB hm4 hm ty s (padGL hm Ψ MA MB ty) := by
  classical
  have hsum : ∑ x : Amb F m, ((rawSet hm4 ty x.2.1 x.2.2).card : ℝ)⁻¹
        * ∑ raw' ∈ rawSet hm4 ty x.2.1 x.2.2, lineTermL hm hm4 Ψ MA MB ty x.1 x.2.1 raw'
      = ∑ s : F, ∑ pt : Point F (4 * m), ∑ raw : Point F (4 * m),
          lineTermL hm hm4 Ψ MA MB ty pt s raw := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => ?_
    exact sum_rawSet_fiber hm4 ty s fun raw' => lineTermL hm hm4 Ψ MA MB ty u s raw'
  simp only [avgSubAB_padGL hm hm4 Ψ ty, agreeSum, uniform,
    sum_bornProb_lineEvalFam_ptFam hm hm4 hMA hMB Ψ ty hty]
  rw [← Finset.mul_sum, hsum, inv_card_amb_eq]
  simp only [← Finset.mul_sum]
  ring

theorem agreeSum_ptFam_lineEvalFam (ty : CL.Ty) (hty : ty ≠ .point) :
    agreeSum (uniform (Amb F m)) Ψ (ptFam hMA) (lineEvalFam hm hm4 ty hMB)
      = (Fintype.card F : ℝ)⁻¹ * ∑ s : F, avgSubAB hm4 hm ty s (padGR hm Ψ MA MB ty) := by
  classical
  have hsum : ∑ x : Amb F m, ((rawSet hm4 ty x.2.1 x.2.2).card : ℝ)⁻¹
        * ∑ raw' ∈ rawSet hm4 ty x.2.1 x.2.2, lineTermR hm hm4 Ψ MA MB ty x.1 x.2.1 raw'
      = ∑ s : F, ∑ pt : Point F (4 * m), ∑ raw : Point F (4 * m),
          lineTermR hm hm4 Ψ MA MB ty pt s raw := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => ?_
    exact sum_rawSet_fiber hm4 ty s fun raw' => lineTermR hm hm4 Ψ MA MB ty u s raw'
  simp only [avgSubAB_padGR hm hm4 Ψ ty, agreeSum, uniform,
    sum_bornProb_ptFam_lineEvalFam hm hm4 hMA hMB Ψ ty hty]
  rw [← Finset.mul_sum, hsum, inv_card_amb_eq]
  simp only [← Finset.mul_sum]
  ring

end LinePoint

/-! ## From the padded consistency to the agreement bounds

On the padded state the Born rule sees only compressions, so the dilated point measurements of
`lem:qld-padded-lines` and `lem:qld-combined-points` can be replaced by the sandwich extended by
the identity, which is what the strategy measures. -/

section Transfer

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

/-- A dilated point measurement on Bob's side, coarse-grained, against anything on Alice's: only
its compression matters. -/
theorem bornProb_extHat_ptComb_right {x z : Point F m}
    (QB : F × F → Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ)
    (hk : ∀ r, (ancillaEmbed (dB × Anc F m) ((0 : F), (0 : F)))ᴴ
        * (QB r * ancillaEmbed (dB × Anc F m) ((0 : F), (0 : F)))
      = sand (hatMats MB .X x) (hatMats MB .Z z) r)
    (E : Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ) (a b v : F) :
    bornProb (extHat (F := F) (m := m) ψ) E (ptComb QB a b v)
      = bornProb (extHat (F := F) (m := m) ψ) E
          (aOp (ptComb (sand (hatMats MB .X x) (hatMats MB .Z z)) a b v)) := by
  rw [extHat, bornProb_extVec2, bornProb_extVec2, compress_aOp]
  congr 1
  rw [ptComb, Matrix.sum_mul, Matrix.mul_sum, ptComb]
  exact Finset.sum_congr rfl fun r _ => hk r

/-- The same on Alice's side. -/
theorem bornProb_extHat_ptComb_left {x z : Point F m}
    (QA : F × F → Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ)
    (hk : ∀ r, (ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))ᴴ
        * (QA r * ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))
      = sand (hatMats MA .X x) (hatMats MA .Z z) r)
    (G : Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ) (a b v : F) :
    bornProb (extHat (F := F) (m := m) ψ) (ptComb QA a b v) G
      = bornProb (extHat (F := F) (m := m) ψ)
          (aOp (ptComb (sand (hatMats MA .X x) (hatMats MA .Z z)) a b v)) G := by
  rw [extHat, bornProb_extVec2, bornProb_extVec2, compress_aOp]
  congr 1
  rw [ptComb, Matrix.sum_mul, Matrix.mul_sum, ptComb]
  exact Finset.sum_congr rfl fun r _ => hk r

/-- The two items of `lem:qld-expanded-lines` for the presentation of a line type. -/
theorem presOf_items (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (hd :
    1 ≤ d) (ty : CL.Ty) (W : Bas) :
    (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        xSqNorm (hatVec (F := F) (m := m) ψ) ((presOf hm ty W).lineMats d MA c f)
          ((presOf hm ty W).lineMats d MB c f) ≤ 172 * ε)
      ∧ ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
          xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
            ((presOf hm ty W).lineEvalMats d MB c a) ≤ 172 * ε := by
  cases ty
  · exact aPres_items (MB := MB) hd hψ hfail W
  · exact aPres_items (MB := MB) hd hψ hfail W
  · exact dPres_items (MB := MB) hd hψ hfail W

/-- The second item with the players exchanged: Alice's line read at the point against Bob's
point measurement. -/
theorem presOf_items_swap (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hd : 1 ≤ d) (ty : CL.Ty) (W : Bas) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) ((presOf hm ty W).lineEvalMats d MA c a)
          (hatMats MB W (c.pt W) a) ≤ 172 * ε := by
  have h := (presOf_items hm (MA := MB) (MB := MA) (ψ := swapVec ψ) (swapVec_unit hψ)
    (povmValue_swapped_le hfail) hd ty W).2
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
    congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
      (Finset.sum_congr rfl fun a _ => ?_))) h
  rw [hatVec_swapVec, xSqNorm_swapVec]

/-- The collision probability of the `X` presentation of a line type is at most `md/q + 1/q`. -/
theorem presOf_coll (ty : CL.Ty) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * collProb (presOf hm ty .X) d c
      ≤ (m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹ := by
  cases ty
  · rw [show presOf hm .point .X = aPres hm .X from rfl, sum_content_collProb_aPres]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  · rw [show presOf hm .aline .X = aPres hm .X from rfl, sum_content_collProb_aPres]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  · exact sum_content_collProb_dPres hm .X d

/-- **Alice's line against Bob's point, at a fixed seed**: `lem:qld-padded-lines` in the other
register version, with the dilated point measurement replaced by the strategy's sandwich. -/
theorem one_sub_avgSubAB_padGL_le (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA
    MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (ty : CL.Ty) (s : F) :
    1 - avgSubAB hm4 hm ty s (padGL hm (extHat (F := F) (m := m) ψ) MA MB ty)
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  obtain ⟨QB, -, hkB, hb⟩ := padded_lines_consistency_swap hm4 hψ hfail hprojA hprojB
    (presOf hm ty .X) (presOf hm ty .Z) (factorsX_presOf hm ty) (factorsZ_presOf hm ty)
    (presOf_items hm hψ hfail hd ty .X).1 (presOf_items_swap hm hψ hfail hd ty .X)
    (presOf_items_swap hm hψ hfail hd ty .Z) (presOf_coll hm ty) ty s
  refine le_trans (le_of_eq (congrArg (fun t : ℝ => 1 - t)
    (congrArg (avgSubAB hm4 hm ty s) ?_))) hb
  funext a b cX cZ
  refine Finset.sum_congr rfl fun v _ => ?_
  exact (bornProb_extHat_ptComb_right (QB (cX, cZ)) (hkB (cX, cZ)) _ a b v).symm

/-- **Alice's point against Bob's line, at a fixed seed.** -/
theorem one_sub_avgSubAB_padGR_le (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA
    MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (ty : CL.Ty) (s : F) :
    1 - avgSubAB hm4 hm ty s (padGR hm (extHat (F := F) (m := m) ψ) MA MB ty)
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  obtain ⟨QA, -, hkA, hb⟩ := padded_lines_consistency hm4 hψ hfail hprojA hprojB
    (presOf hm ty .X) (presOf hm ty .Z) (factorsX_presOf hm ty) (factorsZ_presOf hm ty)
    (presOf_items hm hψ hfail hd ty .X).1 (presOf_items hm hψ hfail hd ty .X).2
    (presOf_items hm hψ hfail hd ty .Z).2 (presOf_coll hm ty) ty s
  refine le_trans (le_of_eq (congrArg (fun t : ℝ => 1 - t)
    (congrArg (avgSubAB hm4 hm ty s) ?_))) hb
  funext a b cX cZ
  refine Finset.sum_congr rfl fun v _ => ?_
  exact (bornProb_extHat_ptComb_left (QA (cX, cZ)) (hkA (cX, cZ)) _ a b v).symm

omit [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- Averaging a family of bounds over the seed. -/
theorem one_sub_inv_card_mul_sum_le {A : F → ℝ} {B : ℝ} (h : ∀ s, 1 - A s ≤ B) :
    1 - (Fintype.card F : ℝ)⁻¹ * ∑ s, A s ≤ B := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h1 : (Fintype.card F : ℝ)⁻¹ * ∑ s : F, (1 - A s) ≤ (Fintype.card F : ℝ)⁻¹ * ∑ _s : F, B :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => h s) (inv_nonneg.mpr (Nat.cast_nonneg
    _))
  have h2 : (Fintype.card F : ℝ)⁻¹ * ∑ s : F, (1 - A s) = 1 - (Fintype.card F : ℝ)⁻¹ * ∑ s, A s :=
      by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_sub,
      inv_mul_cancel₀ hq]
  have h3 : (Fintype.card F : ℝ)⁻¹ * ∑ _s : F, B = B := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  rw [h2, h3] at h1
  exact h1

/-- **The line-point subtests, Alice's line**: the agreement of Alice's line measurement read at
the sample's point with Bob's padded point measurement, averaged over the ambient sample. -/
theorem one_sub_agreeSum_lineEval_pt_le (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm)
    ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (ty : CL.Ty)
    (hty : ty ≠ .point) :
    1 - agreeSum (uniform (Amb F m)) (extHat (F := F) (m := m) ψ) (lineEvalFam hm hm4 ty hprojA)
        (ptFam hprojB)
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  rw [agreeSum_lineEvalFam_ptFam hm hm4 hprojA hprojB _ ty hty]
  exact one_sub_inv_card_mul_sum_le fun s =>
    one_sub_avgSubAB_padGL_le hm hm4 hψ hfail hprojA hprojB hd ty s

/-- **The line-point subtests, Bob's line.** -/
theorem one_sub_agreeSum_pt_lineEval_le (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm)
    ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (ty : CL.Ty)
    (hty : ty ≠ .point) :
    1 - agreeSum (uniform (Amb F m)) (extHat (F := F) (m := m) ψ) (ptFam hprojA)
        (lineEvalFam hm hm4 ty hprojB)
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  rw [agreeSum_ptFam_lineEvalFam hm hm4 hprojA hprojB _ ty hty]
  exact one_sub_inv_card_mul_sum_le fun s =>
    one_sub_avgSubAB_padGR_le hm hm4 hψ hfail hprojA hprojB hd ty s

/-! ### The identical-point subtest -/

omit [Algebra (ZMod 2) F] in
/-- A function of the two blocks of the sample's point, averaged over the ambient sample, is its
average over the pair of blocks. -/
theorem avg_amb_blocks (g : Point F m → Point F m → ℝ) :
    ∑ x : Amb F m, (Fintype.card (Amb F m) : ℝ)⁻¹ * g (xBlk x.1) (zBlk x.1)
      = ∑ y : Point F m × Point F m, (Fintype.card (Point F m × Point F m) : ℝ)⁻¹ * g y.1 y.2 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← Finset.mul_sum, ← Finset.mul_sum, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_point_pad g, nsmul_eq_mul]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
  field_simp
  ring

/-- **The identical-point subtest**: the two padded point measurements agree up to `δ_Q`, by the
self-consistency item of `lem:qld-combined-points` read through the compressions. -/
theorem one_sub_agreeSum_pt_pt_le (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA
    MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) :
    1 - agreeSum (uniform (Amb F m)) (extHat (F := F) (m := m) ψ) (ptFam hprojA) (ptFam hprojB)
      ≤ deltaQ ε := by
  classical
  obtain ⟨QA, QB, hPA, hPB, hkA, hkB, h1, -, -⟩ :=
    @combined_points_pts F _ _ _ m _ _ hm d dA dB _ _ _ _ ψ MA MB ε hψ hfail hprojA hprojB
  have hΨ : ‖evec (extHat (F := F) (m := m) ψ)‖ = 1 :=
    norm_evec_eq_one_of_unit (extVec2_unit (hatVec_unit hψ) _ _)
  have hu : ∀ u : Point F (4 * m),
      1 - ∑ a, bornProb (extHat (F := F) (m := m) ψ) (((padPt hprojA u).mats a).val)
          (((padPt hprojB u).mats a).val)
        ≤ (∑ p : F × F, xSqNorm (extHat (F := F) (m := m) ψ) (QA (xBlk u, zBlk u) p)
            (QB (xBlk u, zBlk u) p)) / 2 := by
    intro u
    have heq : ∀ a, bornProb (extHat (F := F) (m := m) ψ) (((padPt hprojA u).mats a).val)
        (((padPt hprojB u).mats a).val)
        = bornProb (extHat (F := F) (m := m) ψ) (ptComb (QA (xBlk u, zBlk u)) (alph u) (bet u) a)
            (ptComb (QB (xBlk u, zBlk u)) (alph u) (bet u) a) := by
      intro a
      rw [padPt_mats, padPt_mats, bornProb_extHat_ptComb_left (QA _) (hkA _),
        bornProb_extHat_ptComb_right (QB _) (hkB _)]
    simp only [heq]
    have hA : IsPVM (ptComb (QA (xBlk u, zBlk u)) (alph u) (bet u)) :=
      (hPA _).coarse fun r : F × F => alph u * r.1 + bet u * r.2
    have hB : IsPVM (ptComb (QB (xBlk u, zBlk u)) (alph u) (bet u)) :=
      (hPB _).coarse fun r : F × F => alph u * r.1 + bet u * r.2
    rw [one_sub_sum_bornProb_eq hΨ hA hB]
    exact div_le_div_of_nonneg_right
      (sum_xSqNorm_fibSum_le hΨ (hPA _) (hPB _) fun r : F × F => alph u * r.1 + bet u * r.2)
      zero_le_two
  have hμ : ∑ x : Amb F m, uniform (Amb F m) x = 1 := by
    simp only [uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hexp : 1 - agreeSum (uniform (Amb F m)) (extHat (F := F) (m := m) ψ) (ptFam hprojA) (ptFam
      hprojB)
      = ∑ x : Amb F m, uniform (Amb F m) x * (1 - ∑ a, bornProb (extHat (F := F) (m := m) ψ)
          (((padPt hprojA x.1).mats a).val) (((padPt hprojB x.1).mats a).val)) := by
    rw [agreeSum]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hμ]
    rfl
  rw [hexp]
  calc ∑ x : Amb F m, uniform (Amb F m) x * (1 - ∑ a, bornProb (extHat (F := F) (m := m) ψ)
          (((padPt hprojA x.1).mats a).val) (((padPt hprojB x.1).mats a).val))
      ≤ ∑ x : Amb F m, (Fintype.card (Amb F m) : ℝ)⁻¹
          * ((∑ p : F × F, xSqNorm (extHat (F := F) (m := m) ψ) (QA (xBlk x.1, zBlk x.1) p)
              (QB (xBlk x.1, zBlk x.1) p)) / 2) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hu x.1)
          (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (∑ y : Point F m × Point F m, (Fintype.card (Point F m × Point F m) : ℝ)⁻¹
          * ∑ p : F × F, xSqNorm (extHat (F := F) (m := m) ψ) (QA y p) (QB y p)) / 2 := by
        rw [avg_amb_blocks fun x z => (∑ p : F × F,
          xSqNorm (extHat (F := F) (m := m) ψ) (QA (x, z) p) (QB (x, z) p)) / 2, Finset.sum_div]
        exact Finset.sum_congr rfl fun y _ => by rw [mul_div_assoc]
    _ ≤ 2 * deltaQ ε / 2 := div_le_div_of_nonneg_right h1 zero_le_two
    _ = deltaQ ε := by ring

end Transfer

/-! ## The identical-line subtest

Two distinct polynomial outcomes are told apart by reading both at a uniformly random parameter of
the line, up to `(md + 1)/q`; the parameter of the sample's point is uniform on the line once the
raw direction is fixed and the line is not degenerate, because translating the point along the
line is a bijection of the sample space that fixes the line and shifts the parameter. -/

section Lines

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  (hMA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hMB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
  (Ψ : ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ)

omit [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **The parameter is uniform on the line.** For a quantity that depends on the sample's point
only through the line it generates and the parameter of the point on it, averaging over a uniform
parameter is averaging over the point, when moving the point along the line shifts its parameter
by the same amount. -/
theorem sum_shift_param {n : ℕ} {α β : Type*} (w : Point F n) (LA : Point F n → α)
    (LB : Point F n → β) (τ : Point F n → F) (hLA : ∀ (u : Point F n) (t : F), LA (u + t • w) = LA
        u)
    (hLB : ∀ (u : Point F n) (t : F), LB (u + t • w) = LB u)
    (hτ : ∀ (u : Point F n) (t : F), τ (u + t • w) = τ u + t)
    (Φ : α → β → F → ℝ) :
    ∑ u : Point F n, ∑ t : F, Φ (LA u) (LB u) t
      = (Fintype.card F : ℝ) * ∑ u : Point F n, Φ (LA u) (LB u) (τ u) := by
  calc ∑ u : Point F n, ∑ t : F, Φ (LA u) (LB u) t
      = ∑ u : Point F n, ∑ t : F, Φ (LA u) (LB u) (τ u + t) :=
        Finset.sum_congr rfl fun u _ =>
          (Equiv.sum_comp (Equiv.addLeft (τ u)) fun t => Φ (LA u) (LB u) t).symm
    _ = ∑ t : F, ∑ u : Point F n, Φ (LA u) (LB u) (τ u + t) := Finset.sum_comm
    _ = ∑ t : F, ∑ u : Point F n, Φ (LA (u + t • w)) (LB (u + t • w)) (τ (u + t • w)) := by
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
        rw [hLA, hLB, hτ]
    _ = ∑ t : F, ∑ u : Point F n, Φ (LA u) (LB u) (τ u) :=
        Finset.sum_congr rfl fun t _ =>
          Equiv.sum_comp (Equiv.addRight (t • w)) fun u => Φ (LA u) (LB u) (τ u)
    _ = (Fintype.card F : ℝ) * ∑ u : Point F n, Φ (LA u) (LB u) (τ u) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The disagreement of two polynomial measurements read at the parameter `t`. -/
def evDef (LA : POVM (LinePoly F (m * d + 1)) ((dA × Anc F m) × (F × F)))
    (LB : POVM (LinePoly F (m * d + 1)) ((dB × Anc F m) × (F × F))) (t : F) : ℝ :=
  1 - ∑ a : F, bornProb Ψ (((LA.map fun f => LinePoly.eval f t).mats a).val)
    (((LB.map fun f => LinePoly.eval f t).mats a).val)

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem evDef_nonneg (hΨ : star Ψ ⬝ᵥ Ψ = 1) (LA : POVM (LinePoly F (m * d + 1)) ((dA × Anc F m) ×
    (F × F)))
    (LB : POVM (LinePoly F (m * d + 1)) ((dB × Anc F m) × (F × F))) (t : F) :
    0 ≤ evDef Ψ LA LB t :=
  sub_nonneg.mpr (sum_bornProb_diag_le_one hΨ _ _ (fun a => POVM.posSemidef _ a)
    (fun a => POVM.posSemidef _ a) (POVM.sum_val _) (POVM.sum_val _))

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem evDef_le_one (LA : POVM (LinePoly F (m * d + 1)) ((dA × Anc F m) × (F × F)))
    (LB : POVM (LinePoly F (m * d + 1)) ((dB × Anc F m) × (F × F))) (t : F) :
    evDef Ψ LA LB t ≤ 1 := by
  have : 0 ≤ ∑ a : F, bornProb Ψ (((LA.map fun f => LinePoly.eval f t).mats a).val)
      (((LB.map fun f => LinePoly.eval f t).mats a).val) :=
    Finset.sum_nonneg fun a _ => bornProb_nonneg Ψ (POVM.posSemidef _ a) (POVM.posSemidef _ a)
  unfold evDef
  linarith

/-- The disagreement of the two line measurements read at the sample's point is the disagreement of
the evaluated families. -/
theorem evDef_lineTau (ty : CL.Ty) (x : Amb F m) :
    evDef Ψ (lineFam hm hm4 ty hMA x) (lineFam hm hm4 ty hMB x) (lineTau hm4 ty x.1 x.2.1 x.2.2)
      = 1 - ∑ a : F, bornProb Ψ (((lineEvalFam hm hm4 ty hMA x).mats a).val)
          (((lineEvalFam hm hm4 ty hMB x).mats a).val) := rfl

/-- **At a fixed seed and raw direction, averaging the evaluated disagreement over the parameter
is averaging it over the point**, unless the direction is degenerate, in which case the average is
at most one. -/
theorem sum_avg_evDef_le (hΨ : star Ψ ⬝ᵥ Ψ = 1) (ty : CL.Ty) (s : F) (raw : Point F (4 * m)) :
    ∑ u : Point F (4 * m), (Fintype.card F : ℝ)⁻¹ * ∑ t : F,
        evDef Ψ (lineFam hm hm4 ty hMA (u, s, raw)) (lineFam hm hm4 ty hMB (u, s, raw)) t
      ≤ ∑ u : Point F (4 * m), evDef Ψ (lineFam hm hm4 ty hMA (u, s, raw))
          (lineFam hm hm4 ty hMB (u, s, raw)) (lineTau hm4 ty u s raw)
        + (if lineDir hm4 ty s raw = 0 then (Fintype.card (Point F (4 * m)) : ℝ) else 0) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases hdir : lineDir hm4 ty s raw = 0
  · rw [if_pos hdir]
    have h1 : ∑ u : Point F (4 * m), (Fintype.card F : ℝ)⁻¹ * ∑ t : F,
        evDef Ψ (lineFam hm hm4 ty hMA (u, s, raw)) (lineFam hm hm4 ty hMB (u, s, raw)) t
        ≤ ∑ _u : Point F (4 * m), (1 : ℝ) := by
      refine Finset.sum_le_sum fun u _ => ?_
      calc (Fintype.card F : ℝ)⁻¹ * ∑ t : F,
            evDef Ψ (lineFam hm hm4 ty hMA (u, s, raw)) (lineFam hm hm4 ty hMB (u, s, raw)) t
          ≤ (Fintype.card F : ℝ)⁻¹ * ∑ _t : F, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => evDef_le_one Ψ _ _ t)
              (inv_nonneg.mpr (Nat.cast_nonneg _))
        _ = 1 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hq]
    have h2 : 0 ≤ ∑ u : Point F (4 * m), evDef Ψ (lineFam hm hm4 ty hMA (u, s, raw))
        (lineFam hm hm4 ty hMB (u, s, raw)) (lineTau hm4 ty u s raw) :=
      Finset.sum_nonneg fun u _ => evDef_nonneg Ψ hΨ _ _ _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h1
    linarith
  · rw [if_neg hdir, add_zero, ← Finset.mul_sum]
    have hw : ∃ j, lineDir hm4 ty s raw j ≠ 0 := by
      by_contra h
      exact hdir (funext fun j => not_not.mp fun hj => h ⟨j, hj⟩)
    have hLA : ∀ (u : Point F (4 * m)) (t : F),
        lineFam hm hm4 ty hMA (u + t • lineDir hm4 ty s raw, s, raw)
          = lineFam hm hm4 ty hMA (u, s, raw) := by
      intro u t
      simp only [lineFam, rep_add_smul]
    have hLB : ∀ (u : Point F (4 * m)) (t : F),
        lineFam hm hm4 ty hMB (u + t • lineDir hm4 ty s raw, s, raw)
          = lineFam hm hm4 ty hMB (u, s, raw) := by
      intro u t
      simp only [lineFam, rep_add_smul]
    have hτ : ∀ (u : Point F (4 * m)) (t : F),
        lineTau hm4 ty (u + t • lineDir hm4 ty s raw) s raw = lineTau hm4 ty u s raw + t :=
      fun u t => lineParam_rep_add_smul hw u t
    rw [sum_shift_param (lineDir hm4 ty s raw) (fun u => lineFam hm hm4 ty hMA (u, s, raw))
      (fun u => lineFam hm hm4 ty hMB (u, s, raw)) (fun u => lineTau hm4 ty u s raw) hLA hLB hτ
      (fun LA LB t => evDef Ψ LA LB t), ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

omit [Algebra (ZMod 2) F] in
/-- **Degenerate lines are rare**: over the seed and the raw direction, a line type other than
`point` describes the zero direction on at most a `1/q` fraction of the samples. -/
theorem sum_deg_le (ty : CL.Ty) (hty : ty ≠ .point) :
    ∑ s : F, ∑ raw : Point F (4 * m), (if lineDir hm4 ty s raw = 0 then (1 : ℝ) else 0)
      ≤ (Fintype.card (Point F (4 * m)) : ℝ) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  cases ty
  · exact absurd rfl hty
  · have h0 : ∀ (s : F) (raw : Point F (4 * m)), lineDir hm4 .aline s raw ≠ 0 := by
      intro s raw h
      have := congrFun h (chi hm4 s)
      simp [lineDir] at this
    simp only [h0, if_false, Finset.sum_const_zero]
    exact Nat.cast_nonneg _
  · calc ∑ s : F, ∑ raw : Point F (4 * m), (if lineDir hm4 .dline s raw = 0 then (1 : ℝ) else 0)
        ≤ ∑ _s : F, (Fintype.card (Point F (4 * m)) : ℝ) / Fintype.card F :=
          Finset.sum_le_sum fun s _ => sum_indicator_zeroBelow_eq_zero_le (chi hm4 s)
      _ = (Fintype.card (Point F (4 * m)) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hq]

omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- A sum over the ambient sample, as a sum over the seed, the raw direction and the point. -/
theorem sum_amb_eq (g : Amb F m → ℝ) :
    ∑ x : Amb F m, g x = ∑ s : F, ∑ raw : Point F (4 * m), ∑ u : Point F (4 * m), g (u, s, raw) :=
        by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_comm

omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem uniform_amb_nonneg (x : Amb F m) : 0 ≤ uniform (Amb F m) x :=
  inv_nonneg.mpr (Nat.cast_nonneg _)

omit [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem sum_uniform_amb : ∑ x : Amb F m, uniform (Amb F m) x = 1 := by
  simp only [uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- The disagreement of two families, as the uniform average of the per-sample disagreements. -/
theorem one_sub_agreeSum_uniform_eq (M : Amb F m → POVM F ((dA × Anc F m) × (F × F)))
    (N : Amb F m → POVM F ((dB × Anc F m) × (F × F))) :
    1 - agreeSum (uniform (Amb F m)) Ψ M N
      = ∑ x : Amb F m, uniform (Amb F m) x
          * (1 - ∑ a : F, bornProb Ψ (((M x).mats a).val) (((N x).mats a).val)) := by
  rw [agreeSum]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sum_uniform_amb]

/-- **The identical-line agreement, through the triangle**: Alice's line read at the sample's point
agrees with Bob's, because each agrees with the padded point measurements there. -/
theorem one_sub_agreeSum_lineEval_lineEval_le {ψ : dA × dB → ℂ} {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (hε : 0 ≤ ε) (hd : 1 ≤ d) (ty : CL.Ty)
    (hty : ty ≠ .point) :
    1 - agreeSum (uniform (Amb F m)) (extHat (F := F) (m := m) ψ) (lineEvalFam hm hm4 ty hMA)
        (lineEvalFam hm hm4 ty hMB)
      ≤ 11 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹)
          + deltaQ ε) := by
  have hΨ : star (extHat (F := F) (m := m) ψ) ⬝ᵥ extHat (F := F) (m := m) ψ = 1 :=
    extVec2_unit (hatVec_unit hψ) _ _
  have hQ0 : 0 ≤ deltaQ ε := by
    unfold deltaQ
    positivity
  have hP0 : 0 ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹)
      := by
    unfold deltaPairs deltaPairsD kappaPairs deltaQ
    positivity
  refine agreeSum_triangle uniform_amb_nonneg sum_uniform_amb hΨ (lineEvalFam hm hm4 ty hMA)
    (ptFam hMA) (ptFam hMB) (lineEvalFam hm hm4 ty hMB) ?_ ?_ ?_
  · exact le_trans (one_sub_agreeSum_lineEval_pt_le hm hm4 hψ hfail hMA hMB hd ty hty)
      (le_add_of_nonneg_right hQ0)
  · exact le_trans (one_sub_agreeSum_pt_pt_le hm hψ hfail hMA hMB) (le_add_of_nonneg_left hP0)
  · exact le_trans (one_sub_agreeSum_pt_lineEval_le hm hm4 hψ hfail hMA hMB hd ty hty)
      (le_add_of_nonneg_right hQ0)

end Lines

/-! ## The nine subtests, and the value -/

section Assembly

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

/-- The failure weight of one ordered pair of types: the conditional failure of the padded strategy
at the questions of the two types, averaged over the ambient sample. -/
def padW (ψ : dA × dB → ℂ) (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (tA tB : CL.Ty) : ℝ :=
  ∑ x : Amb F m, uniform (Amb F m) x
    * condFail (clGame (d := d) (ldc := 1) hm4) (extHat (F := F) (m := m) ψ)
        (padStrat hm hm4 hprojA) (padStrat hm hm4 hprojB)
        (lineQ hm4 tA x.1 x.2.1 x.2.2) (lineQ hm4 tB x.1 x.2.1 x.2.2)

variable {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
  (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
  (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))

include hψ hfail in
theorem padW_point_point_le : padW hm hm4 ψ hprojA hprojB .point .point ≤ deltaQ ε := by
  have h := one_sub_agreeSum_pt_pt_le hm hψ hfail hprojA hprojB
  rw [one_sub_agreeSum_uniform_eq] at h
  refine le_trans (Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left ?_ (uniform_amb_nonneg x)) h
  exact condFail_point_point_le hm hm4 hprojA hprojB _ x.1

include hψ hfail in
theorem padW_line_point_le (hd : 1 ≤ d) (hlegA : LegalSupport MA) (ty : CL.Ty) (hty : ty ≠ .point) :
    padW hm hm4 ψ hprojA hprojB ty .point
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  have h := one_sub_agreeSum_lineEval_pt_le hm hm4 hψ hfail hprojA hprojB hd ty hty
  rw [one_sub_agreeSum_uniform_eq] at h
  refine le_trans (Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left ?_ (uniform_amb_nonneg x)) h
  exact condFail_lineQ_point_le hm hm4 hprojA hprojB _ ty hty hd hlegA x.1 x.2.1 x.2.2

include hψ hfail in
theorem padW_point_line_le (hd : 1 ≤ d) (hlegB : LegalSupport MB) (ty : CL.Ty) (hty : ty ≠ .point) :
    padW hm hm4 ψ hprojA hprojB .point ty
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  have h := one_sub_agreeSum_pt_lineEval_le hm hm4 hψ hfail hprojA hprojB hd ty hty
  rw [one_sub_agreeSum_uniform_eq] at h
  refine le_trans (Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left ?_ (uniform_amb_nonneg x)) h
  exact condFail_point_lineQ_le hm hm4 hprojA hprojB _ ty hty hd hlegB x.1 x.2.1 x.2.2

include hψ in
theorem padW_aline_dline_le : padW hm hm4 ψ hprojA hprojB .aline .dline ≤ 0 := by
  have hΨ : star (extHat (F := F) (m := m) ψ) ⬝ᵥ extHat (F := F) (m := m) ψ = 1 :=
    extVec2_unit (hatVec_unit hψ) _ _
  refine le_trans (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (condFail_aline_dline_le hm hm4 hprojA hprojB _ hΨ x.1 x.2.1 x.2.2 x.1 x.2.1 x.2.2)
    (uniform_amb_nonneg x)) ?_
  simp

include hψ in
theorem padW_dline_aline_le : padW hm hm4 ψ hprojA hprojB .dline .aline ≤ 0 := by
  have hΨ : star (extHat (F := F) (m := m) ψ) ⬝ᵥ extHat (F := F) (m := m) ψ = 1 :=
    extVec2_unit (hatVec_unit hψ) _ _
  refine le_trans (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (condFail_dline_aline_le hm hm4 hprojA hprojB _ hΨ x.1 x.2.1 x.2.2 x.1 x.2.1 x.2.2)
    (uniform_amb_nonneg x)) ?_
  simp

include hψ hfail in
/-- **The identical-line subtests.** -/
theorem padW_line_line_le (hε : 0 ≤ ε) (hd : 1 ≤ d) (ty : CL.Ty) (hty : ty ≠ .point) :
    padW hm hm4 ψ hprojA hprojB ty ty
      ≤ 11 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹)
            + deltaQ ε)
        + ((m : ℝ) * d + 1) / Fintype.card F + (Fintype.card F : ℝ)⁻¹ := by
  set Ψ := extHat (F := F) (m := m) ψ with hΨdef
  have hΨ : star Ψ ⬝ᵥ Ψ = 1 := extVec2_unit (hatVec_unit hψ) _ _
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcA : (Fintype.card (Amb F m) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hP0 : (0 : ℝ) ≤ Fintype.card (Point F (4 * m)) := Nat.cast_nonneg _
  have hcAinv : (0 : ℝ) ≤ (Fintype.card (Amb F m) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  -- the per-sample bound, by polynomial separation
  have h1 : ∀ x : Amb F m,
      condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hprojA) (padStrat hm hm4 hprojB)
          (lineQ hm4 ty x.1 x.2.1 x.2.2) (lineQ hm4 ty x.1 x.2.1 x.2.2)
        ≤ (Fintype.card F : ℝ)⁻¹ * ∑ t : F,
            evDef Ψ (lineFam hm hm4 ty hprojA x) (lineFam hm hm4 ty hprojB x) t
          + ((m : ℝ) * d + 1) / Fintype.card F := by
    intro x
    refine le_trans (condFail_lineQ_lineQ_le hm hm4 hprojA hprojB Ψ ty hty x.1 x.2.1 x.2.2) ?_
    have h := one_sub_sum_bornProb_le_avg_eval hΨ (lineFam hm hm4 ty hprojA x)
      (lineFam hm hm4 ty hprojB x)
    push_cast at h
    exact h
  -- the degenerate lines
  have hdeg : (Fintype.card (Amb F m) : ℝ)⁻¹ * ((Fintype.card (Point F (4 * m)) : ℝ)
      * ∑ s : F, ∑ raw : Point F (4 * m), (if lineDir hm4 ty s raw = 0 then (1 : ℝ) else 0))
      ≤ (Fintype.card F : ℝ)⁻¹ := by
    have hc : (Fintype.card (Amb F m) : ℝ)⁻¹
        * ((Fintype.card (Point F (4 * m)) : ℝ) * (Fintype.card (Point F (4 * m)) : ℝ))
        = (Fintype.card F : ℝ)⁻¹ := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
      field_simp
    rw [← hc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sum_deg_le hm4 ty hty) hP0)
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc padW hm hm4 ψ hprojA hprojB ty ty
      ≤ ∑ x : Amb F m, uniform (Amb F m) x * ((Fintype.card F : ℝ)⁻¹ * ∑ t : F,
            evDef Ψ (lineFam hm hm4 ty hprojA x) (lineFam hm hm4 ty hprojB x) t
          + ((m : ℝ) * d + 1) / Fintype.card F) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h1 x) (uniform_amb_nonneg x)
    _ = (Fintype.card (Amb F m) : ℝ)⁻¹ * ∑ x : Amb F m, ((Fintype.card F : ℝ)⁻¹ * ∑ t : F,
            evDef Ψ (lineFam hm hm4 ty hprojA x) (lineFam hm hm4 ty hprojB x) t)
          + ((m : ℝ) * d + 1) / Fintype.card F := by
        simp only [uniform, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcA, one_mul]
    _ ≤ (Fintype.card (Amb F m) : ℝ)⁻¹ * (∑ x : Amb F m,
            evDef Ψ (lineFam hm hm4 ty hprojA x) (lineFam hm hm4 ty hprojB x)
              (lineTau hm4 ty x.1 x.2.1 x.2.2)
          + (Fintype.card (Point F (4 * m)) : ℝ)
            * ∑ s : F, ∑ raw : Point F (4 * m), (if lineDir hm4 ty s raw = 0 then (1 : ℝ) else 0))
          + ((m : ℝ) * d + 1) / Fintype.card F := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ hcAinv) le_rfl
        rw [sum_amb_eq, sum_amb_eq]
        conv_rhs => simp only [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun s _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun raw _ => ?_
        rw [mul_ite, mul_one, mul_zero]
        exact sum_avg_evDef_le hm hm4 hprojA hprojB Ψ hΨ ty s raw
    _ ≤ (Fintype.card (Amb F m) : ℝ)⁻¹ * ∑ x : Amb F m,
            evDef Ψ (lineFam hm hm4 ty hprojA x) (lineFam hm hm4 ty hprojB x)
              (lineTau hm4 ty x.1 x.2.1 x.2.2)
          + (Fintype.card F : ℝ)⁻¹ + ((m : ℝ) * d + 1) / Fintype.card F := by
        rw [mul_add]
        linarith
    _ = (1 - agreeSum (uniform (Amb F m)) Ψ (lineEvalFam hm hm4 ty hprojA)
          (lineEvalFam hm hm4 ty hprojB))
          + (Fintype.card F : ℝ)⁻¹ + ((m : ℝ) * d + 1) / Fintype.card F := by
        rw [one_sub_agreeSum_uniform_eq]
        simp only [uniform, ← Finset.mul_sum, evDef_lineTau]
    _ ≤ 11 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹)
            + deltaQ ε)
        + ((m : ℝ) * d + 1) / Fintype.card F + (Fintype.card F : ℝ)⁻¹ := by
        have := one_sub_agreeSum_lineEval_lineEval_le hm hm4 hprojA hprojB hψ hfail hε hd ty hty
        linarith

omit [DecidableEq F] [Algebra (ZMod 2) F] in
theorem Sample.question_fst_eq_lineQ (tA tB : CL.Ty) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) :
    (⟨tA, tB, u, s, raw⟩ : CL.Sample F (4 * m)).question hm4 tA = lineQ hm4 tA u s raw := by
  cases tA <;> rfl

omit [DecidableEq F] [Algebra (ZMod 2) F] in
theorem Sample.question_snd_eq_lineQ (tA tB : CL.Ty) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) :
    (⟨tA, tB, u, s, raw⟩ : CL.Sample F (4 * m)).question hm4 tB = lineQ hm4 tB u s raw := by
  cases tB <;> rfl

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- A sum over the three question types. -/
theorem sum_ty (f : CL.Ty → ℝ) : ∑ t, f t = f .point + f .aline + f .dline := by
  show ∑ t ∈ ({CL.Ty.point, CL.Ty.aline, CL.Ty.dline} : Finset CL.Ty), f t = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- **The failure probability of the padded strategy is the average over the nine ordered type
pairs of their failure weights.** -/
theorem one_sub_povmValue_padStrat_eq :
    1 - povmValue (clGame (d := d) (ldc := 1) hm4) (extHat (F := F) (m := m) ψ)
        (padStrat hm hm4 hprojA) (padStrat hm hm4 hprojB)
      = (9 : ℝ)⁻¹ * ∑ tA : CL.Ty, ∑ tB : CL.Ty, padW hm hm4 ψ hprojA hprojB tA tB := by
  rw [one_sub_povmValue_clGame hm4, sum_sample_eq, card_sample]
  simp only [Sample.question_fst_eq_lineQ, Sample.question_snd_eq_lineQ, padW, uniform,
    Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun tA _ => Finset.sum_congr rfl fun tB _ =>
    Finset.sum_congr rfl fun x _ => ?_
  rw [mul_inv, mul_assoc]

include hψ hfail in
/-- **`lem:qld-global-success`: the padded strategy wins the seeded low individual degree test at
`(q, 4m, d, 1)` with probability `1 - O(δ_combine + δ_Q + md/q)`**, with
`δ_combine = m² δ_P(ε, md/q + 1/q)`. -/
theorem padStrat_value (hε : 0 ≤ ε) (hlegA : LegalSupport MA) (hlegB : LegalSupport MB)
    (hd : 1 ≤ d) :
    1 - povmValue (clGame (d := d) (ldc := 1) hm4) (extHat (F := F) (m := m) ψ)
        (padStrat hm hm4 hprojA) (padStrat hm hm4 hprojB)
      ≤ 5 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹))
        + 4 * deltaQ ε + ((m : ℝ) * d + 1) / Fintype.card F := by
  rw [one_sub_povmValue_padStrat_eq hm hm4 hprojA hprojB, sum_ty, sum_ty, sum_ty, sum_ty]
  have hpp := padW_point_point_le hm hm4 hψ hfail hprojA hprojB
  have hap := padW_line_point_le hm hm4 hψ hfail hprojA hprojB hd hlegA .aline (by decide)
  have hdp := padW_line_point_le hm hm4 hψ hfail hprojA hprojB hd hlegA .dline (by decide)
  have hpa := padW_point_line_le hm hm4 hψ hfail hprojA hprojB hd hlegB .aline (by decide)
  have hpd := padW_point_line_le hm hm4 hψ hfail hprojA hprojB hd hlegB .dline (by decide)
  have haa := padW_line_line_le hm hm4 hψ hfail hprojA hprojB hε hd .aline (by decide)
  have hdd := padW_line_line_le hm hm4 hψ hfail hprojA hprojB hε hd .dline (by decide)
  have had := padW_aline_dline_le hm hm4 hψ hprojA hprojB
  have hda := padW_dline_aline_le hm hm4 hψ hprojA hprojB
  have hQ0 : 0 ≤ deltaQ ε := by
    unfold deltaQ
    positivity
  have hP0 : 0 ≤ (m : ℝ) * m
      * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
    unfold deltaPairs deltaPairsD kappaPairs deltaQ
    positivity
  have hR0 : 0 ≤ ((m : ℝ) * d + 1) / Fintype.card F := by positivity
  have hq1 : (Fintype.card F : ℝ)⁻¹ ≤ ((m : ℝ) * d + 1) / Fintype.card F := by
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_left (inv_nonneg.mpr (Nat.cast_nonneg _))
      (le_add_of_nonneg_left (by positivity))
  linarith

end Assembly

end MIPRE.QLD

end
