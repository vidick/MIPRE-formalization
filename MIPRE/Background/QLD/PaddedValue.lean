/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.PaddedStrategy

@[expose] public section

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

## In a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The padded strategy is a pair of
families of POVMs in the expanded model `N₀ = M.reg (Anc F m)` (`padStrat`, in the players'
`Matrix (Anc F m) (Anc F m) _`), and the stage-4a interface is `padStrat_value`:
`1 - δ_GS ≤ N₀.povmValue (clGame hm4) (padStrat hm hm4 hPA) (padStrat hm hm4 hPB)` for a legally
supported projective strategy of value `1 - ε`. The point measurement *is* the sandwich, read along
`(alpha, beta)`, so the identical-point subtest is the first agreement bound of
`combined_points_pts` coarse-grained (`sum_bornProb_le_fibre`) and the line-point subtests are
`padded_lines_consistency` verbatim: no compression is needed, and the matrix route's
`bornProb_extHat_ptComb_left`/`_right` are gone. The decomposition of the failure probability into
the nine type pairs is the model form of `one_sub_povmValue_clGame`
(`BipartiteModel.one_sub_povmValue_clGame`, below); the per-sample families and the polynomial
separation are stated in any bipartite model with the players' algebras of `N₀`. `deltaGS`, the error
of `lem:qld-global-success`, is defined here (moved from `PaddedLIDT.lean`) so that the interface
can be stated with it.
-/

noncomputable section

namespace MIPRE.BipartiteModel

open Finset MIPRE.LIDT

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [PartialOrder ℬ]

/-- **The failure probability of a POVM strategy in the seeded test is the average over the
verifier's samples of the conditional failure at the two questions the sample generates**, in a
bipartite model: the model form of `MIPRE.LIDT.CL.one_sub_povmValue_clGame`. -/
theorem one_sub_povmValue_clGame (N : BipartiteModel 𝒞 𝒜 ℬ) {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {m d ldc : ℕ} [NeZero m] (hm : m ∣ Fintype.card F)
    (PA : CL.Question F m → POVMIn (CL.Answer F m d ldc) 𝒜)
    (PB : CL.Question F m → POVMIn (CL.Answer F m d ldc) ℬ) :
    1 - N.povmValue (CL.clGame (d := d) (ldc := ldc) hm) PA PB
      = (Fintype.card (CL.Sample F m) : ℝ)⁻¹ * ∑ sm : CL.Sample F m,
          N.condFail (CL.clGame hm) PA PB (sm.question hm sm.tyA) (sm.question hm sm.tyB) := by
  classical
  rw [N.one_sub_povmValue_eq, Finset.mul_sum]
  set c : ℝ := (Fintype.card (CL.Sample F m) : ℝ)⁻¹ with hc
  set T : CL.Question F m → CL.Question F m → CL.Sample F m → ℝ := fun x y sm =>
    (c * if (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y) then 1 else 0)
      * N.condFail (CL.clGame hm) PA PB x y with hT
  have hμ : ∀ x y, (CL.clGame (d := d) (ldc := ldc) hm).μ x y
      * N.condFail (CL.clGame hm) PA PB x y = ∑ sm : CL.Sample F m, T x y sm := fun x y => by
    rw [hT]
    show (∑ sm : CL.Sample F m, c * if (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y)
      then (1 : ℝ) else 0) * N.condFail (CL.clGame hm) PA PB x y = _
    rw [Finset.sum_mul]
  simp only [hμ]
  calc ∑ x, ∑ y, ∑ sm, T x y sm
      = ∑ x, ∑ sm, ∑ y, T x y sm := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ sm, ∑ x, ∑ y, T x y sm := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun sm _ => ?_
  rw [← Fintype.sum_prod_type' fun x y => T x y sm]
  simp only [hT, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Prod.mk.eta, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

end MIPRE.BipartiteModel

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## The error of `lem:qld-global-success` -/

/-- **`δ_GS`**, the error of `lem:qld-global-success`: the padded strategy's failure probability
in the seeded test at `(q, 4m, d, 1)`. -/
def deltaGS (q m d : ℕ) (ε : ℝ) : ℝ :=
  5 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / q + (q : ℝ)⁻¹)) + 4 * deltaQ ε
    + ((m : ℝ) * d + 1) / q

theorem deltaGS_nonneg {q m d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ deltaGS q m d ε := by
  unfold deltaGS deltaPairs deltaPairsD kappaPairs deltaQ
  positivity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)

/-- The verifier's ambient sample: the point, the seed and the raw direction. -/
abbrev Amb (F : Type*) (m : ℕ) := Point F (4 * m) × F × Point F (4 * m)

/-! ## The families of measurements indexed by the ambient sample -/

section Families

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
  [StarOrderedRing R] [StarProper R] {S : Question F m → POVMIn (Answer F m d) R}

/-- The padded point measurement at the sample's point. -/
def ptFam (hS : ∀ q, IsPVMIn (S q).op) : Amb F m → POVMIn F (Matrix (Anc F m) (Anc F m) R) :=
  fun x => padPt hS x.1

/-- The strategy's line measurement of type `ty` at the line the sample generates. -/
def lineFam (ty : CL.Ty) (hS : ∀ q, IsPVMIn (S q).op) :
    Amb F m → POVMIn (LinePoly F (m * d + 1)) (Matrix (Anc F m) (Anc F m) R) :=
  fun x => lineMeas hm hm4 ty hS (CL.rep (lineDir hm4 ty x.2.1 x.2.2) x.1) x.2.1
    (rawSet hm4 ty x.2.1 x.2.2)

/-- The line measurement read at the parameter of the sample's point. -/
def lineEvalFam (ty : CL.Ty) (hS : ∀ q, IsPVMIn (S q).op) :
    Amb F m → POVMIn F (Matrix (Anc F m) (Anc F m) R) :=
  fun x => (lineFam hm hm4 ty hS x).map fun f => LinePoly.eval f (lineTau hm4 ty x.1 x.2.1 x.2.2)

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

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] [Ring ℬ]
  [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]
  {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
  (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op)
  (N : BipartiteModel 𝒞 (Matrix (Anc F m) (Anc F m) 𝒜) (Matrix (Anc F m) (Anc F m) ℬ))

/-- The first player's pasted line measurement at the sample's data, coarse-grained by the combining
map at the sample's point, against the second player's sandwich there, averaged over the fresh
randomness. -/
def lineTermL (PA : Question F m → POVMIn (Answer F m d) 𝒜)
    (PB : Question F m → POVMIn (Answer F m d) ℬ)
    (ty : CL.Ty) (u : Point F (4 * m)) (s : F) (raw' : Point F (4 * m)) : ℝ :=
  (Fintype.card (SubRand F m) : ℝ)⁻¹ * ∑ e : SubRand F m, ∑ a : F,
    N.bornProb (lineComb (presOf hm ty .X) (presOf hm ty .Z) d PA
        (pairCX (subPair hm4 hm ty ⟨u, s, raw'⟩ e)) (pairCZ (subPair hm4 hm ty ⟨u, s, raw'⟩ e))
        (alph u) (bet u) a)
      (ptComb (sand (hatMats PB .X (xBlk u)) (hatMats PB .Z (zBlk u))) (alph u) (bet u) a)

/-- The same with the players exchanged: the first player's sandwich against the second player's
pasted line. -/
def lineTermR (PA : Question F m → POVMIn (Answer F m d) 𝒜)
    (PB : Question F m → POVMIn (Answer F m d) ℬ)
    (ty : CL.Ty) (u : Point F (4 * m)) (s : F) (raw' : Point F (4 * m)) : ℝ :=
  (Fintype.card (SubRand F m) : ℝ)⁻¹ * ∑ e : SubRand F m, ∑ a : F,
    N.bornProb
      (ptComb (sand (hatMats PA .X (xBlk u)) (hatMats PA .Z (zBlk u))) (alph u) (bet u) a)
      (lineComb (presOf hm ty .X) (presOf hm ty .Z) d PB
        (pairCX (subPair hm4 hm ty ⟨u, s, raw'⟩ e)) (pairCZ (subPair hm4 hm ty ⟨u, s, raw'⟩ e))
        (alph u) (bet u) a)

/-- The summand of `avgSubAB` for the first player's line against the second player's point. -/
def padGL (PA : Question F m → POVMIn (Answer F m d) 𝒜)
    (PB : Question F m → POVMIn (Answer F m d) ℬ)
    (ty : CL.Ty) (a b : F) (cX cZ : LPData F m) : ℝ :=
  ∑ v : F, N.bornProb
    (lineComb (presOf hm ty .X) (presOf hm ty .Z) d PA (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v)
    (ptComb (sand (hatMats PB .X cX.pt) (hatMats PB .Z cZ.pt)) a b v)

/-- The summand of `avgSubAB` for the first player's point against the second player's line. -/
def padGR (PA : Question F m → POVMIn (Answer F m d) 𝒜)
    (PB : Question F m → POVMIn (Answer F m d) ℬ)
    (ty : CL.Ty) (a b : F) (cX cZ : LPData F m) : ℝ :=
  ∑ v : F, N.bornProb
    (ptComb (sand (hatMats PA .X cX.pt) (hatMats PA .Z cZ.pt)) a b v)
    (lineComb (presOf hm ty .X) (presOf hm ty .Z) d PB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v)

theorem sum_bornProb_lineEvalFam_ptFam (ty : CL.Ty) (hty : ty ≠ .point) (x : Amb F m) :
    ∑ a, N.bornProb ((lineEvalFam hm hm4 ty hPA x).op a) ((ptFam hPB x).op a)
      = ((rawSet hm4 ty x.2.1 x.2.2).card : ℝ)⁻¹
          * ∑ raw' ∈ rawSet hm4 ty x.2.1 x.2.2, lineTermL hm hm4 N PA PB ty x.1 x.2.1 raw' := by
  obtain ⟨u, s, raw⟩ := x
  simp only [lineEvalFam, lineFam, ptFam, lineMeas_map_eval_mats hm hm4 ty hty hPA, padPt_mats,
    N.bornProb_smul_left, N.bornProb_sum_left, lineTermL, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun raw' _ => Finset.sum_comm

theorem sum_bornProb_ptFam_lineEvalFam (ty : CL.Ty) (hty : ty ≠ .point) (x : Amb F m) :
    ∑ a, N.bornProb ((ptFam hPA x).op a) ((lineEvalFam hm hm4 ty hPB x).op a)
      = ((rawSet hm4 ty x.2.1 x.2.2).card : ℝ)⁻¹
          * ∑ raw' ∈ rawSet hm4 ty x.2.1 x.2.2, lineTermR hm hm4 N PA PB ty x.1 x.2.1 raw' := by
  obtain ⟨u, s, raw⟩ := x
  simp only [lineEvalFam, lineFam, ptFam, lineMeas_map_eval_mats hm hm4 ty hty hPB, padPt_mats,
    N.bornProb_smul_right, N.bornProb_sum_right, lineTermR, Finset.mul_sum]
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

/-- The inner sum of `avgSubAB` at a fixed padded point and raw direction, for the first player's
line. -/
theorem sum_padGL_eq (ty : CL.Ty) (s : F) (pt raw : Point F (4 * m)) :
    ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
        padGL hm N PA PB ty (alph pt) (bet pt) (subX hm4 hm ⟨pt, s, raw⟩ eX)
          (subZ hm4 hm ty ⟨pt, s, raw⟩ eZ)
      = (Fintype.card (SubRand F m) : ℝ) * lineTermL hm hm4 N PA PB ty pt s raw := by
  have hcard : (Fintype.card (SubRand F m) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [lineTermL, mul_inv_cancel_left₀ hcard]
  set G : SubRand F m → ℝ := fun e => ∑ a : F,
    N.bornProb (lineComb (presOf hm ty .X) (presOf hm ty .Z) d PA
        (pairCX (subPair hm4 hm ty ⟨pt, s, raw⟩ e)) (pairCZ (subPair hm4 hm ty ⟨pt, s, raw⟩ e))
        (alph pt) (bet pt) a)
      (ptComb (sand (hatMats PB .X (xBlk pt)) (hatMats PB .Z (zBlk pt)))
        (alph pt) (bet pt) a) with hGdef
  have hG : ∀ eX eZ : F × Point F m, padGL hm N PA PB ty (alph pt) (bet pt)
      (subX hm4 hm ⟨pt, s, raw⟩ eX) (subZ hm4 hm ty ⟨pt, s, raw⟩ eZ) = G (eX, eZ) := by
    intro eX eZ
    simp only [hGdef, padGL, subX_pt, subZ_pt, subPair]
  simp only [hG]
  exact (Fintype.sum_prod_type G).symm

theorem sum_padGR_eq (ty : CL.Ty) (s : F) (pt raw : Point F (4 * m)) :
    ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
        padGR hm N PA PB ty (alph pt) (bet pt) (subX hm4 hm ⟨pt, s, raw⟩ eX)
          (subZ hm4 hm ty ⟨pt, s, raw⟩ eZ)
      = (Fintype.card (SubRand F m) : ℝ) * lineTermR hm hm4 N PA PB ty pt s raw := by
  have hcard : (Fintype.card (SubRand F m) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [lineTermR, mul_inv_cancel_left₀ hcard]
  set G : SubRand F m → ℝ := fun e => ∑ a : F,
    N.bornProb
      (ptComb (sand (hatMats PA .X (xBlk pt)) (hatMats PA .Z (zBlk pt)))
        (alph pt) (bet pt) a)
      (lineComb (presOf hm ty .X) (presOf hm ty .Z) d PB
        (pairCX (subPair hm4 hm ty ⟨pt, s, raw⟩ e)) (pairCZ (subPair hm4 hm ty ⟨pt, s, raw⟩ e))
        (alph pt) (bet pt) a) with hGdef
  have hG : ∀ eX eZ : F × Point F m, padGR hm N PA PB ty (alph pt) (bet pt)
      (subX hm4 hm ⟨pt, s, raw⟩ eX) (subZ hm4 hm ty ⟨pt, s, raw⟩ eZ) = G (eX, eZ) := by
    intro eX eZ
    simp only [hGdef, padGR, subX_pt, subZ_pt, subPair]
  simp only [hG]
  exact (Fintype.sum_prod_type G).symm

theorem avgSubAB_padGL (ty : CL.Ty) (s : F) :
    avgSubAB hm4 hm ty s (padGL hm N PA PB ty)
      = ((Fintype.card F : ℝ) ^ (10 * m + 2))⁻¹ * ((Fintype.card (SubRand F m) : ℝ)
          * ∑ pt : Point F (4 * m), ∑ raw : Point F (4 * m), lineTermL hm hm4 N PA PB ty pt s raw)
          := by
  rw [avgSubAB, sumSubAB]
  congr 1
  simp only [sumSubAt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun pt _ => Finset.sum_congr rfl fun raw _ =>
    sum_padGL_eq hm hm4 N ty s pt raw

theorem avgSubAB_padGR (ty : CL.Ty) (s : F) :
    avgSubAB hm4 hm ty s (padGR hm N PA PB ty)
      = ((Fintype.card F : ℝ) ^ (10 * m + 2))⁻¹ * ((Fintype.card (SubRand F m) : ℝ)
          * ∑ pt : Point F (4 * m), ∑ raw : Point F (4 * m), lineTermR hm hm4 N PA PB ty pt s raw)
          := by
  rw [avgSubAB, sumSubAB]
  congr 1
  simp only [sumSubAt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun pt _ => Finset.sum_congr rfl fun raw _ =>
    sum_padGR_eq hm hm4 N ty s pt raw

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

/-- **The agreement of the first player's line read at the sample's point with the second player's
padded point measurement is the seed-average of the padded consistency quantity.** -/
theorem agreeSum_lineEvalFam_ptFam (ty : CL.Ty) (hty : ty ≠ .point) :
    N.agreeSum (uniform (Amb F m)) (lineEvalFam hm hm4 ty hPA) (ptFam hPB)
      = (Fintype.card F : ℝ)⁻¹ * ∑ s : F, avgSubAB hm4 hm ty s (padGL hm N PA PB ty) := by
  classical
  have hsum : ∑ x : Amb F m, ((rawSet hm4 ty x.2.1 x.2.2).card : ℝ)⁻¹
        * ∑ raw' ∈ rawSet hm4 ty x.2.1 x.2.2, lineTermL hm hm4 N PA PB ty x.1 x.2.1 raw'
      = ∑ s : F, ∑ pt : Point F (4 * m), ∑ raw : Point F (4 * m),
          lineTermL hm hm4 N PA PB ty pt s raw := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => ?_
    exact sum_rawSet_fiber hm4 ty s fun raw' => lineTermL hm hm4 N PA PB ty u s raw'
  simp only [avgSubAB_padGL hm hm4 N ty, BipartiteModel.agreeSum, uniform,
    sum_bornProb_lineEvalFam_ptFam hm hm4 hPA hPB N ty hty]
  rw [← Finset.mul_sum, hsum, inv_card_amb_eq]
  simp only [← Finset.mul_sum]
  ring

theorem agreeSum_ptFam_lineEvalFam (ty : CL.Ty) (hty : ty ≠ .point) :
    N.agreeSum (uniform (Amb F m)) (ptFam hPA) (lineEvalFam hm hm4 ty hPB)
      = (Fintype.card F : ℝ)⁻¹ * ∑ s : F, avgSubAB hm4 hm ty s (padGR hm N PA PB ty) := by
  classical
  have hsum : ∑ x : Amb F m, ((rawSet hm4 ty x.2.1 x.2.2).card : ℝ)⁻¹
        * ∑ raw' ∈ rawSet hm4 ty x.2.1 x.2.2, lineTermR hm hm4 N PA PB ty x.1 x.2.1 raw'
      = ∑ s : F, ∑ pt : Point F (4 * m), ∑ raw : Point F (4 * m),
          lineTermR hm hm4 N PA PB ty pt s raw := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => ?_
    exact sum_rawSet_fiber hm4 ty s fun raw' => lineTermR hm hm4 N PA PB ty u s raw'
  simp only [avgSubAB_padGR hm hm4 N ty, BipartiteModel.agreeSum, uniform,
    sum_bornProb_ptFam_lineEvalFam hm hm4 hPA hPB N ty hty]
  rw [← Finset.mul_sum, hsum, inv_card_amb_eq]
  simp only [← Finset.mul_sum]
  ring

end LinePoint

/-! ## From the padded consistency to the agreement bounds

In the expanded model the padded point measurement is the first player's sandwich read along
`(alpha, beta)`, which is exactly the point side of `padded_lines_consistency` and a coarse-graining
of the sandwich whose agreement `combined_points_pts` bounds; nothing has to be compressed. -/

section Transfer

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] [Ring ℬ]
  [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]
  {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
  {ε : ℝ}

/-- The two items of `lem:qld-expanded-lines` for the presentation of a line type. -/
theorem presOf_items (hM : ‖M.ψ‖ = 1) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hd : 1 ≤ d) (ty : CL.Ty) (W : Bas) :
    (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        (M.reg (Anc F m)).xSqNorm ((presOf hm ty W).lineMats d PA c f)
          ((presOf hm ty W).lineMats d PB c f) ≤ 172 * ε)
      ∧ ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
          (M.reg (Anc F m)).xSqNorm (hatMats PA W (c.pt W) a)
            ((presOf hm ty W).lineEvalMats d PB c a) ≤ 172 * ε := by
  cases ty
  · exact aPres_items (PB := PB) hd hM hfail W
  · exact aPres_items (PB := PB) hd hM hfail W
  · exact dPres_items (PB := PB) hd hM hfail W

/-- The second item with the players exchanged: the first player's line read at the point against
the second player's point measurement. -/
theorem presOf_items_swap (hM : ‖M.ψ‖ = 1) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hd : 1 ≤ d) (ty : CL.Ty) (W : Bas) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        (M.reg (Anc F m)).xSqNorm ((presOf hm ty W).lineEvalMats d PA c a)
          (hatMats PB W (c.pt W) a) ≤ 172 * ε := by
  have h := (presOf_items hm (M := M.swap) (PA := PB) (PB := PA) (swapVec_unit hM)
    (povmValue_swapped_le hfail) hd ty W).2
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
    congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
      (Finset.sum_congr rfl fun a _ => ?_))) h
  exact (hatVec_swapVec_xSqNorm M _ _).symm

omit [Algebra (ZMod 2) F] in
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

/-- **The first player's line against the second player's point, at a fixed seed**:
`lem:qld-padded-lines` in the other register version, in the expanded model. -/
theorem one_sub_avgSubAB_padGL_le (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op) (hd : 1 ≤ d) (ty : CL.Ty)
    (s : F) :
    1 - avgSubAB hm4 hm ty s (padGL hm (M.reg (Anc F m)) PA PB ty)
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) :=
  padded_lines_consistency_swap hm4 hM hfail hPA hPB
    (presOf hm ty .X) (presOf hm ty .Z) (factorsX_presOf hm ty) (factorsZ_presOf hm ty)
    (presOf_items hm hM hfail hd ty .X).1 (presOf_items_swap hm hM hfail hd ty .X)
    (presOf_items_swap hm hM hfail hd ty .Z) (presOf_coll hm ty) ty s

/-- **The first player's point against the second player's line, at a fixed seed.** -/
theorem one_sub_avgSubAB_padGR_le (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op) (hd : 1 ≤ d) (ty : CL.Ty)
    (s : F) :
    1 - avgSubAB hm4 hm ty s (padGR hm (M.reg (Anc F m)) PA PB ty)
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) :=
  padded_lines_consistency hm4 hM hfail hPA hPB
    (presOf hm ty .X) (presOf hm ty .Z) (factorsX_presOf hm ty) (factorsZ_presOf hm ty)
    (presOf_items hm hM hfail hd ty .X).1 (presOf_items hm hM hfail hd ty .X).2
    (presOf_items hm hM hfail hd ty .Z).2 (presOf_coll hm ty) ty s

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

/-- **The line-point subtests, the first player's line**: the agreement of the first player's line
measurement read at the sample's point with the second player's padded point measurement, averaged
over the ambient sample, in the expanded model. -/
theorem one_sub_agreeSum_lineEval_pt_le (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op) (hd : 1 ≤ d) (ty : CL.Ty)
    (hty : ty ≠ .point) :
    1 - (M.reg (Anc F m)).agreeSum (uniform (Amb F m)) (lineEvalFam hm hm4 ty hPA) (ptFam hPB)
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  rw [agreeSum_lineEvalFam_ptFam hm hm4 hPA hPB _ ty hty]
  exact one_sub_inv_card_mul_sum_le fun s =>
    one_sub_avgSubAB_padGL_le hm hm4 hM hfail hPA hPB hd ty s

/-- **The line-point subtests, the second player's line.** -/
theorem one_sub_agreeSum_pt_lineEval_le (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op) (hd : 1 ≤ d) (ty : CL.Ty)
    (hty : ty ≠ .point) :
    1 - (M.reg (Anc F m)).agreeSum (uniform (Amb F m)) (ptFam hPA) (lineEvalFam hm hm4 ty hPB)
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  rw [agreeSum_ptFam_lineEvalFam hm hm4 hPA hPB _ ty hty]
  exact one_sub_inv_card_mul_sum_le fun s =>
    one_sub_avgSubAB_padGR_le hm hm4 hM hfail hPA hPB hd ty s

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
self-agreement item of `lem:qld-combined-points` (`combined_points_pts`), coarse-grained along
`(alpha, beta)`: agreement only increases under a common coarse-graining. -/
theorem one_sub_agreeSum_pt_pt_le (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op) :
    1 - (M.reg (Anc F m)).agreeSum (uniform (Amb F m)) (ptFam hPA) (ptFam hPB) ≤ deltaQ ε := by
  classical
  set N := M.reg (Anc F m) with hN
  obtain ⟨h1, -, -⟩ := combined_points_pts (PA := PA) (PB := PB) hM hfail hPA hPB
  have hu : ∀ u : Point F (4 * m),
      1 - ∑ a, N.bornProb ((padPt hPA u).op a) ((padPt hPB u).op a)
        ≤ 1 - ∑ p : F × F, N.bornProb (sand (hatMats PA .X (xBlk u)) (hatMats PA .Z (zBlk u)) p)
            (sand (hatMats PB .X (xBlk u)) (hatMats PB .Z (zBlk u)) p) := by
    intro u
    have h := sum_bornProb_le_fibre N (sand (hatMats PA .X (xBlk u)) (hatMats PA .Z (zBlk u)))
      (sand (hatMats PB .X (xBlk u)) (hatMats PB .Z (zBlk u)))
      (fun p => (padPtPair hPA u).op_nonneg p) (fun p => (padPtPair hPB u).op_nonneg p)
      (padComb u)
    have heq : ∀ a, N.bornProb ((padPt hPA u).op a) ((padPt hPB u).op a)
        = N.bornProb
            (∑ p ∈ univ.filter fun p => padComb u p = a,
              sand (hatMats PA .X (xBlk u)) (hatMats PA .Z (zBlk u)) p)
            (∑ p ∈ univ.filter fun p => padComb u p = a,
              sand (hatMats PB .X (xBlk u)) (hatMats PB .Z (zBlk u)) p) := fun a => by
      rw [padPt, padPt, POVMIn.map_op, POVMIn.map_op]
      rfl
    simp only [heq]
    linarith
  have hμ : ∑ x : Amb F m, uniform (Amb F m) x = 1 := by
    simp only [uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hexp : 1 - N.agreeSum (uniform (Amb F m)) (ptFam hPA) (ptFam hPB)
      = ∑ x : Amb F m, uniform (Amb F m) x * (1 - ∑ a, N.bornProb
          ((padPt hPA x.1).op a) ((padPt hPB x.1).op a)) := by
    rw [BipartiteModel.agreeSum]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hμ]
    rfl
  have hpts : ∑ y : Point F m × Point F m, (Fintype.card (Point F m × Point F m) : ℝ)⁻¹
        * (1 - ∑ p : F × F, N.bornProb (sand (hatMats PA .X y.1) (hatMats PA .Z y.2) p)
            (sand (hatMats PB .X y.1) (hatMats PB .Z y.2) p))
      = 1 - ∑ y : Point F m × Point F m, (Fintype.card (Point F m × Point F m) : ℝ)⁻¹
          * ∑ p : F × F, N.bornProb (sand (hatMats PA .X y.1) (hatMats PA .Z y.2) p)
            (sand (hatMats PB .X y.1) (hatMats PB .Z y.2) p) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sum_uniform_pts]
  rw [hexp]
  calc ∑ x : Amb F m, uniform (Amb F m) x * (1 - ∑ a, N.bornProb
          ((padPt hPA x.1).op a) ((padPt hPB x.1).op a))
      ≤ ∑ x : Amb F m, (Fintype.card (Amb F m) : ℝ)⁻¹
          * (1 - ∑ p : F × F, N.bornProb
              (sand (hatMats PA .X (xBlk x.1)) (hatMats PA .Z (zBlk x.1)) p)
              (sand (hatMats PB .X (xBlk x.1)) (hatMats PB .Z (zBlk x.1)) p)) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hu x.1)
          (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = ∑ y : Point F m × Point F m, (Fintype.card (Point F m × Point F m) : ℝ)⁻¹
          * (1 - ∑ p : F × F, N.bornProb (sand (hatMats PA .X y.1) (hatMats PA .Z y.2) p)
            (sand (hatMats PB .X y.1) (hatMats PB .Z y.2) p)) :=
        avg_amb_blocks fun x z => 1 - ∑ p : F × F,
          N.bornProb (sand (hatMats PA .X x) (hatMats PA .Z z) p)
            (sand (hatMats PB .X x) (hatMats PB .Z z) p)
    _ ≤ deltaQ ε := by
        rw [hpts]
        exact h1

end Transfer

/-! ## The identical-line subtest

Two distinct polynomial outcomes are told apart by reading both at a uniformly random parameter of
the line, up to `(md + 1)/q`; the parameter of the sample's point is uniform on the line once the
raw direction is fixed and the line is not degenerate, because translating the point along the
line is a bijection of the sample space that fixes the line and shifts the parameter. -/

section Lines

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] [Ring ℬ]
  [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]
  {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
  (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op)
  {𝒞' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞']
  (N : BipartiteModel 𝒞' (Matrix (Anc F m) (Anc F m) 𝒜) (Matrix (Anc F m) (Anc F m) ℬ))

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
def evDef (LA : POVMIn (LinePoly F (m * d + 1)) (Matrix (Anc F m) (Anc F m) 𝒜))
    (LB : POVMIn (LinePoly F (m * d + 1)) (Matrix (Anc F m) (Anc F m) ℬ)) (t : F) : ℝ :=
  1 - ∑ a : F, N.bornProb ((LA.map fun f => LinePoly.eval f t).op a)
    ((LB.map fun f => LinePoly.eval f t).op a)

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem evDef_nonneg (hN : ‖N.ψ‖ = 1)
    (LA : POVMIn (LinePoly F (m * d + 1)) (Matrix (Anc F m) (Anc F m) 𝒜))
    (LB : POVMIn (LinePoly F (m * d + 1)) (Matrix (Anc F m) (Anc F m) ℬ)) (t : F) :
    0 ≤ evDef N LA LB t :=
  sub_nonneg.mpr (sum_bornProb_diag_le_one hN _ _ (fun a => POVMIn.op_nonneg _ a)
    (fun a => POVMIn.op_nonneg _ a) (POVMIn.sum_op _) (POVMIn.sum_op _))

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem evDef_le_one (LA : POVMIn (LinePoly F (m * d + 1)) (Matrix (Anc F m) (Anc F m) 𝒜))
    (LB : POVMIn (LinePoly F (m * d + 1)) (Matrix (Anc F m) (Anc F m) ℬ)) (t : F) :
    evDef N LA LB t ≤ 1 := by
  have : 0 ≤ ∑ a : F, N.bornProb ((LA.map fun f => LinePoly.eval f t).op a)
      ((LB.map fun f => LinePoly.eval f t).op a) :=
    Finset.sum_nonneg fun a _ => N.bornProb_nonneg (POVMIn.op_nonneg _ a) (POVMIn.op_nonneg _ a)
  unfold evDef
  linarith

/-- The disagreement of the two line measurements read at the sample's point is the disagreement of
the evaluated families. -/
theorem evDef_lineTau (ty : CL.Ty) (x : Amb F m) :
    evDef N (lineFam hm hm4 ty hPA x) (lineFam hm hm4 ty hPB x) (lineTau hm4 ty x.1 x.2.1 x.2.2)
      = 1 - ∑ a : F, N.bornProb ((lineEvalFam hm hm4 ty hPA x).op a)
          ((lineEvalFam hm hm4 ty hPB x).op a) := rfl

/-- **At a fixed seed and raw direction, averaging the evaluated disagreement over the parameter
is averaging it over the point**, unless the direction is degenerate, in which case the average is
at most one. -/
theorem sum_avg_evDef_le (hN : ‖N.ψ‖ = 1) (ty : CL.Ty) (s : F) (raw : Point F (4 * m)) :
    ∑ u : Point F (4 * m), (Fintype.card F : ℝ)⁻¹ * ∑ t : F,
        evDef N (lineFam hm hm4 ty hPA (u, s, raw)) (lineFam hm hm4 ty hPB (u, s, raw)) t
      ≤ ∑ u : Point F (4 * m), evDef N (lineFam hm hm4 ty hPA (u, s, raw))
          (lineFam hm hm4 ty hPB (u, s, raw)) (lineTau hm4 ty u s raw)
        + (if lineDir hm4 ty s raw = 0 then (Fintype.card (Point F (4 * m)) : ℝ) else 0) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases hdir : lineDir hm4 ty s raw = 0
  · rw [if_pos hdir]
    have h1 : ∑ u : Point F (4 * m), (Fintype.card F : ℝ)⁻¹ * ∑ t : F,
        evDef N (lineFam hm hm4 ty hPA (u, s, raw)) (lineFam hm hm4 ty hPB (u, s, raw)) t
        ≤ ∑ _u : Point F (4 * m), (1 : ℝ) := by
      refine Finset.sum_le_sum fun u _ => ?_
      calc (Fintype.card F : ℝ)⁻¹ * ∑ t : F,
            evDef N (lineFam hm hm4 ty hPA (u, s, raw)) (lineFam hm hm4 ty hPB (u, s, raw)) t
          ≤ (Fintype.card F : ℝ)⁻¹ * ∑ _t : F, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => evDef_le_one N _ _ t)
              (inv_nonneg.mpr (Nat.cast_nonneg _))
        _ = 1 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hq]
    have h2 : 0 ≤ ∑ u : Point F (4 * m), evDef N (lineFam hm hm4 ty hPA (u, s, raw))
        (lineFam hm hm4 ty hPB (u, s, raw)) (lineTau hm4 ty u s raw) :=
      Finset.sum_nonneg fun u _ => evDef_nonneg N hN _ _ _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h1
    linarith
  · rw [if_neg hdir, add_zero, ← Finset.mul_sum]
    have hw : ∃ j, lineDir hm4 ty s raw j ≠ 0 := by
      by_contra h
      exact hdir (funext fun j => not_not.mp fun hj => h ⟨j, hj⟩)
    have hLA : ∀ (u : Point F (4 * m)) (t : F),
        lineFam hm hm4 ty hPA (u + t • lineDir hm4 ty s raw, s, raw)
          = lineFam hm hm4 ty hPA (u, s, raw) := by
      intro u t
      simp only [lineFam, rep_add_smul]
    have hLB : ∀ (u : Point F (4 * m)) (t : F),
        lineFam hm hm4 ty hPB (u + t • lineDir hm4 ty s raw, s, raw)
          = lineFam hm hm4 ty hPB (u, s, raw) := by
      intro u t
      simp only [lineFam, rep_add_smul]
    have hτ : ∀ (u : Point F (4 * m)) (t : F),
        lineTau hm4 ty (u + t • lineDir hm4 ty s raw) s raw = lineTau hm4 ty u s raw + t :=
      fun u t => lineParam_rep_add_smul hw u t
    rw [sum_shift_param (lineDir hm4 ty s raw) (fun u => lineFam hm hm4 ty hPA (u, s, raw))
      (fun u => lineFam hm hm4 ty hPB (u, s, raw)) (fun u => lineTau hm4 ty u s raw) hLA hLB hτ
      (fun LA LB t => evDef N LA LB t), ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

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
theorem one_sub_agreeSum_uniform_eq
    (P : Amb F m → POVMIn F (Matrix (Anc F m) (Anc F m) 𝒜))
    (Q : Amb F m → POVMIn F (Matrix (Anc F m) (Anc F m) ℬ)) :
    1 - N.agreeSum (uniform (Amb F m)) P Q
      = ∑ x : Amb F m, uniform (Amb F m) x
          * (1 - ∑ a : F, N.bornProb ((P x).op a) ((Q x).op a)) := by
  rw [BipartiteModel.agreeSum]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sum_uniform_amb]

/-- **The identical-line agreement, through the triangle**: the first player's line read at the
sample's point agrees with the second player's, because each agrees with the padded point
measurements there. -/
theorem one_sub_agreeSum_lineEval_lineEval_le {M : BipartiteModel 𝒞 𝒜 ℬ} {ε : ℝ}
    (hM : ‖M.ψ‖ = 1) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (hε : 0 ≤ ε)
    (hd : 1 ≤ d) (ty : CL.Ty) (hty : ty ≠ .point) :
    1 - (M.reg (Anc F m)).agreeSum (uniform (Amb F m)) (lineEvalFam hm hm4 ty hPA)
        (lineEvalFam hm hm4 ty hPB)
      ≤ 11 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹)
          + deltaQ ε) := by
  have hΨ : ‖(M.reg (Anc F m)).ψ‖ = 1 := hatVec_unit hM
  have hQ0 : 0 ≤ deltaQ ε := by
    unfold deltaQ
    positivity
  have hP0 : 0 ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹)
      := by
    unfold deltaPairs deltaPairsD kappaPairs deltaQ
    positivity
  refine (M.reg (Anc F m)).agreeSum_triangle uniform_amb_nonneg sum_uniform_amb hΨ
    (lineEvalFam hm hm4 ty hPA) (ptFam hPA) (ptFam hPB) (lineEvalFam hm hm4 ty hPB) ?_ ?_ ?_
  · exact le_trans (one_sub_agreeSum_lineEval_pt_le hm hm4 hM hfail hPA hPB hd ty hty)
      (le_add_of_nonneg_right hQ0)
  · exact le_trans (one_sub_agreeSum_pt_pt_le hm hM hfail hPA hPB) (le_add_of_nonneg_left hP0)
  · exact le_trans (one_sub_agreeSum_pt_lineEval_le hm hm4 hM hfail hPA hPB hd ty hty)
      (le_add_of_nonneg_right hQ0)

end Lines

/-! ## The nine subtests, and the value -/

section Assembly

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜] [Ring ℬ]
  [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]
  {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
  {ε : ℝ}

/-- The failure weight of one ordered pair of types: the conditional failure of the padded strategy
in the expanded model at the questions of the two types, averaged over the ambient sample. -/
def padW (M : BipartiteModel 𝒞 𝒜 ℬ) (hPA : ∀ q, IsPVMIn (PA q).op)
    (hPB : ∀ q, IsPVMIn (PB q).op) (tA tB : CL.Ty) : ℝ :=
  ∑ x : Amb F m, uniform (Amb F m) x
    * (M.reg (Anc F m)).condFail (clGame (d := d) (ldc := 1) hm4)
        (padStrat hm hm4 hPA) (padStrat hm hm4 hPB)
        (lineQ hm4 tA x.1 x.2.1 x.2.2) (lineQ hm4 tB x.1 x.2.1 x.2.2)

variable {M : BipartiteModel 𝒞 𝒜 ℬ} (hM : ‖M.ψ‖ = 1)
  (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
  (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op)

include hM hfail in
theorem padW_point_point_le : padW hm hm4 M hPA hPB .point .point ≤ deltaQ ε := by
  have h := one_sub_agreeSum_pt_pt_le hm hM hfail hPA hPB
  rw [one_sub_agreeSum_uniform_eq] at h
  refine le_trans (Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left ?_ (uniform_amb_nonneg x)) h
  exact condFail_point_point_le hm hm4 hPA hPB _ x.1

include hM hfail in
theorem padW_line_point_le (hd : 1 ≤ d) (hlegA : LegalSupport PA) (ty : CL.Ty)
    (hty : ty ≠ .point) :
    padW hm hm4 M hPA hPB ty .point
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  have h := one_sub_agreeSum_lineEval_pt_le hm hm4 hM hfail hPA hPB hd ty hty
  rw [one_sub_agreeSum_uniform_eq] at h
  refine le_trans (Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left ?_ (uniform_amb_nonneg x)) h
  exact condFail_lineQ_point_le hm hm4 hPA hPB _ ty hty hd hlegA x.1 x.2.1 x.2.2

include hM hfail in
theorem padW_point_line_le (hd : 1 ≤ d) (hlegB : LegalSupport PB) (ty : CL.Ty)
    (hty : ty ≠ .point) :
    padW hm hm4 M hPA hPB .point ty
      ≤ (m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹) := by
  have h := one_sub_agreeSum_pt_lineEval_le hm hm4 hM hfail hPA hPB hd ty hty
  rw [one_sub_agreeSum_uniform_eq] at h
  refine le_trans (Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left ?_ (uniform_amb_nonneg x)) h
  exact condFail_point_lineQ_le hm hm4 hPA hPB _ ty hty hd hlegB x.1 x.2.1 x.2.2

include hM in
theorem padW_aline_dline_le : padW hm hm4 M hPA hPB .aline .dline ≤ 0 := by
  have hΨ : ‖(M.reg (Anc F m)).ψ‖ = 1 := hatVec_unit hM
  refine le_trans (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (condFail_aline_dline_le hm hm4 hPA hPB _ hΨ x.1 x.2.1 x.2.2 x.1 x.2.1 x.2.2)
    (uniform_amb_nonneg x)) ?_
  simp

include hM in
theorem padW_dline_aline_le : padW hm hm4 M hPA hPB .dline .aline ≤ 0 := by
  have hΨ : ‖(M.reg (Anc F m)).ψ‖ = 1 := hatVec_unit hM
  refine le_trans (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (condFail_dline_aline_le hm hm4 hPA hPB _ hΨ x.1 x.2.1 x.2.2 x.1 x.2.1 x.2.2)
    (uniform_amb_nonneg x)) ?_
  simp

include hM hfail in
/-- **The identical-line subtests.** -/
theorem padW_line_line_le (hε : 0 ≤ ε) (hd : 1 ≤ d) (ty : CL.Ty) (hty : ty ≠ .point) :
    padW hm hm4 M hPA hPB ty ty
      ≤ 11 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹)
            + deltaQ ε)
        + ((m : ℝ) * d + 1) / Fintype.card F + (Fintype.card F : ℝ)⁻¹ := by
  set Ψ := M.reg (Anc F m) with hΨdef
  have hΨ : ‖Ψ.ψ‖ = 1 := hatVec_unit hM
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcA : (Fintype.card (Amb F m) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hP0 : (0 : ℝ) ≤ Fintype.card (Point F (4 * m)) := Nat.cast_nonneg _
  have hcAinv : (0 : ℝ) ≤ (Fintype.card (Amb F m) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  -- the per-sample bound, by polynomial separation
  have h1 : ∀ x : Amb F m,
      Ψ.condFail (clGame (d := d) (ldc := 1) hm4) (padStrat hm hm4 hPA) (padStrat hm hm4 hPB)
          (lineQ hm4 ty x.1 x.2.1 x.2.2) (lineQ hm4 ty x.1 x.2.1 x.2.2)
        ≤ (Fintype.card F : ℝ)⁻¹ * ∑ t : F,
            evDef Ψ (lineFam hm hm4 ty hPA x) (lineFam hm hm4 ty hPB x) t
          + ((m : ℝ) * d + 1) / Fintype.card F := by
    intro x
    refine le_trans (condFail_lineQ_lineQ_le hm hm4 hPA hPB Ψ ty hty x.1 x.2.1 x.2.2) ?_
    have h := one_sub_sum_bornProb_le_avg_eval hΨ (lineFam hm hm4 ty hPA x)
      (lineFam hm hm4 ty hPB x)
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
  calc padW hm hm4 M hPA hPB ty ty
      ≤ ∑ x : Amb F m, uniform (Amb F m) x * ((Fintype.card F : ℝ)⁻¹ * ∑ t : F,
            evDef Ψ (lineFam hm hm4 ty hPA x) (lineFam hm hm4 ty hPB x) t
          + ((m : ℝ) * d + 1) / Fintype.card F) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h1 x) (uniform_amb_nonneg x)
    _ = (Fintype.card (Amb F m) : ℝ)⁻¹ * ∑ x : Amb F m, ((Fintype.card F : ℝ)⁻¹ * ∑ t : F,
            evDef Ψ (lineFam hm hm4 ty hPA x) (lineFam hm hm4 ty hPB x) t)
          + ((m : ℝ) * d + 1) / Fintype.card F := by
        simp only [uniform, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcA, one_mul]
    _ ≤ (Fintype.card (Amb F m) : ℝ)⁻¹ * (∑ x : Amb F m,
            evDef Ψ (lineFam hm hm4 ty hPA x) (lineFam hm hm4 ty hPB x)
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
        exact sum_avg_evDef_le hm hm4 hPA hPB Ψ hΨ ty s raw
    _ ≤ (Fintype.card (Amb F m) : ℝ)⁻¹ * ∑ x : Amb F m,
            evDef Ψ (lineFam hm hm4 ty hPA x) (lineFam hm hm4 ty hPB x)
              (lineTau hm4 ty x.1 x.2.1 x.2.2)
          + (Fintype.card F : ℝ)⁻¹ + ((m : ℝ) * d + 1) / Fintype.card F := by
        rw [mul_add]
        linarith
    _ = (1 - Ψ.agreeSum (uniform (Amb F m)) (lineEvalFam hm hm4 ty hPA)
          (lineEvalFam hm hm4 ty hPB))
          + (Fintype.card F : ℝ)⁻¹ + ((m : ℝ) * d + 1) / Fintype.card F := by
        rw [one_sub_agreeSum_uniform_eq]
        simp only [uniform, ← Finset.mul_sum, evDef_lineTau]
    _ ≤ 11 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹)
            + deltaQ ε)
        + ((m : ℝ) * d + 1) / Fintype.card F + (Fintype.card F : ℝ)⁻¹ := by
        have := one_sub_agreeSum_lineEval_lineEval_le hm hm4 hPA hPB hM hfail hε hd ty hty
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
    1 - (M.reg (Anc F m)).povmValue (clGame (d := d) (ldc := 1) hm4)
        (padStrat hm hm4 hPA) (padStrat hm hm4 hPB)
      = (9 : ℝ)⁻¹ * ∑ tA : CL.Ty, ∑ tB : CL.Ty, padW hm hm4 M hPA hPB tA tB := by
  rw [(M.reg (Anc F m)).one_sub_povmValue_clGame hm4, sum_sample_eq, card_sample]
  simp only [Sample.question_fst_eq_lineQ, Sample.question_snd_eq_lineQ, padW, uniform,
    Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun tA _ => Finset.sum_congr rfl fun tB _ =>
    Finset.sum_congr rfl fun x _ => ?_
  rw [mul_inv, mul_assoc]

include hM hfail in
/-- **`lem:qld-global-success`: the padded strategy wins the seeded low individual degree test at
`(q, 4m, d, 1)` with probability at least `1 - δ_GS`**, in the expanded model `M.reg (Anc F m)`, with
`δ_GS = 5 δ_combine + 4 δ_Q + (md + 1)/q` and `δ_combine = m² δ_P(ε, md/q + 1/q)`: the stage-4a
interface. For a projective strategy `S : M.ProjStrat (qldGame hm)` the hypotheses are
`S.ψ_unit`, `hfail : 1 - S.value ≤ ε`, `S.projA`, `S.projB`. -/
theorem padStrat_value (hε : 0 ≤ ε) (hlegA : LegalSupport PA) (hlegB : LegalSupport PB)
    (hd : 1 ≤ d) :
    1 - deltaGS (Fintype.card F) m d ε
      ≤ (M.reg (Anc F m)).povmValue (clGame (d := d) (ldc := 1) hm4)
          (padStrat hm hm4 hPA) (padStrat hm hm4 hPB) := by
  suffices h : 1 - (M.reg (Anc F m)).povmValue (clGame (d := d) (ldc := 1) hm4)
        (padStrat hm hm4 hPA) (padStrat hm hm4 hPB)
      ≤ 5 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / Fintype.card F + (Fintype.card F : ℝ)⁻¹))
        + 4 * deltaQ ε + ((m : ℝ) * d + 1) / Fintype.card F by
    unfold deltaGS
    linarith
  rw [one_sub_povmValue_padStrat_eq hm hm4 hPA hPB, sum_ty, sum_ty, sum_ty, sum_ty]
  have hpp := padW_point_point_le hm hm4 hM hfail hPA hPB
  have hap := padW_line_point_le hm hm4 hM hfail hPA hPB hd hlegA .aline (by decide)
  have hdp := padW_line_point_le hm hm4 hM hfail hPA hPB hd hlegA .dline (by decide)
  have hpa := padW_point_line_le hm hm4 hM hfail hPA hPB hd hlegB .aline (by decide)
  have hpd := padW_point_line_le hm hm4 hM hfail hPA hPB hd hlegB .dline (by decide)
  have haa := padW_line_line_le hm hm4 hM hfail hPA hPB hε hd .aline (by decide)
  have hdd := padW_line_line_le hm hm4 hM hfail hPA hPB hε hd .dline (by decide)
  have had := padW_aline_dline_le hm hm4 hM hPA hPB
  have hda := padW_dline_aline_le hm hm4 hM hPA hPB
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

end
