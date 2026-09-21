/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.PaddedLines
import MIPRE.Foundations.POVMMix
import MIPRE.Background.LIDT.Adapter.Value

/-!
# The padded strategy for the seeded low individual degree test

Stage 4 of the Pauli basis test's analysis (`lem:qld-global-setup`, `lem:qld-global-success`)
assembles the padded point and line measurements of `lem:qld-padded-points` and
`lem:qld-padded-lines` into a strategy for the seeded test `clGame` at parameters
`(q, 4m, d, 1)`, and shows that it succeeds with probability `1 - O(δ_combine + δ_Q + md/q)`.
This file defines the strategy and bounds its conditional failure at each of the seeded test's
question pairs by an agreement defect of the measurements it is built from; the averages over the
verifier's samples, and the value bound, are in `PaddedValue.lean`.

## The registers, and why the strategy is a family of POVMs

The strategy lives on the registers `(dA × Anc F m) × (F × F)` of `extHat ψ`: the player's own
space, the expansion's ancilla, and the combining coefficients' ancilla that `lem:qld-padded-points`
dilates its sandwich with. Its point measurement is the *sandwich* `M^X_a M^Z_b M^X_a` of the
hatted point measurements, coarse-grained along `(a, b) ↦ α a + β b`, extended by the identity to
the last register; its line measurements are the padded line measurements `padLineMats`. Both are
POVMs and neither is projective, so the strategy is a family of POVMs, and one Naimark dilation at
the end (`clSoundness_ldc_one_deltaCL_of_povm`) makes it the projective strategy the soundness
theorem takes. The dilated point measurement of `lem:qld-padded-points` is not used: on the
extended state the Born rule sees only compressions (`bornProb_extVec2`), so every bound proved
for it is a bound for the sandwich.

## A function of the question

The seeded test asks for a measurement per *question*, while `padLineMats` is indexed by the
*data* `⟨pt, s, raw⟩` a sample generates the question from. A line question carries the canonical
base point `u₀` of the line, the seed, and for a diagonal line the truncated direction `v'`; the
strategy answers it with the padded line measurement at the data `⟨u₀, s, raw⟩`, **averaged over
the raw directions that produce the question** (`rawFiber`). Two things make this the right
choice. The decider reads the answer polynomial at the parameter of the sampled point relative to
`u₀`, and moving the data's point to the sampled point along the line does not change the padded
line measurement (`pasteLine_subPair_padShift`), so what the decider reads is `padLineMats` at the
sample's own data, coarse-grained by evaluation at the sample's point --- exactly the quantity
`lem:qld-padded-lines` controls (`lineMeas_map_eval_mats`). And the sample distribution averages
uniformly over the raw direction, so by linearity of the Born rule the strategy's failure at a
question is the average of the per-sample quantities.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA : Type} [Fintype dA] [DecidableEq dA] {hm : m ∣ Fintype.card F}

/-! ## The padded point measurement -/

/-- The sandwich `M^X_a M^Z_b M^X_a` of the hatted point measurements at the `X` and `Z` blocks of
a padded point, as a POVM with outcomes the pairs `(a, b)`. -/
def padPtPair {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) :
    POVM (F × F) (dA × Anc F m) :=
  sandPOVM (isPVM_hatMats hM .X (xBlk u)) (isPVM_hatMats hM .Z (zBlk u))

@[simp] theorem padPtPair_mats {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) (r : F × F) :
    (((padPtPair hM u).mats r).val) = sand (hatMats M .X (xBlk u)) (hatMats M .Z (zBlk u)) r :=
  rfl

/-- The combining coefficients' reading of a pair outcome at a padded point:
`(a, b) ↦ α a + β b`. -/
def padComb (u : Point F (4 * m)) (r : F × F) : F := alph u * r.1 + bet u * r.2

/-- **The padded point measurement**: the sandwich read through the combining coefficients and
extended by the identity to the coefficients' ancilla, the strategy's answer to a point question
as a POVM with outcomes in `F`. -/
def padPt {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) :
    POVM F ((dA × Anc F m) × (F × F)) :=
  ((padPtPair hM u).aOp).map (padComb u)

theorem padPt_mats {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) (a : F) :
    ((padPt hM u).mats a).val
      = aOp (ptComb (sand (hatMats M .X (xBlk u)) (hatMats M .Z (zBlk u))) (alph u) (bet u) a) := by
  rw [padPt, POVM.map_mats, ptComb, aOp_sum]
  rfl

/-! ## The padded line measurements, as POVMs -/

variable (hm4 : 4 * m ∣ Fintype.card F)

/-- `padLineMats`, bundled as a POVM. -/
def padLinePOVM (ty : CL.Ty) (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    {M : Question F m → POVM (Answer F m d) dA} (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (P : LPData F (4 * m)) : POVM (LinePoly F (m * d + 1)) ((dA × Anc F m) × (F × F)) :=
  POVM.ofPosSemidef (padLineMats hm4 ty PX PZ M P) (posSemidef_padLineMats hm4 ty PX PZ hM P)
    (sum_padLineMats hm4 ty PX PZ hM P)

@[simp] theorem padLinePOVM_mats (ty : CL.Ty) (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    {M : Question F m → POVM (Answer F m d) dA} (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (P : LPData F (4 * m)) (f : LinePoly F (m * d + 1)) :
    (((padLinePOVM hm4 ty PX PZ hM P).mats f).val) = padLineMats hm4 ty PX PZ M P f := rfl

variable (hm)

/-- The presentation of a line type on side `W`: the diagonal one for `dline`, the axis-parallel
one otherwise. -/
def presOf (ty : CL.Ty) (W : Bas) : LinePres F m hm W :=
  match ty with
  | .dline => dPres hm W
  | _ => aPres hm W

theorem factorsX_presOf (ty : CL.Ty) : FactorsX (presOf hm ty .X) := by
  cases ty
  · exact factorsX_aPres
  · exact factorsX_aPres
  · exact factorsX_dPres

theorem factorsZ_presOf (ty : CL.Ty) : FactorsZ (presOf hm ty .Z) := by
  cases ty
  · exact factorsZ_aPres
  · exact factorsZ_aPres
  · exact factorsZ_dPres

theorem presOf_base_eq (ty : CL.Ty) (W : Bas) (c : Content F m) :
    (presOf hm ty W).base c = CL.rep ((presOf hm ty W).dir c) (c.pt W) := by
  cases ty
  · exact aPres_base_eq hm W c
  · exact aPres_base_eq hm W c
  · exact dPres_base_eq hm W c

theorem presOf_dir_ofLPX (ty : CL.Ty) (hty : ty ≠ .point) (D : LPData F m) (u : Point F m) :
    (presOf hm ty .X).dir (ofLPX D u) = D.dir hm ty := by
  cases ty
  · exact absurd rfl hty
  · exact aPres_dir_ofLPX hm D u
  · exact dPres_dir_ofLPX hm D u

theorem presOf_dir_ofLPZ (ty : CL.Ty) (hty : ty ≠ .point) (D : LPData F m) (u : Point F m) :
    (presOf hm ty .Z).dir (ofLPZ D u) = D.dir hm ty := by
  cases ty
  · exact absurd rfl hty
  · exact aPres_dir_ofLPZ hm D u
  · exact dPres_dir_ofLPZ hm D u

/-- **The line measurement of the padded strategy**: the padded line POVM at the data
`⟨u₀, s, raw⟩`, averaged over the raw directions in `S`. -/
def lineMeas (ty : CL.Ty) {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u₀ : Point F (4 * m)) (s : F)
    (S : Finset (Point F (4 * m))) : POVM (LinePoly F (m * d + 1)) ((dA × Anc F m) × (F × F)) :=
  POVM.avgOn S (fun raw => padLinePOVM hm4 ty (presOf hm ty .X) (presOf hm ty .Z) hM ⟨u₀, s, raw⟩) 0

theorem lineMeas_mats (ty : CL.Ty) {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u₀ : Point F (4 * m)) (s : F)
    {S : Finset (Point F (4 * m))} (hS : S.Nonempty) (f : LinePoly F (m * d + 1)) :
    ((lineMeas hm hm4 ty hM u₀ s S).mats f).val
      = (S.card : ℝ)⁻¹ • ∑ raw ∈ S,
          padLineMats hm4 ty (presOf hm ty .X) (presOf hm ty .Z) M ⟨u₀, s, raw⟩ f := by
  rw [lineMeas, POVM.avgOn_mats hS]
  rfl

/-- The raw directions a sample with seed `s` can carry so that its diagonal question shows the
truncated direction `v'`. -/
def rawFiber (s : F) (v' : Point F (4 * m)) : Finset (Point F (4 * m)) :=
  univ.filter fun raw => zeroBelow (chi hm4 s) raw = v'

omit [Algebra (ZMod 2) F] in
theorem mem_rawFiber {s : F} {v' raw : Point F (4 * m)} :
    raw ∈ rawFiber hm4 s v' ↔ zeroBelow (chi hm4 s) raw = v' := by
  rw [rawFiber, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-! ## The questions of a sample -/

/-- The direction of the line of type `ty` a seed and raw direction describe; `0` for the point
type. -/
def lineDir (ty : CL.Ty) (s : F) (raw : Point F (4 * m)) : Point F (4 * m) :=
  match ty with
  | .point => 0
  | .aline => Pi.single (chi hm4 s) 1
  | .dline => zeroBelow (chi hm4 s) raw

omit [DecidableEq F] [Algebra (ZMod 2) F] in
theorem LPData.dir_eq_lineDir (ty : CL.Ty) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) :
    (⟨u, s, raw⟩ : LPData F (4 * m)).dir hm4 ty = lineDir hm4 ty s raw := by
  cases ty <;> rfl

/-- The raw directions the strategy averages over at the line question of type `ty` a sample with
seed `s` and raw direction `raw` generates: all of them for an axis-parallel line, the fibre of
the truncated direction for a diagonal one. -/
def rawSet (ty : CL.Ty) (s : F) (raw : Point F (4 * m)) : Finset (Point F (4 * m)) :=
  match ty with
  | .dline => rawFiber hm4 s (zeroBelow (chi hm4 s) raw)
  | _ => univ

omit [Algebra (ZMod 2) F] in
theorem rawSet_nonempty (ty : CL.Ty) (s : F) (raw : Point F (4 * m)) :
    (rawSet hm4 ty s raw).Nonempty := by
  cases ty
  · exact ⟨raw, mem_univ _⟩
  · exact ⟨raw, mem_univ _⟩
  · exact ⟨raw, (mem_rawFiber hm4).mpr rfl⟩

omit [Algebra (ZMod 2) F] in
/-- Every raw direction the strategy averages over describes the sample's line. -/
theorem lineDir_of_mem_rawSet (ty : CL.Ty) {s : F} {raw raw' : Point F (4 * m)}
    (h : raw' ∈ rawSet hm4 ty s raw) : lineDir hm4 ty s raw' = lineDir hm4 ty s raw := by
  cases ty
  · rfl
  · rfl
  · exact (mem_rawFiber hm4).mp h

/-- The line question of type `ty` the sample `(u, s, raw)` generates, as the seeded test
computes it. -/
def lineQ (ty : CL.Ty) (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) :
    CL.Question F (4 * m) :=
  (⟨ty, ty, u, s, raw⟩ : CL.Sample F (4 * m)).question hm4 ty

omit [DecidableEq F] [Algebra (ZMod 2) F] in
theorem lineQ_point (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) :
    lineQ hm4 .point u s raw = .point u := rfl

omit [DecidableEq F] [Algebra (ZMod 2) F] in
theorem lineQ_aline (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) :
    lineQ hm4 .aline u s raw = .aline (CL.rep (lineDir hm4 .aline s raw) u) s := rfl

omit [DecidableEq F] [Algebra (ZMod 2) F] in
theorem lineQ_dline (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) :
    lineQ hm4 .dline u s raw
      = .dline (CL.rep (lineDir hm4 .dline s raw) u) s (lineDir hm4 .dline s raw) := rfl

/-- The parameter of the sample's point on the line it generates. -/
def lineTau (ty : CL.Ty) (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) : F :=
  CL.lineParam (CL.rep (lineDir hm4 ty s raw) u) (lineDir hm4 ty s raw) u

/-- **The strategy's line data, moved to the sample's point along the line, is the sample's own
data**, for every raw direction the strategy averages over. -/
theorem padShift_lineData (ty : CL.Ty) (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m))
    {raw' : Point F (4 * m)} (h : raw' ∈ rawSet hm4 ty s raw) :
    padShift hm4 ty (lineTau hm4 ty u s raw) ⟨CL.rep (lineDir hm4 ty s raw) u, s, raw'⟩
      = ⟨u, s, raw'⟩ := by
  rw [padShift, LPData.dir_eq_lineDir, lineDir_of_mem_rawSet hm4 ty h]
  show (⟨CL.rep (lineDir hm4 ty s raw) u + lineTau hm4 ty u s raw • lineDir hm4 ty s raw, s,
    raw'⟩ : LPData F (4 * m)) = ⟨u, s, raw'⟩
  rw [lineTau, rep_add_lineParam_smul]

/-! ## The strategy -/

/-- The answer a padded line outcome is read as, at an axis-parallel line question: the polynomial
resized to degree `d`. On the support of a legally supported strategy this loses nothing
(`padLineMats_aline_eq_zero_of_not_degLE`). -/
def alineAns (f : LinePoly F (m * d + 1)) : CL.Answer F (4 * m) d 1 :=
  .apolys fun _ => padLine d f

/-- The answer a padded line outcome is read as, at a diagonal line question: the polynomial
resized to degree `4 m d`, which loses nothing since `m d + 1 ≤ 4 m d`. -/
def dlineAns (f : LinePoly F (m * d + 1)) : CL.Answer F (4 * m) d 1 :=
  .dpolys fun _ => padLine (4 * m * d) f

/-- The answer map of a line type. -/
def lineAns (ty : CL.Ty) (f : LinePoly F (m * d + 1)) : CL.Answer F (4 * m) d 1 :=
  match ty with
  | .dline => dlineAns f
  | _ => alineAns f

/-- The value a line answer takes at the parameter `t`; a point answer reads as `0`. -/
def rdEval (t : F) : CL.Answer F (4 * m) d 1 → F
  | .apolys p => (p 0).eval t
  | .dpolys p => (p 0).eval t
  | _ => 0

/-- **The padded strategy** of one player, as a family of POVMs indexed by the seeded test's
questions at `(q, 4m, d, 1)`. -/
def padStrat {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) :
    CL.Question F (4 * m) → POVM (CL.Answer F (4 * m) d 1) ((dA × Anc F m) × (F × F))
  | .point u => (padPt hM u).map fun a => .values fun _ => a
  | .aline u₀ s => (lineMeas hm hm4 .aline hM u₀ s univ).map (lineAns .aline)
  | .dline u₀ s v' => (lineMeas hm hm4 .dline hM u₀ s (rawFiber hm4 s v')).map (lineAns .dline)

theorem padStrat_point {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) :
    padStrat hm hm4 hM (.point u) = (padPt hM u).map fun a => .values fun _ => a := rfl

theorem padStrat_lineQ (ty : CL.Ty) (hty : ty ≠ .point) {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) :
    padStrat hm hm4 hM (lineQ hm4 ty u s raw)
      = (lineMeas hm hm4 ty hM (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw)).map
          (lineAns ty) := by
  cases ty
  · exact absurd rfl hty
  · rfl
  · rfl

/-! ## The support of the strategy's answers -/

theorem exists_of_padStrat_point_mats_ne_zero {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m))
    {a : CL.Answer F (4 * m) d 1} (h : ((padStrat hm hm4 hM (.point u)).mats a).val ≠ 0) :
    ∃ c : F, a = .values fun _ => c := by
  by_contra hne
  exact h (POVM.map_mats_eq_zero_of_forall_ne _ _ fun c hc => hne ⟨c, hc.symm⟩)

theorem exists_of_padStrat_lineQ_mats_ne_zero (ty : CL.Ty) (hty : ty ≠ .point)
    {M : Question F m → POVM (Answer F m d) dA} (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) {a : CL.Answer F (4 * m) d 1}
    (h : ((padStrat hm hm4 hM (lineQ hm4 ty u s raw)).mats a).val ≠ 0) :
    ∃ f, a = lineAns ty f := by
  rw [padStrat_lineQ hm hm4 ty hty] at h
  by_contra hne
  exact h (POVM.map_mats_eq_zero_of_forall_ne _ _ fun f hf => hne ⟨f, hf.symm⟩)

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- Resizing to the degree bound a polynomial already satisfies does not change its values. -/
theorem eval_padLine_of_degLE {k n : ℕ} {f : LinePoly F k} (hf : DegLE f n) (t : F) :
    (padLine n f).eval t = f.eval t := by
  classical
  have hterm : ∀ j : ℕ, (if h : j < n + 1 then (padLine n f) ⟨j, h⟩ else 0)
      = (if h : j < k + 1 then f ⟨j, h⟩ else 0) := by
    intro j
    by_cases hn : j < n + 1
    · rw [dif_pos hn]
      rfl
    · rw [dif_neg hn]
      by_cases hk : j < k + 1
      · rw [dif_pos hk]
        exact (hf ⟨j, hk⟩ (by simpa using not_lt.mp hn)).symm
      · rw [dif_neg hk]
  have hzero : ∀ j, ¬ j < n + 1 →
      (if h : j < k + 1 then f ⟨j, h⟩ else 0) * t ^ j = 0 := by
    intro j hn
    by_cases hk : j < k + 1
    · rw [dif_pos hk, hf ⟨j, hk⟩ (by simpa using not_lt.mp hn), zero_mul]
    · rw [dif_neg hk, zero_mul]
  have hzero' : ∀ j, ¬ j < k + 1 →
      (if h : j < k + 1 then f ⟨j, h⟩ else 0) * t ^ j = 0 := by
    intro j hk
    rw [dif_neg hk, zero_mul]
  rw [linePoly_eval_eq_range, linePoly_eval_eq_range]
  simp only [hterm]
  rw [Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left (n + 1) (k + 1)))
      fun j _ hj => hzero j (by simpa using hj),
    Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right (n + 1) (k + 1)))
      fun j _ hj => hzero' j (by simpa using hj)]

/-- On an axis-parallel line, the strategy's line measurement has no element off `DegLE _ d`. -/
theorem lineMeas_aline_mats_eq_zero_of_not_degLE (hd : 1 ≤ d)
    {M : Question F m → POVM (Answer F m d) dA} (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (hleg : LegalSupport M) (u₀ : Point F (4 * m)) (s : F) (S : Finset (Point F (4 * m)))
    {f : LinePoly F (m * d + 1)} (hf : ¬ DegLE f d) :
    ((lineMeas hm hm4 .aline hM u₀ s S).mats f).val = 0 := by
  by_cases hS : S.Nonempty
  · rw [lineMeas_mats hm hm4 .aline hM u₀ s hS, Finset.sum_eq_zero, smul_zero]
    intro raw _
    exact padLineMats_aline_eq_zero_of_not_degLE hm4 hd hleg _ hf
  · rw [lineMeas, POVM.avgOn, dif_neg hS]
    show (if f = 0 then (1 : Matrix _ _ ℂ) else 0) = 0
    rw [if_neg]
    rintro rfl
    exact hf degLE_zero

/-- **Reading the strategy's line answer at a parameter is reading the line measurement there**:
the resizing in `lineAns` is invisible on the support. -/
theorem padStrat_lineQ_map_rdEval (ty : CL.Ty) (hty : ty ≠ .point) (hd : 1 ≤ d)
    {M : Question F m → POVM (Answer F m d) dA} (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (hleg : LegalSupport M) (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) (t : F) :
    (padStrat hm hm4 hM (lineQ hm4 ty u s raw)).map (rdEval t)
      = (lineMeas hm hm4 ty hM (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw)).map
          fun f => LinePoly.eval f t := by
  rw [padStrat_lineQ hm hm4 ty hty, POVM.map_map]
  cases ty
  · exact absurd rfl hty
  · refine POVM.map_congr_of_support _ fun f hf => ?_
    have hdeg : DegLE f d := by
      by_contra h
      exact hf (lineMeas_aline_mats_eq_zero_of_not_degLE hm hm4 hd hM hleg _ _ _ h)
    exact eval_padLine_of_degLE hdeg t
  · refine POVM.map_congr_of_support _ fun f _ => ?_
    show (padLine (4 * m * d) f).eval t = f.eval t
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact eval_padLine (by nlinarith) f t

/-- The strategy's point answer, read back as a field element, is the padded point measurement. -/
theorem padStrat_point_map_toValue {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) :
    (padStrat hm hm4 hM (.point u)).map CL.Answer.toValue = padPt hM u := by
  rw [padStrat_point, POVM.map_map]
  exact POVM.map_id _

/-! ## The line measurement read at the sampled point

`sum_filter_padLineMats` reads the padded line measurement at the parameter of a point of the
padded line as the pasted line measurement, at the data's *own* point, coarse-grained by the
combining map at the *shifted* point. The strategy's line data carries the canonical base point of
the line, while `lem:qld-padded-lines` is stated at the sample's point; the two are reconciled by
the invariance of the pasted line measurement under moving the padded point along the padded
line, which holds because each block of the padded point either moves along its own subline or
does not move at all (`xBlk_dir_sub`, `zBlk_dir_sub`). -/

section ShiftInvariance

variable {dB : Type} [Fintype dB] [DecidableEq dB] {M : Question F m → POVM (Answer F m d) dB}

/-- The `X` line measurement of the pair of sublines is unchanged by the padded shift. -/
theorem lineMats_pairCX_padShift (ty : CL.Ty) (PX : LinePres F m hm .X) (hfacX : FactorsX PX)
    (hdirX : ∀ (D : LPData F m) (u : Point F m), PX.dir (ofLPX D u) = D.dir hm ty) (tau : F)
    (P : LPData F (4 * m)) (e : SubRand F m) :
    PX.lineMats d M (pairCX (subPair hm4 hm ty (padShift hm4 ty tau P) e))
      = PX.lineMats d M (pairCX (subPair hm4 hm ty P e)) := by
  have hL : PX.lineMats d M (pairCX (subPair hm4 hm ty (padShift hm4 ty tau P) e))
      = PX.lineMats d M (ofLPX (subX hm4 hm (padShift hm4 ty tau P) e.1)
          (subZ hm4 hm ty P e.2).pt) :=
    lineMats_ofLPX hfacX (ofLPX (subX hm4 hm (padShift hm4 ty tau P) e.1)
      (subZ hm4 hm ty P e.2).pt) (subZ hm4 hm ty (padShift hm4 ty tau P) e.2).pt
  rw [hL, subX_padShift]
  show PX.lineMats d M (ofLPX ⟨xBlk (padShift hm4 ty tau P).pt, (subX hm4 hm P e.1).s,
    (subX hm4 hm P e.1).raw⟩ (subZ hm4 hm ty P e.2).pt)
    = PX.lineMats d M (ofLPX (subX hm4 hm P e.1) (subZ hm4 hm ty P e.2).pt)
  rcases xBlk_dir_sub hm4 hm ty P e.1 with h | h
  · have hc : ofLPX (⟨xBlk (padShift hm4 ty tau P).pt, (subX hm4 hm P e.1).s,
        (subX hm4 hm P e.1).raw⟩ : LPData F m) (subZ hm4 hm ty P e.2).pt
        = Content.shiftAlong .X PX.dir tau (ofLPX (subX hm4 hm P e.1) (subZ hm4 hm ty P e.2).pt) :=
            by
      rw [Content.shiftAlong_eq, hdirX]
      show (⟨xBlk (padShift hm4 ty tau P).pt, _, _, _, 0, 0⟩ : Content F m)
        = ⟨(subX hm4 hm P e.1).pt + tau • (subX hm4 hm P e.1).dir hm ty, _, _, _, 0, 0⟩
      rw [padShift_pt, xBlk_add_smul, h, subX_pt]
      rfl
    rw [hc, LinePres.lineMats_shiftAlong]
  · have hpt : xBlk (padShift hm4 ty tau P).pt = (subX hm4 hm P e.1).pt := by
      rw [padShift_pt, xBlk_add_smul, h, smul_zero, add_zero, subX_pt]
    rw [hpt]

/-- The `Z` line measurement of the pair of sublines is unchanged by the padded shift. -/
theorem lineMats_pairCZ_padShift (ty : CL.Ty) (PZ : LinePres F m hm .Z) (hfacZ : FactorsZ PZ)
    (hdirZ : ∀ (D : LPData F m) (u : Point F m), PZ.dir (ofLPZ D u) = D.dir hm ty) (tau : F)
    (P : LPData F (4 * m)) (e : SubRand F m) :
    PZ.lineMats d M (pairCZ (subPair hm4 hm ty (padShift hm4 ty tau P) e))
      = PZ.lineMats d M (pairCZ (subPair hm4 hm ty P e)) := by
  have hL : PZ.lineMats d M (pairCZ (subPair hm4 hm ty (padShift hm4 ty tau P) e))
      = PZ.lineMats d M (ofLPZ (subZ hm4 hm ty (padShift hm4 ty tau P) e.2)
          (subX hm4 hm P e.1).pt) :=
    lineMats_ofLPZ hfacZ (ofLPZ (subZ hm4 hm ty (padShift hm4 ty tau P) e.2)
      (subX hm4 hm P e.1).pt) (subX hm4 hm (padShift hm4 ty tau P) e.1).pt
  rw [hL, subZ_padShift]
  show PZ.lineMats d M (ofLPZ ⟨zBlk (padShift hm4 ty tau P).pt, (subZ hm4 hm ty P e.2).s,
    (subZ hm4 hm ty P e.2).raw⟩ (subX hm4 hm P e.1).pt)
    = PZ.lineMats d M (ofLPZ (subZ hm4 hm ty P e.2) (subX hm4 hm P e.1).pt)
  rcases zBlk_dir_sub hm4 hm ty P e.2 with h | h
  · have hc : ofLPZ (⟨zBlk (padShift hm4 ty tau P).pt, (subZ hm4 hm ty P e.2).s,
        (subZ hm4 hm ty P e.2).raw⟩ : LPData F m) (subX hm4 hm P e.1).pt
        = Content.shiftAlong .Z PZ.dir tau (ofLPZ (subZ hm4 hm ty P e.2) (subX hm4 hm P e.1).pt) :=
            by
      rw [Content.shiftAlong_eq, hdirZ]
      show (⟨_, zBlk (padShift hm4 ty tau P).pt, _, _, 0, 0⟩ : Content F m)
        = ⟨_, (subZ hm4 hm ty P e.2).pt + tau • (subZ hm4 hm ty P e.2).dir hm ty, _, _, 0, 0⟩
      rw [padShift_pt, zBlk_add_smul, h, subZ_pt]
      rfl
    rw [hc, LinePres.lineMats_shiftAlong]
  · have hpt : zBlk (padShift hm4 ty tau P).pt = (subZ hm4 hm ty P e.2).pt := by
      rw [padShift_pt, zBlk_add_smul, h, smul_zero, add_zero, subZ_pt]
    rw [hpt]

/-- **The pasted line measurement is unchanged by moving the padded point along the padded
line.** -/
theorem pasteLine_subPair_padShift (ty : CL.Ty) (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    (hfacX : FactorsX PX) (hfacZ : FactorsZ PZ)
    (hdirX : ∀ (D : LPData F m) (u : Point F m), PX.dir (ofLPX D u) = D.dir hm ty)
    (hdirZ : ∀ (D : LPData F m) (u : Point F m), PZ.dir (ofLPZ D u) = D.dir hm ty) (tau : F)
    (P : LPData F (4 * m)) (e : SubRand F m) (q : LinePoly F (m * d) × LinePoly F (m * d)) :
    pasteLine PX PZ d M (pairCX (subPair hm4 hm ty (padShift hm4 ty tau P) e))
        (pairCZ (subPair hm4 hm ty (padShift hm4 ty tau P) e)) q
      = pasteLine PX PZ d M (pairCX (subPair hm4 hm ty P e)) (pairCZ (subPair hm4 hm ty P e)) q :=
          by
  rw [pasteLine, pasteLine, lineMats_pairCX_padShift hm hm4 ty PX hfacX hdirX,
    lineMats_pairCZ_padShift hm hm4 ty PZ hfacZ hdirZ]

/-- **The padded line measurement read at the parameter of a point of the padded line is the
average over the fresh randomness of the pasted line measurement at that point, coarse-grained by
the combining map there.** -/
theorem sum_filter_padLineMats_eq_lineComb (ty : CL.Ty) (PX : LinePres F m hm .X)
    (PZ : LinePres F m hm .Z) (hfacX : FactorsX PX) (hfacZ : FactorsZ PZ)
    (hbaseX : ∀ c : Content F m, PX.base c = CL.rep (PX.dir c) (c.pt .X))
    (hdirX : ∀ (D : LPData F m) (u : Point F m), PX.dir (ofLPX D u) = D.dir hm ty)
    (hbaseZ : ∀ c : Content F m, PZ.base c = CL.rep (PZ.dir c) (c.pt .Z))
    (hdirZ : ∀ (D : LPData F m) (u : Point F m), PZ.dir (ofLPZ D u) = D.dir hm ty)
    (P : LPData F (4 * m)) (tau a : F) :
    ∑ f ∈ univ.filter fun f : LinePoly F (m * d + 1) => LinePoly.eval f tau = a,
        padLineMats hm4 ty PX PZ M P f
      = ((Fintype.card (SubRand F m) : ℝ))⁻¹ • ∑ e : SubRand F m,
          lineComb PX PZ d M (pairCX (subPair hm4 hm ty (padShift hm4 ty tau P) e))
            (pairCZ (subPair hm4 hm ty (padShift hm4 ty tau P) e))
            (alph (padShift hm4 ty tau P).pt) (bet (padShift hm4 ty tau P).pt) a := by
  rw [sum_filter_padLineMats hm4 ty PX PZ hbaseX hdirX hbaseZ hdirZ P tau a]
  refine congrArg _ (Finset.sum_congr rfl fun e _ => ?_)
  rw [lineComb]
  exact Finset.sum_congr rfl fun q _ =>
    (pasteLine_subPair_padShift hm hm4 ty PX PZ hfacX hfacZ hdirX hdirZ tau P e q).symm

end ShiftInvariance

/-- **The strategy's line measurement, read at the parameter of the sample's point, is the
average over the raw directions and the fresh randomness of the pasted line measurement at the
sample's own data, coarse-grained by the combining map at the sample's point.** This is the
quantity `lem:qld-padded-lines` controls. -/
theorem lineMeas_map_eval_mats (ty : CL.Ty) (hty : ty ≠ .point)
    {M : Question F m → POVM (Answer F m d) dA} (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) (a : F) :
    (((lineMeas hm hm4 ty hM (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw)).map
        fun f => LinePoly.eval f (lineTau hm4 ty u s raw)).mats a).val
      = ((rawSet hm4 ty s raw).card : ℝ)⁻¹ • ∑ raw' ∈ rawSet hm4 ty s raw,
          ((Fintype.card (SubRand F m) : ℝ))⁻¹ • ∑ e : SubRand F m,
            lineComb (presOf hm ty .X) (presOf hm ty .Z) d M
              (pairCX (subPair hm4 hm ty ⟨u, s, raw'⟩ e)) (pairCZ (subPair hm4 hm ty ⟨u, s, raw'⟩
                  e))
              (alph u) (bet u) a := by
  rw [POVM.map_mats]
  simp only [lineMeas_mats hm hm4 ty hM _ s (rawSet_nonempty hm4 ty s raw)]
  rw [← Finset.smul_sum, Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun raw' hraw' => ?_)
  rw [sum_filter_padLineMats_eq_lineComb hm hm4 ty _ _ (factorsX_presOf hm ty) (factorsZ_presOf hm
      ty)
    (presOf_base_eq hm ty .X) (presOf_dir_ofLPX hm ty hty) (presOf_base_eq hm ty .Z)
    (presOf_dir_ofLPZ hm ty hty) ⟨_, s, raw'⟩ _ a, padShift_lineData hm4 ty u s raw hraw']

/-! ## The conditional failures of the strategy, question pair by question pair -/

section Fail

variable {dB : Type} [Fintype dB] [DecidableEq dB]
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  (hMA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
  (hMB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
  (Ψ : ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ)

/-- A line answer read at the parameter of the sampled point, against the point answer there: the
decider accepts. -/
theorem accepts_lineQ_point (ty : CL.Ty) (hty : ty ≠ .point) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) (f : LinePoly F (m * d + 1)) (c : F)
    (h : rdEval (lineTau hm4 ty u s raw) (lineAns ty f) = c) :
    CL.accepts hm4 (lineQ hm4 ty u s raw) (.point u) (lineAns ty f) (CL.Answer.values fun _ => c) =
    true := by
  have hon : ∃ t, u = CL.rep (lineDir hm4 ty s raw) u + t • lineDir hm4 ty s raw :=
    ⟨lineTau hm4 ty u s raw, (rep_add_lineParam_smul _ u).symm⟩
  cases ty
  · exact absurd rfl hty
  · simp only [lineQ_aline, lineAns, alineAns, CL.accepts, CL.Question.fmtOk, CL.subtests,
      Bool.true_and, CL.lineVsPoint, decide_eq_true_eq]
    exact ⟨hon, fun _ => h⟩
  · simp only [lineQ_dline, lineAns, dlineAns, CL.accepts, CL.Question.fmtOk, CL.subtests,
      Bool.true_and, CL.lineVsPoint, decide_eq_true_eq]
    exact ⟨hon, fun _ => h⟩

/-- The same with the players exchanged. -/
theorem accepts_point_lineQ (ty : CL.Ty) (hty : ty ≠ .point) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) (f : LinePoly F (m * d + 1)) (c : F)
    (h : c = rdEval (lineTau hm4 ty u s raw) (lineAns ty f)) :
    CL.accepts hm4 (.point u) (lineQ hm4 ty u s raw) (CL.Answer.values fun _ => c) (lineAns ty f) =
    true := by
  have hon : ∃ t, u = CL.rep (lineDir hm4 ty s raw) u + t • lineDir hm4 ty s raw :=
    ⟨lineTau hm4 ty u s raw, (rep_add_lineParam_smul _ u).symm⟩
  cases ty
  · exact absurd rfl hty
  · simp only [lineQ_aline, lineAns, alineAns, CL.accepts, CL.Question.fmtOk, CL.subtests,
      Bool.true_and, CL.lineVsPoint, decide_eq_true_eq]
    exact ⟨hon, fun _ => h.symm⟩
  · simp only [lineQ_dline, lineAns, dlineAns, CL.accepts, CL.Question.fmtOk, CL.subtests,
      Bool.true_and, CL.lineVsPoint, decide_eq_true_eq]
    exact ⟨hon, fun _ => h.symm⟩

omit [Algebra (ZMod 2) F] in
theorem accepts_point_self (u : Point F (4 * m)) (a : Fin 1 → F) :
    CL.accepts (d := d) hm4 (.point u) (.point u) (CL.Answer.values a) (CL.Answer.values a)
      = true := by
  simp [CL.accepts, CL.Question.fmtOk, CL.subtests]

omit [Algebra (ZMod 2) F] in
theorem accepts_lineQ_lineQ_self (ty : CL.Ty) (hty : ty ≠ .point) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) (f : LinePoly F (m * d + 1)) :
    CL.accepts hm4 (lineQ hm4 ty u s raw) (lineQ hm4 ty u s raw) (lineAns ty f) (lineAns ty f)
      = true := by
  cases ty
  · exact absurd rfl hty
  · simp [lineQ_aline, lineAns, alineAns, CL.accepts, CL.Question.fmtOk, CL.subtests]
  · simp [lineQ_dline, lineAns, dlineAns, CL.accepts, CL.Question.fmtOk, CL.subtests]

/-- **Alice's line against Bob's point**: the conditional failure is at most the disagreement of
Alice's line measurement read at the sample's point with Bob's padded point measurement. -/
theorem condFail_lineQ_point_le (ty : CL.Ty) (hty : ty ≠ .point) (hd : 1 ≤ d)
    (hlegA : LegalSupport MA) (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) :
    condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hMA) (padStrat hm hm4 hMB)
        (lineQ hm4 ty u s raw) (.point u)
      ≤ 1 - ∑ a, bornProb Ψ
          ((((lineMeas hm hm4 ty hMA (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw)).map
            fun f => LinePoly.eval f (lineTau hm4 ty u s raw)).mats a).val)
          (((padPt hMB u).mats a).val) := by
  rw [← padStrat_lineQ_map_rdEval hm hm4 ty hty hd hMA hlegA u s raw,
    ← padStrat_point_map_toValue hm hm4 hMB u]
  refine condFail_le_one_sub_sum_bornProb_map _ _ fun a b ha hb hab => ?_
  obtain ⟨f, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 ty hty hMA u s raw ha
  obtain ⟨c, rfl⟩ := exists_of_padStrat_point_mats_ne_zero hm hm4 hMB u hb
  exact accepts_lineQ_point hm4 ty hty u s raw f c hab

/-- **Alice's point against Bob's line.** -/
theorem condFail_point_lineQ_le (ty : CL.Ty) (hty : ty ≠ .point) (hd : 1 ≤ d)
    (hlegB : LegalSupport MB) (u : Point F (4 * m)) (s : F) (raw : Point F (4 * m)) :
    condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hMA) (padStrat hm hm4 hMB)
        (.point u) (lineQ hm4 ty u s raw)
      ≤ 1 - ∑ a, bornProb Ψ (((padPt hMA u).mats a).val)
          ((((lineMeas hm hm4 ty hMB (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw)).map
            fun f => LinePoly.eval f (lineTau hm4 ty u s raw)).mats a).val) := by
  rw [← padStrat_lineQ_map_rdEval hm hm4 ty hty hd hMB hlegB u s raw,
    ← padStrat_point_map_toValue hm hm4 hMA u]
  refine condFail_le_one_sub_sum_bornProb_map _ _ fun a b ha hb hab => ?_
  obtain ⟨c, rfl⟩ := exists_of_padStrat_point_mats_ne_zero hm hm4 hMA u ha
  obtain ⟨f, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 ty hty hMB u s raw hb
  exact accepts_point_lineQ hm4 ty hty u s raw f c hab

/-- **Identical points**: the conditional failure is at most the disagreement of the two padded
point measurements. -/
theorem condFail_point_point_le (u : Point F (4 * m)) :
    condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hMA) (padStrat hm hm4 hMB)
        (.point u) (.point u)
      ≤ 1 - ∑ a, bornProb Ψ (((padPt hMA u).mats a).val) (((padPt hMB u).mats a).val) := by
  rw [← padStrat_point_map_toValue hm hm4 hMA u, ← padStrat_point_map_toValue hm hm4 hMB u]
  refine condFail_le_one_sub_sum_bornProb_map _ _ fun a b ha hb hab => ?_
  obtain ⟨c, rfl⟩ := exists_of_padStrat_point_mats_ne_zero hm hm4 hMA u ha
  obtain ⟨c', rfl⟩ := exists_of_padStrat_point_mats_ne_zero hm hm4 hMB u hb
  have hc : c = c' := hab
  subst hc
  exact accepts_point_self (d := d) hm4 u _

/-- **Identical lines**: the conditional failure is at most the disagreement of the two line
measurements, outcome polynomial by outcome polynomial. -/
theorem condFail_lineQ_lineQ_le (ty : CL.Ty) (hty : ty ≠ .point) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) :
    condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hMA) (padStrat hm hm4 hMB)
        (lineQ hm4 ty u s raw) (lineQ hm4 ty u s raw)
      ≤ 1 - ∑ f, bornProb Ψ
          (((lineMeas hm hm4 ty hMA (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw)).mats
            f).val)
          (((lineMeas hm hm4 ty hMB (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw)).mats
            f).val) := by
  refine le_trans (condFail_le_one_sub_sum_bornProb_diag fun a ha _ => ?_) ?_
  · obtain ⟨f, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 ty hty hMA u s raw ha
    exact accepts_lineQ_lineQ_self hm4 ty hty u s raw f
  · rw [padStrat_lineQ hm hm4 ty hty hMA, padStrat_lineQ hm hm4 ty hty hMB]
    have := sum_bornProb_le_map Ψ
      (lineMeas hm hm4 ty hMA (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw))
      (lineMeas hm hm4 ty hMB (CL.rep (lineDir hm4 ty s raw) u) s (rawSet hm4 ty s raw))
      (lineAns ty)
    linarith

/-- **The two cross type pairs are always accepted**: the strategy answers in the right format, and
the decider checks nothing else. -/
theorem condFail_aline_dline_le (hΨ : star Ψ ⬝ᵥ Ψ = 1) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) (u' : Point F (4 * m)) (s' : F) (raw' : Point F (4 * m)) :
    condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hMA) (padStrat hm hm4 hMB)
        (lineQ hm4 .aline u s raw) (lineQ hm4 .dline u' s' raw') ≤ 0 := by
  refine le_trans (condFail_le_one_sub_sum_bornProb_map (fun _ => ()) (fun _ => ())
    fun a b ha hb _ => ?_) ?_
  · obtain ⟨f, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 .aline (by decide) hMA u s raw
      ha
    obtain ⟨g, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 .dline (by decide) hMB u' s'
        raw' hb
    rfl
  · rw [Fintype.sum_unique, POVM.map_const_mats, POVM.map_const_mats, bornProb_one_one hΨ]
    norm_num

theorem condFail_dline_aline_le (hΨ : star Ψ ⬝ᵥ Ψ = 1) (u : Point F (4 * m)) (s : F)
    (raw : Point F (4 * m)) (u' : Point F (4 * m)) (s' : F) (raw' : Point F (4 * m)) :
    condFail (clGame (d := d) (ldc := 1) hm4) Ψ (padStrat hm hm4 hMA) (padStrat hm hm4 hMB)
        (lineQ hm4 .dline u s raw) (lineQ hm4 .aline u' s' raw') ≤ 0 := by
  refine le_trans (condFail_le_one_sub_sum_bornProb_map (fun _ => ()) (fun _ => ())
    fun a b ha hb _ => ?_) ?_
  · obtain ⟨f, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 .dline (by decide) hMA u s raw
      ha
    obtain ⟨g, rfl⟩ := exists_of_padStrat_lineQ_mats_ne_zero hm hm4 .aline (by decide) hMB u' s'
        raw' hb
    rfl
  · rw [Fintype.sum_unique, POVM.map_const_mats, POVM.map_const_mats, bornProb_one_one hΨ]
    norm_num

end Fail

/-! ## Polynomial separation

Two distinct line polynomials of degree at most `n` agree at at most `n` parameters
(`card_agree_linePoly_le`), so the disagreement of two polynomial-valued measurements is at most
their disagreement when both are read at a uniformly random parameter, plus `n / q`. This is the
paper's argument for the identical-line subtest. -/

section Separation

variable {dA' dB' : Type*} [Fintype dA'] [DecidableEq dA'] [Fintype dB'] [DecidableEq dB']

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **Polynomial separation.** -/
theorem one_sub_sum_bornProb_le_avg_eval {n : ℕ} {ψ : dA' × dB' → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (LA : POVM (LinePoly F n) dA') (LB : POVM (LinePoly F n) dB') :
    1 - ∑ f, bornProb ψ ((LA.mats f).val) ((LB.mats f).val)
      ≤ (Fintype.card F : ℝ)⁻¹ * ∑ t : F, (1 - ∑ a : F,
          bornProb ψ (((LA.map fun f => LinePoly.eval f t).mats a).val)
            (((LB.map fun f => LinePoly.eval f t).mats a).val))
        + (n : ℝ) / Fintype.card F := by
  classical
  have hq : (0 : ℝ) < Fintype.card F := Nat.cast_pos.mpr Fintype.card_pos
  set b : LinePoly F n → LinePoly F n → ℝ := fun f g =>
    bornProb ψ ((LA.mats f).val) ((LB.mats g).val) with hb
  have hb0 : ∀ f g, 0 ≤ b f g := fun f g =>
    bornProb_nonneg ψ (LA.posSemidef f) (LB.posSemidef g)
  have hb1 : ∑ f, ∑ g, b f g = 1 := sum_bornProb hψ LA LB
  -- the per-parameter identity
  have hsplit : ∀ t : F, ∑ a : F,
      bornProb ψ (((LA.map fun f => LinePoly.eval f t).mats a).val)
        (((LB.map fun f => LinePoly.eval f t).mats a).val)
      = ∑ f, b f f + ∑ f, ∑ g,
          (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g := by
    intro t
    rw [sum_bornProb_map', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hterm : ∀ g, (if LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g
        = (if f = g then (1 : ℝ) else 0) * b f g
          + (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g := by
      intro g
      by_cases hfg : f = g
      · subst hfg
        simp
      · simp [hfg]
    rw [Finset.sum_congr rfl fun g _ => hterm g, Finset.sum_add_distrib]
    congr 1
    simp [Finset.sum_ite_eq]
  -- the collision count
  have hcoll : ∀ f g : LinePoly F n,
      ∑ t : F, (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) ≤ n := by
    intro f g
    by_cases hfg : f = g
    · simp [hfg]
    · rw [Finset.sum_boole]
      have h1 : (univ.filter fun t : F => f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t)
          = univ.filter fun t : F => LinePoly.eval f t = LinePoly.eval g t :=
        Finset.filter_congr fun t _ => ⟨fun h => h.2, fun h => ⟨hfg, h⟩⟩
      rw [h1]
      exact_mod_cast card_agree_linePoly_le hfg
  have hrest : ∑ t : F, ∑ f, ∑ g,
      (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g ≤ n := by
    rw [Finset.sum_comm]
    calc ∑ f, ∑ t : F, ∑ g,
          (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g
        = ∑ f, ∑ g, (∑ t : F,
            (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0)) * b f g := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun g _ => (Finset.sum_mul _ _ _).symm
      _ ≤ ∑ f, ∑ g, (n : ℝ) * b f g :=
          Finset.sum_le_sum fun f _ => Finset.sum_le_sum fun g _ =>
            mul_le_mul_of_nonneg_right (hcoll f g) (hb0 f g)
      _ = n := by
          simp only [← Finset.mul_sum]
          rw [hb1, mul_one]
  have hsum : (Fintype.card F : ℝ) * (1 - ∑ f, b f f)
      = ∑ t : F, (1 - ∑ a : F,
          bornProb ψ (((LA.map fun f => LinePoly.eval f t).mats a).val)
            (((LB.map fun f => LinePoly.eval f t).mats a).val))
        + ∑ t : F, ∑ f, ∑ g,
          (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g := by
    simp only [hsplit]
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun t _ => show (1 - (∑ f, b f f + ∑ f, ∑ g,
        (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g)
        + ∑ f, ∑ g, (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g)
        = 1 - ∑ f, b f f by ring]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmain : 1 - ∑ f, b f f
      = (Fintype.card F : ℝ)⁻¹ * ((∑ t : F, (1 - ∑ a : F,
          bornProb ψ (((LA.map fun f => LinePoly.eval f t).mats a).val)
            (((LB.map fun f => LinePoly.eval f t).mats a).val)))
        + ∑ t : F, ∑ f, ∑ g,
          (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g) := by
    rw [← hsum, inv_mul_cancel_left₀ hq.ne']
  rw [hmain, mul_add]
  have hlast : (Fintype.card F : ℝ)⁻¹ * ∑ t : F, ∑ f, ∑ g,
      (if f ≠ g ∧ LinePoly.eval f t = LinePoly.eval g t then (1 : ℝ) else 0) * b f g
        ≤ (n : ℝ) / Fintype.card F := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hrest (inv_nonneg.mpr hq.le)
  linarith

end Separation

end MIPRE.QLD

end
