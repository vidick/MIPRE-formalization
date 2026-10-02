/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/LdSandwichLineOnePoint/CSSetup.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.OutcomeLemmas

@[expose] public section

/-!
# Section 12 pasting: line one-point transport — Cauchy–Schwarz setup

The setup of the two Cauchy–Schwarz moves of the line one-point transport: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CSSetup.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The linear (pre-`max`) consistency defect `qBipartiteLinearConsDefect` and its expansion against
the complementary right outcome; the source, intermediate and moved outcome sums of
`ld-pasting.tex` lines 960--1010; the ordered and rotated half-products, which are local, in
`𝔓`, and their left placements `ldSandwichLineOnePointCS_Aord`/`_Arot`, joint, in `K →L[ℂ] K`;
the raw commutation of the half-sandwich reindexed to original outcomes, as an `SDDOpRel` on a
symmetric model; and the fact records the Cauchy–Schwarz step consumes. The vendored conjugate
transpose `ᴴ` is `star`.

The vendored `qBipartiteLinearConsDefect` and its three lemmas
(`qBipartiteLinearConsDefect_option_eq_sum_some_complement`,
`qBipartiteLinearConsDefect_nonneg_of_right_total_one` and
`bipartiteConsError_le_of_linearDefect_average_bound`) allow two tensor factors `ιA`, `ιB`;
here, as for every bipartite quantity of the port ("Same-space and bipartite quantities"), both
factors are `𝔓` in a symmetric model `S`, taken as an explicit first argument. Every vendored
use applies them to `strategy.state` with both families on one carrier
(`LdSandwichLineOnePoint/{Core,CauchySchwarz}.lean`), so the narrowed forms serve them. The
definitions that place without a strategy (`ldSandwichLineOnePointCS_Aord`, `_Arot`, their
adjoint families and the two adjoint raw families) and the two lemmas about them take
`(S : SymModel 𝔓 K)` as an explicit first argument, in place of the vendored named carrier
`(ι₂ := ι)`. No vendored statement here carries a swap or normalization hypothesis.

## Not ported

Nothing: every vendored declaration has a counterpart of the same name.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq Point PointTuple Distribution avgOver avgOver_congr
  uniformDistribution)
open MIPStarRE.LDT.Pasting (GHatTupleOutcome SandwichedLineQuestion commuteGHalfSandwichError
  pointTupleLastFrontEquiv gHatTupleOutcomeLastFrontEquiv pointTupleLastReverseEquiv
  gHatTupleOutcomeLastReverseEquiv sandwichedLineQuestionPrefixFstEquiv)
open MIPRE.LIDT.Co (SymModel SymStrat SubMeas IdxSubMeas OpFamily IdxOpFamily IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The linear (pre-`max`) form of the bipartite consistency defect,
`ev(A_total ⊗ B_total) − Σ_o ev(A_o ⊗ B_o)`. -/
noncomputable def qBipartiteLinearConsDefect {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A B : SubMeas Outcome 𝔓) : ℝ :=
  S.ev (S.opTensor A.total B.total) - S.qBipartiteMatchMass A B

/-- For option-valued families with no `none` mass, the linear bipartite
consistency defect is the paper's sum against the complementary right outcome:
`ev(A_total ⊗ B_total) − Σ_o ev(A_o ⊗ B_o) = Σ_a ev(A_a ⊗ (1 − B_a))` when Bob's family is a
measurement and both `none` outcomes vanish. -/
theorem qBipartiteLinearConsDefect_option_eq_sum_some_complement
    {α : Type*} [Fintype α]
    (S : SymModel 𝔓 K)
    (A B : SubMeas (Option α) 𝔓)
    (hBtotal : B.total = 1)
    (hAnone : A.outcome none = 0) (hBnone : B.outcome none = 0) :
    qBipartiteLinearConsDefect S A B =
      ∑ a : α, S.ev (S.opTensor (A.outcome (some a)) (1 - B.outcome (some a))) := by
  have hterm : ∀ o : Option α,
      S.ev (S.opTensor (A.outcome o) 1) - S.ev (S.opTensor (A.outcome o) (B.outcome o)) =
        S.ev (S.opTensor (A.outcome o) (1 - B.outcome o)) := fun o => by
    rw [← S.ev_sub, SymModel.opTensor, SymModel.opTensor,
      SymModel.opTensor, ← mul_sub, S.rightTensor_sub]
  rw [qBipartiteLinearConsDefect, hBtotal, ← A.sum_eq_total, S.opTensor_sum_left_univ, S.ev_sum,
    SymModel.qBipartiteMatchMass, ← Finset.sum_sub_distrib, Fintype.sum_option]
  simp only [hterm, hAnone, hBnone, SymModel.opTensor, map_zero, zero_mul, S.ev_zero, sub_self, zero_add]

/-- The linear consistency defect is nonnegative when the right-hand family is a
measurement.  This lets the paper's averaged linear estimate feed the `max 0`
`qBipartiteConsDefect` form without a pointwise absolute-value gap. -/
theorem qBipartiteLinearConsDefect_nonneg_of_right_total_one
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A B : SubMeas Outcome 𝔓)
    (hBtotal : B.total = 1) :
    0 ≤ qBipartiteLinearConsDefect S A B := by
  have hmatch_le_left : S.qBipartiteMatchMass A B ≤ S.ev (S.L A.total) :=
    calc
      S.qBipartiteMatchMass A B
          ≤ ∑ a : Outcome, S.ev (S.L (A.outcome a)) :=
            Finset.sum_le_sum fun a _ => S.ev_mono _ _ <|
              S.opTensor_le_leftTensor (A.outcome_pos a) (SubMeas.outcome_le_one B a)
      _ = S.ev (S.L A.total) := by
            rw [← S.ev_sum, S.leftTensor_finset_sum, A.sum_eq_total]
  have hleft_eq : S.ev (S.L A.total) = S.ev (S.opTensor A.total B.total) := by
    rw [hBtotal, SymModel.opTensor, S.rightTensor_one, mul_one]
  rw [qBipartiteLinearConsDefect]
  linarith

/-- If the averaged linear consistency-defect comparison holds and the right
family is measurement-valued, then the averaged `max 0` bipartite consistency
error comparison follows.

This is the paper-faithful formulation of `lem:ld-sandwich-line-one-point`: the
Cauchy–Schwarz argument controls an averaged linear expression, not an average
of pointwise absolute values.  Nonnegativity of the linear defects removes the
outer `max 0`. -/
theorem bipartiteConsError_le_of_linearDefect_average_bound
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A B C : IdxSubMeas Question Outcome 𝔓)
    (η : ℝ)
    (hCtotal : ∀ q, (C q).total = 1)
    (hgap :
      avgOver 𝒟 (fun q => qBipartiteLinearConsDefect S (A q) (C q)) ≤
        avgOver 𝒟 (fun q => qBipartiteLinearConsDefect S (B q) (C q)) + η) :
    S.bipartiteConsError 𝒟 A C ≤ S.bipartiteConsError 𝒟 B C + η := by
  have hmax : ∀ X : IdxSubMeas Question Outcome 𝔓, ∀ q,
      S.qBipartiteConsDefect (X q) (C q) = qBipartiteLinearConsDefect S (X q) (C q) :=
    fun X q => max_eq_right
      (qBipartiteLinearConsDefect_nonneg_of_right_total_one S (X q) (C q) (hCtotal q))
  unfold SymModel.bipartiteConsError
  rw [avgOver_congr 𝒟 _ _ (hmax A), avgOver_congr 𝒟 _ _ (hmax B)]
  exact hgap

/-- The original expanded off-diagonal scalar in `ld-pasting.tex:960--963`.

This is the source side after deleting extraneous tail coordinates and expanding
the linear consistency defect as `Σ_a ev(A_a ⊗ (I − B_a))`. -/
noncomputable def ldSandwichLineOnePoint_prefix_sourceOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) : ℝ :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ a : Fq params,
      strategy.state.ev
        (strategy.state.opTensor
          (((ldSandwichLineOnePointPrefixOriginalFamily params family hi) q).outcome
            (some a))
          (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
            (some a))))

/-- The intermediate scalar after the first Cauchy–Schwarz move
`ld-pasting.tex:964--986` (`eq:gonna-need-a-bigger-cauchy-schwarz`).

For an original-order prefix outcome `gs`, `orderedHalf` is
`G^{x_<i}_{g_<i} G^{x_i}_{g_i}` while `rotatedHalf` is
`G^{x_i}_{g_i} G^{x_<i}_{g_<i}`.  The first CS move replaces only the left half
of the sandwich, leaving `star orderedHalf` on the right. -/
noncomputable def ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) : ℝ :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1),
      match Option.map (fun g : MIPStarRE.LDT.Polynomial params => g q.1)
          (gs ⟨i, Nat.lt_succ_self i⟩) with
      | none => 0
      | some a =>
          let orderedHalf := gHatHalfProductOutcomeOperator params family (i + 1)
            (fun j => q.2 ⟨j.1, by omega⟩) gs
          let rotatedHalf := gHatHalfProductOutcomeOperator params family (i + 1)
            ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))
            ((gHatTupleOutcomeLastFrontEquiv params i) gs)
          strategy.state.ev
            (strategy.state.opTensor (rotatedHalf * star orderedHalf)
              (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
                (some a))))

/-- The target expanded off-diagonal scalar after the two CS moves.

This is the moved-prefix side.  The separate endpoint/prefix-completeness
collapse to `ldGbcon` is the already-proved
`ldSandwichLineOnePointPrefixMoved_eq_endpoint`, corresponding to
`ld-pasting.tex:1011--1024`. -/
noncomputable def ldSandwichLineOnePoint_prefix_movedOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) : ℝ :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ a : Fq params,
      strategy.state.ev
        (strategy.state.opTensor
          (((ldSandwichLineOnePointPrefixMovedFamily params family hi) q).outcome
            (some a))
          (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
            (some a))))

/-- Paper-faithful split of the remaining off-diagonal CS route.

The fields isolate the two uses of `Preliminaries.closenessOfIP` /
`Preliminaries.closenessOfIPAdjoint` in `ld-pasting.tex:964--1010`.  The endpoint
collapse after these fields is already packaged by
`ldSandwichLineOnePointPrefixMoved_eq_endpoint` (`ld-pasting.tex:1011--1024`). -/
structure LdSandwichLineOnePointOutcomeSumCSRoute
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    {k i : ℕ} (hi : i < k) : Prop where
  /-- First CS move, paper lines `964--986` and label
  `eq:gonna-need-a-bigger-cauchy-schwarz`: move the selected `G` to the left of
  the prefix in the left half of the sandwich. -/
  firstCauchySchwarz :
    ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi ≤
      ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi +
        Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))
  /-- Second CS move, paper lines `987--1010` and label `eq:even-bigger-CS`:
  move the selected `G` through the adjoint/right half, reaching the moved-prefix
  scalar. -/
  secondCauchySchwarz :
    ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi ≤
      ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi +
        Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))

/-- Absolute-value form of the two off-diagonal Cauchy–Schwarz moves.

This is the direct output shape of `Preliminaries.closenessOfIPAdjoint` and
`Preliminaries.closenessOfIP`: each field compares the two adjacent scalar
averages from `ld-pasting.tex:964--1010` with error `√ν₄`.  The one-sided route
used downstream is only an arithmetic consequence of these absolute-value
bounds. -/
structure LdSandwichLineOnePointOutcomeSumCSAbsBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    {k i : ℕ} (hi : i < k) : Prop where
  /-- First CS move in the exact absolute-value form of `prop:closeness-of-ip`,
  paper lines `964--986` and label `eq:gonna-need-a-bigger-cauchy-schwarz`. -/
  firstAbs :
    |ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi -
      ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi| ≤
      Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))
  /-- Second CS move in the exact absolute-value form of `prop:closeness-of-ip`,
  paper lines `987--1010` and label `eq:even-bigger-CS`. -/
  secondAbs :
    |ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi -
      ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi| ≤
      Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))

/-- Ordered half-product appearing in the line-one-point CS step. -/
noncomputable def ldSandwichLineOnePointCS_orderedHalf
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : 𝔓 :=
  gHatHalfProductOutcomeOperator params family (i + 1)
    (fun j => q.2 ⟨j.1, by omega⟩) gs

/-- Rotated half-product appearing after moving the selected slice to the front. -/
noncomputable def ldSandwichLineOnePointCS_rotatedHalf
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : 𝔓 :=
  gHatHalfProductOutcomeOperator params family (i + 1)
    ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))
    ((gHatTupleOutcomeLastFrontEquiv params i) gs)

/-- Right-hand complement selected by the completed polynomial outcome. -/
noncomputable def ldSandwichLineOnePointCS_rightComplement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ}
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : 𝔓 :=
  match Option.map (fun g : MIPStarRE.LDT.Polynomial params => g q.1)
      (gs ⟨i, Nat.lt_succ_self i⟩) with
  | none => 0
  | some a =>
      1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome (some a)

/-- Raw ordered left-placed family used in the generic CS proposition. -/
noncomputable def ldSandwichLineOnePointCS_Aord
    (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) → (K →L[ℂ] K) :=
  fun q gs => S.L (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)

/-- Raw rotated left-placed family used in the generic CS proposition. -/
noncomputable def ldSandwichLineOnePointCS_Arot
    (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) → (K →L[ℂ] K) :=
  fun q gs => S.L (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)

/-- The adjoint of the ordered raw CS family, as an indexed operator family. -/
noncomputable def ldSandwichLineOnePointCS_AordAdjointFamily
    (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k)
      (GHatTupleOutcome params (i + 1)) (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun gs => star (ldSandwichLineOnePointCS_Aord S params family hi q gs)
      total := 0 }

/-- The adjoint of the rotated raw CS family, as an indexed operator family. -/
noncomputable def ldSandwichLineOnePointCS_ArotAdjointFamily
    (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k)
      (GHatTupleOutcome params (i + 1)) (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun gs => star (ldSandwichLineOnePointCS_Arot S params family hi q gs)
      total := 0 }

/-- Raw left family for the adjoint-oriented CS input, indexed by original outcomes. -/
noncomputable def ldSandwichLineOnePointAdjointRawLeftFamily
    (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (_hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1))
      (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun gs =>
        (gHatHalfSandwichLeft S params family (i + 1)
          ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).outcome
          ((gHatTupleOutcomeLastReverseEquiv params i) gs)
      total := (gHatHalfSandwichLeft S params family (i + 1)
        ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).total }

/-- Raw right family for the adjoint-oriented CS input, indexed by original outcomes. -/
noncomputable def ldSandwichLineOnePointAdjointRawRightFamily
    (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (_hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1))
      (K →L[ℂ] K) :=
  fun q =>
    { outcome := fun gs =>
        (gHatHalfSandwichRight S params family (i + 1)
          ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).outcome
          ((gHatTupleOutcomeLastReverseEquiv params i) gs)
      total := (gHatHalfSandwichRight S params family (i + 1)
        ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).total }

/-- Raw commutation after last-reverse reindexing, lifted to sandwiched-line questions. -/
theorem ldSandwichLineOnePoint_adjointRawCommutation_originalOutcome
    (params : Parameters)
    [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params S family gamma zeta j)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0) :
    S.SDDOpRel
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointAdjointRawLeftFamily S params family hi)
      (ldSandwichLineOnePointAdjointRawRightFamily S params family hi)
      (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
  let Rest := Point params × ({j : Fin k // i < j.1} → Fq params)
  let δ := commuteGHalfSandwichError params gamma zeta (i + 1)
  let A : IdxOpFamily (PointTuple params (i + 1))
      (GHatTupleOutcome params (i + 1)) (K →L[ℂ] K) :=
    fun xs => gHatHalfSandwichLeft S params family (i + 1) ((pointTupleLastReverseEquiv params i) xs)
  let B : IdxOpFamily (PointTuple params (i + 1))
      (GHatTupleOutcome params (i + 1)) (K →L[ℂ] K) :=
    fun xs =>
      gHatHalfSandwichRight S params family (i + 1) ((pointTupleLastReverseEquiv params i) xs)
  have hprefix : S.SDDOpRel (uniformDistribution (PointTuple params (i + 1))) A B δ := by
    have h := (sddOpRel_uniform_equiv (pointTupleLastReverseEquiv params i).symm S.toVecState
      (gHatHalfSandwichLeft S params family (i + 1))
      (gHatHalfSandwichRight S params family (i + 1)) δ).1
      (ldSandwichLineOnePointPrefixMoved_rawCommutation params S family gamma zeta hcomm hi0)
    simpa only [Equiv.symm_symm] using h
  have hprod : S.SDDOpRel (uniformDistribution (PointTuple params (i + 1) × Rest))
      (fun qr => A qr.1) (fun qr => B qr.1) δ :=
    sddOpRel_uniform_fst S.toVecState A B δ hprefix
  have hfull : S.SDDOpRel (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => A ((sandwichedLineQuestionPrefixFstEquiv params hi q).1))
      (fun q => B ((sandwichedLineQuestionPrefixFstEquiv params hi q).1)) δ :=
    (sddOpRel_uniform_equiv (sandwichedLineQuestionPrefixFstEquiv params hi).symm S.toVecState
      (fun qr => A qr.1) (fun qr => B qr.1) δ).1 hprod
  exact CommutativityPoints.sddOpRel_congr_outcome S.toVecState
    (uniformDistribution (SandwichedLineQuestion params k)) _ _
    (ldSandwichLineOnePointAdjointRawLeftFamily S params family hi)
    (ldSandwichLineOnePointAdjointRawRightFamily S params family hi) δ
    (fun _ _ => rfl) (fun _ _ => rfl)
    (CommutativityPoints.sddOpRel_reindex (gHatTupleOutcomeLastReverseEquiv params i).symm
      S.toVecState _ _ _ δ hfull)

/-- The adjoint raw family agrees with the ordered CS family. -/
theorem ldSandwichLineOnePointAdjointRawLeftFamily_eq_CS_Aord_adjoint
    (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) :
    (ldSandwichLineOnePointAdjointRawLeftFamily S params family hi q).outcome gs =
      star (ldSandwichLineOnePointCS_Aord S params family hi q gs) :=
  (congrArg S.L (gHatHalfProduct_lastReverse_eq_conjTranspose params family i _ gs)).trans
    (S.leftTensor_conjTranspose _).symm

/-- The adjoint raw family agrees with the rotated CS family. -/
theorem ldSandwichLineOnePointAdjointRawRightFamily_eq_CS_Arot_adjoint
    (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) :
    (ldSandwichLineOnePointAdjointRawRightFamily S params family hi q).outcome gs =
      star (ldSandwichLineOnePointCS_Arot S params family hi q gs) :=
  (congrArg S.L
    (gHatRotatedHalfProduct_lastReverse_eq_conjTranspose_lastFront params family i _ gs)).trans
    (S.leftTensor_conjTranspose _).symm

/-- The adjoint-oriented raw-core bound needed by the line-one-point CS step. -/
theorem ldSandwichLineOnePoint_adjointRawCommutation_qSDDCore_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params strategy.state family gamma zeta j)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0) :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => strategy.state.qSDDCore
        (fun gs : GHatTupleOutcome params (i + 1) =>
          star (ldSandwichLineOnePointCS_Aord strategy.state params family hi q gs))
        (fun gs : GHatTupleOutcome params (i + 1) =>
          star (ldSandwichLineOnePointCS_Arot strategy.state params family hi q gs))) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1) :=
  (CommutativityPoints.sddOpRel_congr_outcome strategy.state.toVecState
    (uniformDistribution (SandwichedLineQuestion params k))
    (ldSandwichLineOnePointAdjointRawLeftFamily strategy.state params family hi)
    (ldSandwichLineOnePointAdjointRawRightFamily strategy.state params family hi)
    (ldSandwichLineOnePointCS_AordAdjointFamily strategy.state params family hi)
    (ldSandwichLineOnePointCS_ArotAdjointFamily strategy.state params family hi)
    (commuteGHalfSandwichError params gamma zeta (i + 1))
    (ldSandwichLineOnePointAdjointRawLeftFamily_eq_CS_Aord_adjoint strategy.state params family hi)
    (ldSandwichLineOnePointAdjointRawRightFamily_eq_CS_Arot_adjoint strategy.state params family hi)
    (ldSandwichLineOnePoint_adjointRawCommutation_originalOutcome
      params strategy.state family gamma zeta hcomm hi hi0)).squaredDistanceBound

/-- The `C` family for the first, right-action CS move. -/
noncomputable def ldSandwichLineOnePointCS_Cfirst
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) → Unit →
      (K →L[ℂ] K) := fun q gs _ =>
  strategy.state.opTensor (star (ldSandwichLineOnePointCS_orderedHalf params family hi q gs))
    (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)

/-- The `C` family for the second, left-action CS move. -/
noncomputable def ldSandwichLineOnePointCS_Csecond
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) → Unit →
      (K →L[ℂ] K) := fun q gs _ =>
  strategy.state.opTensor (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)
    (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)

/-- Raw scalar on the source side of the first CS application. -/
noncomputable def ldSandwichLineOnePointCS_firstSourceRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) : ℝ :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      strategy.state.ev
        (ldSandwichLineOnePointCS_Aord strategy.state params family hi q gs *
          ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u))

/-- Raw scalar on the target side of the first CS application. -/
noncomputable def ldSandwichLineOnePointCS_firstTargetRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) : ℝ :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      strategy.state.ev
        (ldSandwichLineOnePointCS_Arot strategy.state params family hi q gs *
          ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u))

/-- Raw scalar on the source side of the second CS application. -/
noncomputable def ldSandwichLineOnePointCS_secondSourceRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) : ℝ :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      strategy.state.ev
        (ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u *
          star (ldSandwichLineOnePointCS_Aord strategy.state params family hi q gs)))

/-- Raw scalar on the target side of the second CS application. -/
noncomputable def ldSandwichLineOnePointCS_secondTargetRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k i : ℕ} (hi : i < k) : ℝ :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      strategy.state.ev
        (ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u *
          star (ldSandwichLineOnePointCS_Arot strategy.state params family hi q gs)))

/-- Exact low-level facts needed to turn the generic `closenessOfIP*` lemmas into
`ld-pasting.tex:964--1010` for the line-one-point statement.

This record separates the generic CS theorem instantiation from the paper-specific facts:

* the adjoint-oriented raw square-distance bound corresponding to the first square
  root in lines 974--985 and reused in lines 1005--1010;
* the two unit-side measurement-completeness bounds from lines 986 and 1008;
* the algebraic regrouping/reindexing that identifies the raw CS scalars with the
  existing source, intermediate, and moved outcome sums. -/
structure LdSandwichLineOnePointCSFacts
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    {k i : ℕ} (hi : i < k) : Prop where
  /-- The adjoint-oriented raw square-distance bound. -/
  adjointRawCore :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => strategy.state.qSDDCore
        (fun gs : GHatTupleOutcome params (i + 1) =>
          star (ldSandwichLineOnePointCS_Aord strategy.state params family hi q gs))
        (fun gs : GHatTupleOutcome params (i + 1) =>
          star (ldSandwichLineOnePointCS_Arot strategy.state params family hi q gs))) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1)
  /-- The unit-side completeness bound of the first CS move. -/
  firstUnitBound :
    ∀ q, ∑ gs : GHatTupleOutcome params (i + 1),
      star (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u) *
        (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u) ≤ 1
  /-- The unit-side completeness bound of the second CS move. -/
  secondUnitBound :
    ∀ q, ∑ gs : GHatTupleOutcome params (i + 1),
      (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u) *
        star (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u) ≤ 1
  /-- The source outcome sum is the raw source scalar of the first CS move. -/
  source_eq_firstSourceRaw :
    ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_firstSourceRaw params strategy family hi
  /-- The intermediate outcome sum is the raw target scalar of the first CS move. -/
  afterFirst_eq_firstTargetRaw :
    ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_firstTargetRaw params strategy family hi
  /-- The intermediate outcome sum is the raw source scalar of the second CS move. -/
  afterFirst_eq_secondSourceRaw :
    ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_secondSourceRaw params strategy family hi
  /-- The moved outcome sum is the raw target scalar of the second CS move. -/
  moved_eq_secondTargetRaw :
    ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_secondTargetRaw params strategy family hi

/-- The adjoint-oriented raw commutator square-distance bound used by the two
Cauchy–Schwarz applications in the proof of `lem:ld-sandwich-line-one-point`.

The surrounding endpoint expansions and option-valued match-mass identities are
proved directly where they are used; this structure records only the nontrivial
orientation of the half-sandwich commutation estimate. -/
structure LdSandwichLineOnePointAdjointRawCoreBound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    {k i : ℕ} (hi : i < k) : Prop where
  /-- The averaged raw-core bound. -/
  bound :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => strategy.state.qSDDCore
        (fun gs : GHatTupleOutcome params (i + 1) =>
          star (ldSandwichLineOnePointCS_Aord strategy.state params family hi q gs))
        (fun gs : GHatTupleOutcome params (i + 1) =>
          star (ldSandwichLineOnePointCS_Arot strategy.state params family hi q gs))) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1)

/-- The adjoint-oriented estimate for the paper's `eq:add-in-the-bot` term.

The generic `closenessOfIP*` applications need the adjoint-oriented
`D D^†` square-distance term that appears in `ld-pasting.tex:980--985`
and is reused at lines `1005--1010`. -/
theorem ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_adjointRawCore
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    {k i : ℕ} (hi : i < k) (_hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => strategy.state.qSDDCore
        (fun gs : GHatTupleOutcome params (i + 1) =>
          star (ldSandwichLineOnePointCS_Aord strategy.state params family hi q gs))
        (fun gs : GHatTupleOutcome params (i + 1) =>
          star (ldSandwichLineOnePointCS_Arot strategy.state params family hi q gs))) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1) :=
  facts.bound

end MIPRE.LIDT.Co.Pasting

end
