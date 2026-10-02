/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/LineInterpolation/BadMass.lean, to the symmetric model of `planning/c6b-plan.md`;
not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.LineInterpolation.BadLine

@[expose] public section

/-!
# Line interpolation: bad-mass comparison

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/BadMass.lean` in
the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The main bad-mass comparison of `ld-pasting.tex`: the mismatch sums of the eligible sandwich
family, the decomposition of a bipartite consistency defect against a measurement into
single-outcome defects, the bad mass `hBConsistencyBadMass` and its bound by the line-point
defects, and `pastedInterpolation_verticalLine_defect_le_badMass`, which bounds the consistency
defect of the pasted interpolation restricted to a vertical line by that bad mass.

The slice family is an `IdxPolyFamily params 𝔓` and a strategy a `SymStrat params.next 𝔓 K`, so
the sandwiched, pasted and vertical-line families are local, in `𝔓` (the vendored `Op ι`). The
lemmas that read no state (`singleOutcomeRightSubMeas`, the two `postprocess_decide_*` lemmas and
`postprocess_restrictSubMeas_outcome`) are generic over an ordered `⋆`-ring. The three bipartite
defect lemmas take the symmetric model `S : SymModel 𝔓 K` as their first explicit argument, in
place of the vendored `ψ : QuantumState (ι × ι)`, and keep this file's namespace so that their
vendored names pair; the strategy lemmas read the defects on `strategy.state`. The vendored
normalization field `strategy.isNormalized` used by `hBConsistencyBadMass_le_one` is the
hypothesis-free `S.ev_one_of_isNormalized`, and no statement carries a swap or normalization
hypothesis, the vendored statements having none.

## Not ported

Every declaration of the vendored file has a counterpart here.

## New here

- `instDecidableEqFqFqNext`, `instDecidableEqFqNextFq`: scoped instances deciding equality
  between `Fq params` and `Fq params.next`, which the vendored file obtains from its file-wide
  `respectTransparency false`; ported dependants in `MIPRE.LIDT.Co.Pasting` that state the same
  mismatch conditions (`OverAllOutcomes/NonglobalDecomposition`) get them by importing this file.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq Point PointTuple AxisParallelLine
  AxisLinePolynomial appendPoint zeroCoord lastCoord)
open MIPStarRE.LDT.Pasting (GHatTupleOutcome SandwichedLineQuestion IsGloballyConsistent
  InterpolationEligible tupleInterpolatedVerticalLine
  tupleInterpolatedVerticalLine_ne_gives_exists_some_eval_mismatch)
open MIPRE.LIDT.Co (SymModel SymStrat SubMeas Measurement IdxPolyFamily postprocess)

/-- Equality of a coordinate of `params` with one of `params.next` is decidable. The vendored
file finds `instDecidableEqFin` here only under its file-wide
`backward.isDefEq.respectTransparency false`, since `Fq params.next` and `Fq params` agree only
after unfolding `Parameters.next`; this instance supplies the same decision procedure without
the option, scoped to `MIPRE.LIDT.Co.Pasting`. -/
scoped instance (priority := low) instDecidableEqFqFqNext {params : Parameters}
    (x : Fq params) (y : Fq params.next) : Decidable (x = y) :=
  instDecidableEqFin _ x y

/-- Equality of a coordinate of `params.next` with one of `params` is decidable (the mirror of
`instDecidableEqFqFqNext`). -/
scoped instance (priority := low) instDecidableEqFqNextFq {params : Parameters}
    (x : Fq params.next) (y : Fq params) : Decidable (x = y) :=
  instDecidableEqFin _ x y

section Generic

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- The Boolean submeasurement that keeps only the outcome `a0` of `B`, as its `true`
outcome. -/
noncomputable def singleOutcomeRightSubMeas
    {Outcome : Type*} [Fintype Outcome]
    (B : SubMeas Outcome R) (a0 : Outcome) : SubMeas Bool R where
  outcome
    | true => B.outcome a0
    | false => 0
  total := B.outcome a0
  outcome_pos
    | true => B.outcome_pos a0
    | false => le_refl 0
  sum_eq_total := (Fintype.sum_bool _).trans (add_zero _)
  total_le_one := le_trans (B.outcome_le_total a0) B.total_le_one

/-- The `true` outcome of the indicator postprocessing `a ↦ decide (a = a0)` is `A_{a0}`. -/
theorem postprocess_decide_eq_true_outcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome R) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome true = A.outcome a0 := by
  simp [postprocess, Finset.sum_filter]

/-- The `false` outcome of the indicator postprocessing at `a0`, plus `A_{a0}`, is the total
of `A`. -/
theorem postprocess_decide_false_add_true_eq_total
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome R) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome false + A.outcome a0 = A.total := by
  have h := (postprocess A (fun a => decide (a = a0))).sum_eq_total
  rw [Fintype.sum_bool, postprocess_decide_eq_true_outcome] at h
  exact (add_comm _ _).trans h

/-- The outcomes of a postprocessed restriction: the sum of the outcomes satisfying `p` and
mapped to `b`. -/
theorem postprocess_restrictSubMeas_outcome
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (A : SubMeas α R) (p : α → Prop) [DecidablePred p]
    (f : α → β) (b : β) :
    (postprocess (restrictSubMeas A p) f).outcome b =
      ∑ a : α, if p a ∧ f a = b then A.outcome a else 0 := by
  simp only [postprocess, restrictSubMeas, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hf : f c = b <;> by_cases hp : p c <;> simp [hf, hp]

end Generic

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- On globally consistent tuples, a vertical line interpolant different from `f` forces a
slice answer that disagrees with `f` at its height, so the first mismatch sum is bounded by the
second. -/
theorem interpolationEligibleSandwich_mismatch_sum_mono
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (f : AxisLinePolynomial params.next) :
    ∑ gs : GHatTupleOutcome params k,
        (if IsGloballyConsistent params xs gs
            ∧ tupleInterpolatedVerticalLine params u xs gs ≠ f then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0)
      ≤
      ∑ gs : GHatTupleOutcome params k,
        (if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0) := by
  refine Finset.sum_le_sum fun gs _ => ?_
  have hnonneg := (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs
  by_cases hright : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
      ((gs i).get hiSome) u ≠ f (xs i)
  · rw [ite_eq_left hright]
    split_ifs
    exacts [le_rfl, hnonneg]
  · rw [ite_eq_right hright]
    split_ifs with hleft
    · by_cases hEligible : InterpolationEligible params gs
      · exact absurd (tupleInterpolatedVerticalLine_ne_gives_exists_some_eval_mismatch
          params u xs hxs gs hEligible hleft.1 f hleft.2) hright
      · simp [interpolationEligibleSandwichFamily, restrictSubMeas, hEligible]
    · exact le_rfl

/-- A mismatch at some slice is bounded by the sum over slices of the mismatches at each
slice. -/
theorem interpolationEligibleSandwich_exists_mismatch_sum_le_sum
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (f : AxisLinePolynomial params.next) :
    (∑ gs : GHatTupleOutcome params k,
        if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0)
      ≤
      ∑ i : Fin k,
        ∑ gs : GHatTupleOutcome params k,
          if ∃ hiSome : (gs i).isSome = true,
              ((gs i).get hiSome) u ≠ f (xs i) then
            (interpolationEligibleSandwichFamily params family k xs).outcome gs
          else 0 := by
  refine (Finset.sum_le_sum fun gs _ => ?_).trans_eq Finset.sum_comm
  have hT : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      0 ≤ (if ∃ hiSome : (gs j).isSome = true, ((gs j).get hiSome) u ≠ f (xs j) then
        (interpolationEligibleSandwichFamily params family k xs).outcome gs else 0) :=
    fun j _ => by
      split_ifs
      exacts [(interpolationEligibleSandwichFamily params family k xs).outcome_pos gs, le_rfl]
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    exact (ite_eq_left hi).symm.le.trans (Finset.single_le_sum hT (Finset.mem_univ i))
  · exact Finset.sum_nonneg hT

/-- Reading the pasted interpolation on the vertical line through `u` against the single line
polynomial `f` is reading the globally consistent eligible sandwich against the interpolated
vertical line. -/
theorem pastedInterpolation_verticalLine_singleOutcome_postprocess
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (k : ℕ)
    (u : Point params)
    (xs : PointTuple params k)
    (f : AxisLinePolynomial params.next) :
    postprocess
      (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
      (fun h => decide (h = f)) =
    postprocess
      (restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs))
      (fun gs => decide (tupleInterpolatedVerticalLine params u xs gs = f)) :=
  (postprocess_postprocess _ _ _).trans (postprocess_postprocess _ _ _)

/-- If the right-hand Boolean submeasurement has only the `true` outcome, the
consistency defect is exactly the left `false` mass against its total operator. -/
theorem qBipartiteConsDefect_eq_false_mass_of_bool_right_true
    (S : SymModel 𝔓 K)
    (A B : SubMeas Bool 𝔓)
    (hfalse : B.outcome false = 0)
    (htrue : B.outcome true = B.total) :
    S.qBipartiteConsDefect A B = S.ev (S.opTensor (A.outcome false) B.total) := by
  have hsumA : A.outcome true + A.outcome false = A.total :=
    (Fintype.sum_bool _).symm.trans A.sum_eq_total
  have hzero : S.opTensor (A.outcome false) 0 = 0 :=
    (congrArg (S.L (A.outcome false) * ·) (map_zero S.R)).trans (mul_zero _)
  have hexpr : S.ev (S.opTensor A.total B.total) - S.qBipartiteMatchMass A B =
      S.ev (S.opTensor (A.outcome false) B.total) := by
    rw [SymModel.qBipartiteMatchMass, Fintype.sum_bool, htrue, hfalse, hzero, ← hsumA,
      S.opTensor_add_left_local, S.ev_add, S.ev_zero]
    ring
  change max 0 (S.ev (S.opTensor A.total B.total) - S.qBipartiteMatchMass A B) = _
  rw [hexpr]
  exact max_eq_right (S.ev_nonneg_of_psd _ <|
    S.opTensor_nonneg (A.outcome_pos false) B.total_nonneg)

/-- The defect of the indicator postprocessing at `a0` against the single outcome `a0` of `B`
is the mass of `A` off `a0` against `B_{a0}`. -/
theorem qBipartiteConsDefect_postprocess_eq_singleOutcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (S : SymModel 𝔓 K)
    (A B : SubMeas Outcome 𝔓) (a0 : Outcome) :
    S.qBipartiteConsDefect (postprocess A (fun a => decide (a = a0)))
      (singleOutcomeRightSubMeas B a0) =
        S.ev
          (S.opTensor ((postprocess A (fun a => decide (a = a0))).outcome false)
            (B.outcome a0)) :=
  qBipartiteConsDefect_eq_false_mass_of_bool_right_true S
    (postprocess A (fun a => decide (a = a0))) (singleOutcomeRightSubMeas B a0) rfl rfl

/-- The defect of `A` against a measurement `B` is the sum over outcomes `a0` of the
single-outcome defects. -/
theorem qBipartiteConsDefect_eq_sum_singleOutcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (S : SymModel 𝔓 K)
    (A : SubMeas Outcome 𝔓)
    (B : Measurement Outcome 𝔓) :
    S.qBipartiteConsDefect A B.toSubMeas =
      ∑ a0 : Outcome,
        S.qBipartiteConsDefect (postprocess A (fun a => decide (a = a0)))
          (singleOutcomeRightSubMeas B.toSubMeas a0) := by
  have hsingle_term : ∀ a0 : Outcome,
      S.ev (S.opTensor A.total (B.outcome a0)) =
        S.qBipartiteConsDefect (postprocess A (fun a => decide (a = a0)))
          (singleOutcomeRightSubMeas B.toSubMeas a0) +
          S.ev (S.opTensor (A.outcome a0) (B.outcome a0)) := fun a0 => by
    rw [qBipartiteConsDefect_postprocess_eq_singleOutcome, ← S.ev_add,
      ← S.opTensor_add_left_local, postprocess_decide_false_add_true_eq_total]
  have hdecomp :
      S.ev (S.opTensor A.total B.toSubMeas.total) - S.qBipartiteMatchMass A B.toSubMeas =
        ∑ a0 : Outcome,
          S.qBipartiteConsDefect (postprocess A (fun a => decide (a = a0)))
            (singleOutcomeRightSubMeas B.toSubMeas a0) := by
    rw [← B.sum_eq_total, S.opTensor_sum_right_univ, S.ev_sum, SymModel.qBipartiteMatchMass]
    simp only [hsingle_term, Finset.sum_add_distrib, add_sub_cancel_right]
  change max 0 (S.ev (S.opTensor A.total B.toSubMeas.total) -
    S.qBipartiteMatchMass A B.toSubMeas) = _
  rw [hdecomp]
  exact max_eq_right (Finset.sum_nonneg fun a0 _ => S.qBipartiteConsDefect_nonneg _ _)

/-- The bad mass of the vertical-line consistency: the mass of the eligible sandwich on tuples
with a slice answer disagreeing at its height with the line polynomial `f`, against `B^u_f`,
summed over `f`. -/
noncomputable def hBConsistencyBadMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k) : ℝ :=
  ∑ f : AxisLinePolynomial params.next,
    strategy.state.ev
      (strategy.state.opTensor
        (∑ gs : GHatTupleOutcome params k,
        if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
              ((gs i).get hiSome) u ≠ f (xs i) then
            (interpolationEligibleSandwichFamily params family k xs).outcome gs
          else 0)
        ((verticalLineMeasurementFamily params strategy u).outcome f))

/-- The one-point right family of the `i`-th slot, as a measurement. -/
noncomputable def ldSandwichLineOnePointRightMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) :
    Measurement (Option (Fq params)) 𝔓 where
  toSubMeas := ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q)
  total_eq_one :=
    (strategy.axisParallelMeasurement
      { base := appendPoint params q.1 zeroCoord
        direction := lastCoord params }).total_eq_one

/-- The `some a` outcome of the one-point right measurement is the sum of the vertical line
outcomes whose polynomial takes the value `a` at the slot's height. -/
theorem ldSandwichLineOnePointRightMeasurement_outcome_some_eq_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) (a : Fq params) :
    (ldSandwichLineOnePointRightMeasurement params strategy family i q).outcome (some a) =
      ∑ f : AxisLinePolynomial params.next,
        if f (q.2 i) = a then
          (verticalLineMeasurementFamily params strategy q.1).outcome f
        else 0 := by
  simp only [ldSandwichLineOnePointRightMeasurement, ldSandwichLineOnePointRightFamily,
    postprocess, i.2, Finset.sum_filter, dite_true]
  exact Finset.sum_congr rfl fun f _ => if_congr Option.some_inj rfl rfl

/-- The mismatch mass of the `i`-th slot against the value `a` is bounded by the `false`
outcome of the one-point left family read against `some a`. -/
theorem grouped_coordinate_mismatch_le_left_falseOutcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ} (u : Point params) (xs : PointTuple params k)
    (i : Fin k) (a : Fq params) :
    (∑ gs : GHatTupleOutcome params k,
      if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ a then
        (interpolationEligibleSandwichFamily params family k xs).outcome gs
      else 0)
    ≤
    (postprocess
      ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
      (fun o => decide (o = some a))).outcome false := by
  have hrewrite :
      (postprocess
        ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
        (fun o => decide (o = some a))).outcome false =
        ∑ gs : GHatTupleOutcome params k,
          if Option.map (fun g : MIPStarRE.LDT.Polynomial params => g u) (gs i) ≠ some a then
            (restrictSubMeas (gHatSandwichFamily params family k xs)
              (fun gs => (gs i).isSome = true)).outcome gs
          else 0 := by
    rw [ldSandwichLineOnePointLeftFamily, postprocess_postprocess]
    simp [postprocess, Function.comp, i.2, Finset.sum_filter]
  rw [hrewrite]
  refine Finset.sum_le_sum fun gs _ => ?_
  by_cases hm : ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ a
  · obtain ⟨hiSome, hne⟩ := hm
    have hneq : Option.map (fun g : MIPStarRE.LDT.Polynomial params => g u) (gs i) ≠ some a := by
      cases hgi : gs i with
      | none => simp [hgi] at hiSome
      | some g => simpa [hgi] using hne
    by_cases hEligible : InterpolationEligible params gs
    · simp [interpolationEligibleSandwichFamily, restrictSubMeas, hiSome, hneq, hEligible, hne]
    · simp [interpolationEligibleSandwichFamily, restrictSubMeas, hiSome, hneq, hEligible,
        (gHatSandwichFamily params family k xs).outcome_pos gs]
  · rw [ite_eq_right hm]
    split_ifs
    exacts [(restrictSubMeas (gHatSandwichFamily params family k xs)
      (fun gs => (gs i).isSome = true)).outcome_pos gs, le_rfl]

/-- The bad mass of the `i`-th slot is bounded by the `i`-th line-point consistency defect. -/
theorem hBConsistencyCoordMass_le_linePointDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ} (u : Point params) (xs : PointTuple params k)
    (i : Fin k) :
    (∑ f : AxisLinePolynomial params.next,
      strategy.state.ev
        (strategy.state.opTensor
          (∑ gs : GHatTupleOutcome params k,
            if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0)
          ((verticalLineMeasurementFamily params strategy u).outcome f)))
      ≤ strategy.state.qBipartiteConsDefect
          ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
          ((ldSandwichLineOnePointRightFamily params strategy family k i.1) (u, xs)) := by
  let S := strategy.state
  let q : SandwichedLineQuestion params k := (u, xs)
  let A := ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
  let Bm := ldSandwichLineOnePointRightMeasurement params strategy family i q
  let B := verticalLineMeasurementFamily params strategy u
  let leftFalse : Fq params → 𝔓 := fun a =>
    (postprocess A (fun o => decide (o = some a))).outcome false
  have hstep : ∀ f : AxisLinePolynomial params.next,
      S.ev (S.opTensor
          (∑ gs : GHatTupleOutcome params k,
            if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0)
          (B.outcome f))
        ≤ S.ev (S.opTensor (leftFalse (f (xs i))) (B.outcome f)) := fun f =>
    S.ev_mono _ _ <| S.opTensor_mono_left
      (grouped_coordinate_mismatch_le_left_falseOutcome params strategy family u xs i (f (xs i)))
      (B.outcome_pos f)
  have hgrouped :
      ∑ f : AxisLinePolynomial params.next, S.ev (S.opTensor (leftFalse (f (xs i))) (B.outcome f))
        = ∑ a : Fq params, S.ev (S.opTensor (leftFalse a) (Bm.outcome (some a))) := by
    have hzero : ∀ X : 𝔓, S.opTensor X 0 = 0 := fun X =>
      (congrArg (S.L X * ·) (map_zero S.R)).trans (mul_zero _)
    simp only [Bm, ldSandwichLineOnePointRightMeasurement_outcome_some_eq_sum,
      S.opTensor_sum_right_univ, S.ev_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => Eq.symm <|
      (Finset.sum_eq_single (f (xs i)) (fun b _ hb => ?_)
        (fun h => absurd (Finset.mem_univ _) h)).trans
        (congrArg (fun X => S.ev (S.opTensor _ X)) (ite_eq_left rfl))
    exact (congrArg (fun X => S.ev (S.opTensor (leftFalse b) X))
      (ite_eq_right fun h => hb h.symm)).trans ((congrArg S.ev (hzero _)).trans S.ev_zero)
  calc
    _ ≤ ∑ f : AxisLinePolynomial params.next,
          S.ev (S.opTensor (leftFalse (f (xs i))) (B.outcome f)) :=
        Finset.sum_le_sum fun f _ => hstep f
    _ = ∑ a : Fq params, S.ev (S.opTensor (leftFalse a) (Bm.outcome (some a))) := hgrouped
    _ = ∑ a : Fq params,
          S.qBipartiteConsDefect (postprocess A (fun o => decide (o = some a)))
            (singleOutcomeRightSubMeas Bm.toSubMeas (some a)) :=
        Finset.sum_congr rfl fun a _ =>
          (qBipartiteConsDefect_postprocess_eq_singleOutcome S A Bm.toSubMeas (some a)).symm
    _ ≤ S.qBipartiteConsDefect A Bm.toSubMeas := by
        rw [qBipartiteConsDefect_eq_sum_singleOutcome S A Bm, Fintype.sum_option]
        have hnone_nonneg :
            0 ≤ S.qBipartiteConsDefect (postprocess A (fun o => decide (o = none)))
              (singleOutcomeRightSubMeas Bm.toSubMeas none) :=
          S.qBipartiteConsDefect_nonneg _ _
        linarith

/-- The bad mass is bounded by the sum over slots of the line-point consistency defects. -/
theorem hBConsistencyBadMass_le_linePointDefectSum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    hBConsistencyBadMass params strategy family u xs
      ≤ ∑ i : Fin k,
          strategy.state.qBipartiteConsDefect
            ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
            ((ldSandwichLineOnePointRightFamily params strategy family k i.1) (u, xs)) := by
  let S := strategy.state
  let B := verticalLineMeasurementFamily params strategy u
  calc
    hBConsistencyBadMass params strategy family u xs
      ≤ ∑ f : AxisLinePolynomial params.next,
          S.ev (S.opTensor
              (∑ i : Fin k,
                ∑ gs : GHatTupleOutcome params k,
                  if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs
                  else 0)
              (B.outcome f)) :=
        Finset.sum_le_sum fun f _ => S.ev_mono _ _ <| S.opTensor_mono_left
          (interpolationEligibleSandwich_exists_mismatch_sum_le_sum params family u xs f)
          (B.outcome_pos f)
    _ = ∑ i : Fin k,
          ∑ f : AxisLinePolynomial params.next,
            S.ev (S.opTensor
                (∑ gs : GHatTupleOutcome params k,
                  if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs
                  else 0)
                (B.outcome f)) := by
        simp only [S.opTensor_sum_left_univ, S.ev_sum]
        exact Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
        hBConsistencyCoordMass_le_linePointDefect params strategy family u xs i

/-- The bad mass is nonnegative. -/
theorem hBConsistencyBadMass_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    0 ≤ hBConsistencyBadMass params strategy family u xs := by
  refine Finset.sum_nonneg fun f _ => strategy.state.ev_nonneg_of_psd _ ?_
  refine strategy.state.opTensor_nonneg (Finset.sum_nonneg fun gs _ => ?_)
    ((verticalLineMeasurementFamily params strategy u).outcome_pos f)
  split_ifs
  exacts [(interpolationEligibleSandwichFamily params family k xs).outcome_pos gs, le_rfl]

/-- The bad mass is at most one. -/
theorem hBConsistencyBadMass_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    hBConsistencyBadMass params strategy family u xs ≤ 1 := by
  let S := strategy.state
  let E := interpolationEligibleSandwichFamily params family k xs
  let B := verticalLineMeasurementFamily params strategy u
  have hLle : ∀ f : AxisLinePolynomial params.next,
      (∑ gs : GHatTupleOutcome params k,
        if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
          E.outcome gs
        else 0) ≤ E.total := fun f =>
    (Finset.sum_le_sum fun gs _ => by
      split_ifs
      exacts [le_rfl, E.outcome_pos gs]).trans_eq E.sum_eq_total
  have hBtotal : B.total = 1 :=
    (strategy.axisParallelMeasurement
      { base := appendPoint params u zeroCoord
        direction := lastCoord params }).total_eq_one
  calc
    hBConsistencyBadMass params strategy family u xs
      ≤ ∑ f : AxisLinePolynomial params.next, S.ev (S.opTensor E.total (B.outcome f)) :=
        Finset.sum_le_sum fun f _ =>
          S.ev_mono _ _ <| S.opTensor_mono_left (hLle f) (B.outcome_pos f)
    _ = S.ev (S.opTensor E.total B.total) := by
        rw [← S.ev_sum, ← S.opTensor_sum_right_univ, B.sum_eq_total]
    _ ≤ S.ev 1 :=
        S.ev_mono _ _ <| S.opTensor_le_one E.total_nonneg E.total_le_one hBtotal.le
    _ = 1 := S.ev_one_of_isNormalized

/-- The consistency defect of the pasted interpolation restricted to the vertical line through
`u`, against the vertical line measurement, is bounded by the bad mass. -/
theorem pastedInterpolation_verticalLine_defect_le_badMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs) :
    strategy.state.qBipartiteConsDefect
      (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
      (verticalLineMeasurementFamily params strategy u)
      ≤ hBConsistencyBadMass params strategy family u xs := by
  let S := strategy.state
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params u zeroCoord
      direction := lastCoord params }
  let Bm : Measurement (AxisLinePolynomial params.next) 𝔓 :=
    (strategy.axisParallelMeasurement ℓ).toMeasurement
  change S.qBipartiteConsDefect _ Bm.toSubMeas ≤ _
  rw [qBipartiteConsDefect_eq_sum_singleOutcome S _ Bm]
  refine Finset.sum_le_sum fun f _ => ?_
  rw [qBipartiteConsDefect_postprocess_eq_singleOutcome,
    pastedInterpolation_verticalLine_singleOutcome_postprocess,
    postprocess_restrictSubMeas_outcome]
  simp only [decide_eq_false_iff_not]
  exact S.ev_mono _ _ <| S.opTensor_mono_left
    (interpolationEligibleSandwich_mismatch_sum_mono params family u xs hxs f)
    (Bm.outcome_pos f)

end MIPRE.LIDT.Co.Pasting

end
