/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG/Core/StageMass.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.Core.BernoulliTail
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.Core.AveragesAndOps
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.Setup.StepLemmas.Split
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich.Setup.StepLemmas.Move
public import MIPRE.Background.LIDT.Co.Preliminaries.CauchySchwarz
public import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.Core.StageMass

@[expose] public section

/-!
# Section 12 pasting: from-H-to-G stage-mass bookkeeping

Stage-`0` identification, terminal identification, adjacent-stage split, and telescoping lemmas
that connect the Lean recurrence stages to the paper scalars: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/StageMass.lean` in the port
of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The slice family is an `IdxPolyFamily params 𝔓`, so the sandwiched family, its per-type averages
and the recurrence weights are local operators in `𝔓` (the vendored `Op ι`). The vendored second
bipartite state `ψbi : QuantumState (ι × ι)` both places and evaluates, so it is the symmetric
model `S : SymModel 𝔓 K`, in the vendored argument position, as in `Co/Pasting/Statements.lean`;
`leftTensor (ι₂ := ι)`/`rightTensor (ι₁ := ι)` are `S.L`/`S.R`. The vendored weight operator,
also named `S` in `fromHToGAdjacentStageM4_head_sum`, `fromHToG_avgOver_head_ev` and
`fromHToG_avgOver_head_branch_ev`, is renamed `W` (a `let` or an explicit positional argument,
so callers are unaffected). The four sandwich-total identities read no state.

## Not ported

- `fromHToG_outcomesByType_iff_type_eq`: classical, imported.
- `fromHToG_interpolationEligible_iff_type_weight`: classical, imported.
- `abs_telescope_nat`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq PointTuple uniformDistribution avgOver)
open MIPStarRE.LDT.Pasting (GHatType GHatOutcome GHatTupleOutcome gHatTypeWeight prependTypeBit
  gHatTupleType InterpolationEligible fromHToGRecurrenceError
  fromHToG_outcomesByType_iff_type_eq fromHToG_interpolationEligible_iff_type_weight
  abs_telescope_nat)
open MIPRE.LIDT.Co (SymModel SymStrat IdxPolyFamily averageOperatorOverDistribution)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Terminal endpoint identification for the Lean `fromHToG` stage mass: at stage `k`,
the tail is empty, the suffix sandwich contributes identity, and the recurrence weight
is the Bernoulli-tail operator. -/
theorem fromHToGStageMass_terminal_eq (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    fromHToGStageMass params S family k k =
      fromHToGBernoulliTailMass params S family k := by
  unfold fromHToGStageMass
  rw [Nat.sub_self, Fintype.sum_subsingleton _ (default : GHatType 0)]
  change S.ev (S.L (averagedSandwichByTypeSubMeas params family 0 default).total *
      S.R (truncatedTypeSums family.averagedSubMeas.total params.d k default)) =
    S.ev (S.R (bernoulliTailOperator k params.d family.averagedSubMeas.total))
  rw [fromHToG_averagedSandwichByTypeSubMeas_zero_total_eq_one, S.leftTensor_one, one_mul,
    fromHToG_truncatedTypeSums_full_eq_bernoulliTailOperator]

/-- Collapse the head outcome sum in `M₄` for fixed tail point and type. -/
theorem fromHToGAdjacentStageM4_head_sum (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (ℓ n : ℕ)
    (b : Bool) (τ : GHatType n) (x : Fq params) (xs : PointTuple params n) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let W := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          S.ev (S.L (T * star T) * S.R (W * U * U))) =
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        let W := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        let B := if b then (completePartSubMeas params family x).total
          else (incompletePartSubMeas params family x).total
        S.ev (S.L (T * star T) * S.R (W * B)) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun gs _ => ?_
  cases b
  · exact fromHToG_ev_sum_isSome_false_weight params S family x _ _
  · exact fromHToG_ev_sum_isSome_true_weight params S family x _ _

/-- Split the eligible sandwich total into a sum over exact Boolean outcome types. -/
theorem fromHToG_interpolationEligibleSandwich_total_eq_type_sum (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (k : ℕ)
    (xs : PointTuple params k) :
    (interpolationEligibleSandwichFamily params family k xs).total =
      ∑ τ : GHatType k,
        if params.d + 1 ≤ gHatTypeWeight τ then
          ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
            gHatTupleType gs = τ,
            (gHatSandwichFamily params family k xs).outcome gs
        else 0 := by
  change ∑ gs ∈ Finset.univ.filter (InterpolationEligible params),
      (gHatSandwichFamily params family k xs).outcome gs = _
  rw [Finset.sum_filter, ← Finset.sum_fiberwise Finset.univ gHatTupleType]
  refine Finset.sum_congr rfl fun τ _ => ?_
  split_ifs with hτ
  · refine Finset.sum_congr rfl fun gs hgs => ite_eq_left ?_
    rw [fromHToG_interpolationEligible_iff_type_weight, (Finset.mem_filter.1 hgs).2]
    exact hτ
  · refine Finset.sum_eq_zero fun gs hgs => ite_eq_right ?_
    rw [fromHToG_interpolationEligible_iff_type_weight, (Finset.mem_filter.1 hgs).2]
    exact hτ

/-- The per-type averaged sandwich total is the uniform average of the exact-type
fibers of `gHatSandwichFamily`. -/
theorem fromHToG_averagedSandwichByType_total_eq_type_sum (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (k : ℕ) (τ : GHatType k) :
    (averagedSandwichByTypeSubMeas params family k τ).total =
      ∑ xs ∈ (uniformDistribution (PointTuple params k)).support,
        (uniformDistribution (PointTuple params k)).weight xs •
          (∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
            gHatTupleType gs = τ,
            (gHatSandwichFamily params family k xs).outcome gs) := by
  classical
  exact Finset.sum_congr rfl fun _ _ => congrArg _ <|
    Finset.sum_congr (Finset.filter_congr fun gs _ => fromHToG_outcomesByType_iff_type_eq gs τ)
      fun _ _ => rfl

/-- Fold the tail point/outcome average of a fixed type into
`averagedSandwichByTypeSubMeas`. -/
theorem fromHToG_avgOver_tail_type_ev (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (n : ℕ) (τ : GHatType n) (B : 𝔓) :
    avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        S.ev (S.L (T * star T) * S.R B)) =
      S.ev (S.L (averagedSandwichByTypeSubMeas params family n τ).total * S.R B) := by
  rw [fromHToG_averagedSandwichByType_total_eq_type_sum, ← S.leftTensor_finset_sum,
    Finset.sum_mul, S.ev_finset_sum]
  refine Finset.sum_congr rfl fun xs _ => ?_
  rw [S.leftTensor_mul_rightTensor_real_smul_left, S.ev_scale, ← S.leftTensor_finset_sum,
    Finset.sum_mul, S.ev_finset_sum]
  rfl

/-- Fold a head-point scalar average into an operator average on the right tensor
factor, with a fixed left factor and fixed left multiplier `W` on the right
register. -/
theorem fromHToG_avgOver_head_ev (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (A W : 𝔓) (F : Fq params → 𝔓) :
    avgOver (uniformDistribution (Fq params)) (fun x => S.ev (S.L A * S.R (W * F x))) =
      S.ev (S.L A *
        S.R (W * averageOperatorOverDistribution (uniformDistribution (Fq params)) F)) := by
  unfold avgOver averageOperatorOverDistribution
  rw [Finset.mul_sum, ← S.rightTensor_finset_sum, Finset.mul_sum, S.ev_finset_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_smul_comm, S.leftTensor_mul_rightTensor_real_smul_right, S.ev_scale]

/-- Fold the complete/incomplete head branch average into the stored exact branch
averages. -/
theorem fromHToG_avgOver_head_branch_ev (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (hcomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total)
    (hincomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total)
    (b : Bool) (A W : 𝔓) :
    avgOver (uniformDistribution (Fq params)) (fun x =>
      let B := if b then (completePartSubMeas params family x).total
        else (incompletePartSubMeas params family x).total
      S.ev (S.L A * S.R (W * B))) =
      S.ev (S.L A *
        S.R (W * if b then family.averagedSubMeas.total
          else 1 - family.averagedSubMeas.total)) := by
  cases b
  · exact (fromHToG_avgOver_head_ev params S A W _).trans
      (congrArg (fun T => S.ev (S.L A * S.R (W * T))) hincomplete)
  · exact (fromHToG_avgOver_head_ev params S A W _).trans
      (congrArg (fun T => S.ev (S.L A * S.R (W * T))) hcomplete)

/-- The eligible averaged sandwich total is the sum of the eligible exact-type
averaged totals.  This is the exact stage-`0` bookkeeping identity used in
`lem:from-H-to-G`. -/
theorem fromHToG_averagedEligibleSandwich_total_eq_type_sum (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    (averagedEligibleSandwichSubMeas params family k).total =
      ∑ τ : GHatType k,
        if params.d + 1 ≤ gHatTypeWeight τ then
          (averagedSandwichByTypeSubMeas params family k τ).total
        else 0 := by
  change ∑ xs ∈ (uniformDistribution (PointTuple params k)).support,
      (uniformDistribution (PointTuple params k)).weight xs •
        (interpolationEligibleSandwichFamily params family k xs).total = _
  simp only [fromHToG_interpolationEligibleSandwich_total_eq_type_sum,
    fromHToG_averagedSandwichByType_total_eq_type_sum, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun τ _ => by rw [Finset.sum_ite_irrel, Finset.sum_const_zero]

/-- Stage `0` of the Lean recurrence is exactly the all-outcomes expansion mass:
the zero-prefix recurrence weight is the eligibility indicator, and the exact-type
fibers partition the eligible sandwich total. -/
theorem fromHToGStageMass_zero_eq (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k : ℕ) :
    fromHToGStageMass params S family k 0 =
      fromHToGAllOutcomesMass params strategy S family k := by
  change ∑ τ : GHatType k, S.ev (S.L (averagedSandwichByTypeSubMeas params family k τ).total *
      S.R (truncatedTypeSums family.averagedSubMeas.total params.d 0 τ)) =
    S.ev (S.L (averagedEligibleSandwichSubMeas params family k).total)
  rw [fromHToG_averagedEligibleSandwich_total_eq_type_sum, ← S.leftTensor_finset_sum,
    S.ev_finset_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [fromHToG_truncatedTypeSums_zero_eq_indicator, fromHToG_leftTensor_mul_rightTensor_indicator]

/-- Tail-level version of the exact `S`-recurrence used at the end of the
adjacent-stage comparison.  After the analytic move-right / commute / move-right
steps, the remaining paper expression collapses to the next Lean stage by
expanding the recurrence weight as
`S_{τ_{>ℓ}} = S_{1 :: τ_{>ℓ}} G + S_{0 :: τ_{>ℓ}} (I-G)`; this lemma records
that exact bookkeeping at the scalar mass level. -/
theorem fromHToGTailStageMass_succ_weight_recurrence (params : Parameters)
    [FieldModel params.q] (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGTailStageMass params S family (prefixLen + 1) τtail =
      S.ev (S.L (averagedSandwichByTypeSubMeas params family tailLen τtail).total *
        S.R (fromHToGRecurrenceWeight params family prefixLen
              (prependTypeBit true τtail) * family.averagedSubMeas.total +
            fromHToGRecurrenceWeight params family prefixLen
              (prependTypeBit false τtail) * (1 - family.averagedSubMeas.total))) :=
  congrArg (fun T => S.ev (S.L (averagedSandwichByTypeSubMeas params family tailLen τtail).total *
    S.R T)) (fromHToGRecurrenceWeight_succ params family prefixLen τtail)

/-- Split a nonterminal `fromHToG` stage by the next Boolean tail bit. -/
theorem fromHToGStageMass_split_succ (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) {k ℓ : ℕ} (hℓ : ℓ < k) :
    fromHToGStageMass params S family k ℓ =
      ∑ p : Bool × GHatType (k - (ℓ + 1)),
        fromHToGTailStageMass params S family ℓ (prependTypeBit p.1 p.2) := by
  unfold fromHToGStageMass
  rw [show k - ℓ = (k - (ℓ + 1)) + 1 by omega]
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Bool).symm _ _
    fun τ => congrArg _ (Fin.cons_self_tail τ).symm

/-- The adjacent-stage recurrence fields imply the scalar first-to-last
`telescope` bound for the `fromHToG` stage masses. -/
theorem fromHToGStageMass_telescope (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (gamma zeta : ℝ) (k : ℕ)
    (hstep : ∀ ℓ : ℕ, ℓ < k →
      |fromHToGStageMass params S family k ℓ -
          fromHToGStageMass params S family k (ℓ + 1)| ≤
        fromHToGRecurrenceError params gamma zeta k) :
    |fromHToGStageMass params S family k 0 -
        fromHToGStageMass params S family k k| ≤
      (k : ℝ) * fromHToGRecurrenceError params gamma zeta k :=
  abs_telescope_nat (fun ℓ => fromHToGStageMass params S family k ℓ)
    (fromHToGRecurrenceError params gamma zeta k) k hstep

end MIPRE.LIDT.Co.Pasting

end
