/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG/PaperBounds/SandwichContext.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.AdjacentStages.Chain.FinalMove

@[expose] public section

/-!
# Section 12 pasting: from-H-to-G `S U S` context-average bounds

Sandwich-sum identities and the `S U S` context-average bound used in the second half-sandwich
and final move-right Cauchy--Schwarz steps: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperBounds/SandwichContext.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The slice family is an `IdxPolyFamily params 𝔓`, so the completed-slice outcomes, the
half-products and the recurrence weights are local operators in `𝔓` (the vendored `Op ι`), and
`ᴴ` is `star`. The vendored bipartite state `ψbi : QuantumState (ι × ι)` both places and
evaluates, so it is the symmetric model `S : SymModel 𝔓 K`, in the vendored argument position;
`leftTensor`/`rightTensor` are `S.L`/`S.R`. The vendored weight operator, also named `S` (a `let`
in `fromHToG_SUS_context_avg_le_one`, an explicit argument of the three sandwich-average lemmas),
is renamed `W`. The vendored `fromHToG_SUS_context_avg_le_one` takes the normalization hypothesis
`hnorm : ψbi.IsNormalized`, used only for `ev 1 = 1`; it is dropped here
(`S.ev_one_of_isNormalized` holds for every model), so vendored callers pass `strategy.state`
where they passed `ψbi hnorm`. No other lemma has a swap, density or normalization hypothesis.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq PointTuple uniformDistribution avgOver avgOver_congr)
open MIPStarRE.LDT.Pasting (GHatType GHatOutcome GHatTupleOutcome prependTypeBit gHatTupleType
  fromHToG_sum_product fromHToG_type_filtered_outcome_sum fromHToG_bool_type_filtered_outcome_sum
  fromHToGAdjacentStage_globalize_pointwiseShape)
open MIPRE.LIDT.Co (SymModel IdxPolyFamily averageOperatorOverDistribution
  averageOperatorOverDistribution_mul_left_right)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The total mass of the tail sandwich family is the identity. -/
theorem fromHToG_gHatSandwichFamily_total_eq_one (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (n : ℕ) (xs : PointTuple params n) :
    (gHatSandwichFamily params family n xs).total = 1 := by
  show gHatHalfProductTotalOperator params family n xs *
    star (gHatHalfProductTotalOperator params family n xs) = 1
  rw [gHatHalfProductTotalOperator_eq_one, star_one, mul_one]

/-- The tail sandwich outcomes sum to the identity. -/
theorem fromHToG_gHatSandwichFamily_sum_eq_one (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (n : ℕ) (xs : PointTuple params n) :
    (∑ gs : GHatTupleOutcome params n,
      (gHatSandwichFamily params family n xs).outcome gs) = 1 :=
  (gHatSandwichFamily params family n xs).sum_eq_total.trans
    (fromHToG_gHatSandwichFamily_total_eq_one params family n xs)

/-- Expectation-level branch sum with an `S · U · S` sandwich. -/
theorem fromHToG_ev_sum_isSome_sandwich_weight (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (x : Fq params)
    (b : Bool) (A W : 𝔓) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        S.ev (S.L A * S.R (W * (gHatIdxMeas params family x).outcome g * W))) =
      S.ev (S.L A *
        S.R (W * (if b then (completePartSubMeas params family x).total
          else (incompletePartSubMeas params family x).total) * W)) := by
  rw [← S.ev_finset_sum, ← Finset.mul_sum, S.rightTensor_finset_sum, ← Finset.sum_mul,
    ← Finset.mul_sum]
  cases b
  · rw [fromHToG_gHatIdxMeas_sum_isSome_false]; rfl
  · rw [fromHToG_gHatIdxMeas_sum_isSome_true]; rfl

/-- Fold a head-point scalar average with an `S · F x · S` sandwich into the
right tensor factor. -/
theorem fromHToG_avgOver_head_ev_sandwich (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (A W : 𝔓) (F : Fq params → 𝔓) :
    avgOver (uniformDistribution (Fq params)) (fun x => S.ev (S.L A * S.R (W * F x * W))) =
      S.ev (S.L A *
        S.R (W * averageOperatorOverDistribution (uniformDistribution (Fq params)) F * W)) := by
  rw [← averageOperatorOverDistribution_mul_left_right]
  unfold avgOver averageOperatorOverDistribution
  rw [← S.rightTensor_finset_sum, Finset.mul_sum, S.ev_finset_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [S.rightTensor_real_smul, mul_smul_comm, S.ev_real_smul]

/-- Fold the complete/incomplete head branch average with an `S · B · S`
sandwich into the stored exact branch averages. -/
theorem fromHToG_avgOver_head_branch_ev_sandwich (params : Parameters) [FieldModel params.q]
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
      S.ev (S.L A * S.R (W * B * W))) =
      S.ev (S.L A *
        S.R (W * (if b then family.averagedSubMeas.total
          else 1 - family.averagedSubMeas.total) * W)) := by
  cases b
  · exact (fromHToG_avgOver_head_ev_sandwich params S A W _).trans
      (congrArg (fun T => S.ev (S.L A * S.R (W * T * W))) hincomplete)
  · exact (fromHToG_avgOver_head_ev_sandwich params S A W _).trans
      (congrArg (fun T => S.ev (S.L A * S.R (W * T * W))) hcomplete)

/-- Summing the per-type averaged sandwich totals gives the full tail sandwich
total, hence the identity. -/
theorem fromHToG_sum_averagedSandwichByType_total_eq_one (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (n : ℕ) :
    (∑ τ : GHatType n,
      (averagedSandwichByTypeSubMeas params family n τ).total) = 1 := by
  simp only [fromHToG_averagedSandwichByType_total_eq_type_sum]
  rw [Finset.sum_comm]
  calc ∑ xs ∈ (uniformDistribution (PointTuple params n)).support, ∑ τ : GHatType n,
        (uniformDistribution (PointTuple params n)).weight xs •
          (∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ, (gHatSandwichFamily params family n xs).outcome gs)
      = averageOperatorOverDistribution (uniformDistribution (PointTuple params n))
          (fun _ => (1 : 𝔓)) := by
        refine Finset.sum_congr rfl fun xs _ => ?_
        rw [← Finset.smul_sum, fromHToG_type_filtered_outcome_sum params
            (fun _ gs => (gHatSandwichFamily params family n xs).outcome gs),
          fromHToG_gHatSandwichFamily_sum_eq_one]
    _ = 1 := fromHToG_averageOperator_uniform_const_one _

/-- Averaged first-root context bound for the `S U S` sandwich used in the
second half-sandwich and final move-right Cauchy--Schwarz steps. -/
theorem fromHToG_SUS_context_avg_le_one (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (hcomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total)
    (hincomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total)
    (ℓ n : ℕ) :
    avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
      ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
        let W := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
        let U := (gHatIdxMeas params family q.1).outcome ogs.1
        let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
        S.ev ((S.L T * S.R (W * U)) * star (S.L T * S.R (W * U)))) ≤ 1 := by
  -- The summand, with the head outcome absorbed into the weight sandwich.
  have hterm : ∀ (x : Fq params) (xs : PointTuple params n) (g : GHatOutcome params)
      (gs : GHatTupleOutcome params n) (W : 𝔓), star W = W →
      (let U := (gHatIdxMeas params family x).outcome g
       let T := gHatHalfProductOutcomeOperator params family n xs gs
       S.ev ((S.L T * S.R (W * U)) * star (S.L T * S.R (W * U)))) =
        S.ev (S.L ((gHatSandwichFamily params family n xs).outcome gs) *
          S.R (W * (gHatIdxMeas params family x).outcome g * W)) := by
    intro x xs g gs W hW
    show S.ev (S.opTensor _ _ * star (S.opTensor _ _)) = S.ev (S.opTensor _ _)
    rw [S.conjTranspose_opTensor, S.opTensor_mul, star_mul, hW,
      fromHToG_gHatIdxMeas_outcome_isHermitian, ← mul_assoc, mul_assoc W,
      gHatIdxMeas_proj]
    rfl
  let F : Bool → GHatType n → Fq params → PointTuple params n → ℝ := fun b τ x xs =>
    ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with gHatTupleType gs = τ,
        S.ev (S.L ((gHatSandwichFamily params family n xs).outcome gs) *
          S.R (fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ) *
            (gHatIdxMeas params family x).outcome g *
            fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)))
  rw [← fromHToGAdjacentStage_globalize_pointwiseShape params F
    (fun x xs => ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
        let W := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
        let U := (gHatIdxMeas params family x).outcome ogs.1
        let T := gHatHalfProductOutcomeOperator params family n xs ogs.2
        S.ev ((S.L T * S.R (W * U)) * star (S.L T * S.R (W * U))))
    fun x xs => (fromHToG_bool_type_filtered_outcome_sum params _).trans <|
      (fromHToG_sum_product _).trans <| Fintype.sum_congr _ _ fun ogs =>
        (hterm x xs ogs.1 ogs.2 _ (fromHToGRecurrenceWeight_isHermitian params family ℓ _)).symm]
  -- Each branch is bounded by the averaged sandwich total against the branch average.
  have hbranch : ∀ (b : Bool) (τ : GHatType n),
      (avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs => F b τ x xs) ≤
      S.ev (S.L (averagedSandwichByTypeSubMeas params family n τ).total *
        S.R (if b then family.averagedSubMeas.total else 1 - family.averagedSubMeas.total)) := by
    intro b τ
    set W := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
    have hAτ : 0 ≤ (averagedSandwichByTypeSubMeas params family n τ).total :=
      (averagedSandwichByTypeSubMeas params family n τ).total_nonneg
    calc (avgOver (uniformDistribution (Fq params)) fun x =>
          avgOver (uniformDistribution (PointTuple params n)) fun xs => F b τ x xs)
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            let B := if b then (completePartSubMeas params family x).total
              else (incompletePartSubMeas params family x).total
            S.ev (S.L (averagedSandwichByTypeSubMeas params family n τ).total *
              S.R (W * B * W))) :=
          avgOver_congr _ _ _ fun x => by
            refine (avgOver_congr _ _ _ fun xs => ?_).trans
              (fromHToG_avgOver_tail_type_ev_sandwich params S family n τ _)
            exact Finset.sum_comm.trans <| Finset.sum_congr rfl fun gs _ =>
              fromHToG_ev_sum_isSome_sandwich_weight params S family x b _ W
      _ = S.ev (S.L (averagedSandwichByTypeSubMeas params family n τ).total *
            S.R (W * (if b then family.averagedSubMeas.total
              else 1 - family.averagedSubMeas.total) * W)) :=
          fromHToG_avgOver_head_branch_ev_sandwich params S family hcomplete hincomplete b _ W
      _ ≤ _ := by
          refine fromHToG_ev_leftTensor_rightTensor_mono_right_of_nonneg_left S hAτ ?_
          cases b
          · exact fromHToGRecurrenceWeight_sandwich_one_sub_base_le params family ℓ _
          · exact fromHToGRecurrenceWeight_sandwich_base_le params family ℓ _
  refine (Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun τ _ => hbranch b τ).trans_eq ?_
  rw [Finset.sum_comm]
  calc ∑ τ : GHatType n, ∑ b : Bool,
        S.ev (S.L (averagedSandwichByTypeSubMeas params family n τ).total *
          S.R (if b then family.averagedSubMeas.total else 1 - family.averagedSubMeas.total))
      = ∑ τ : GHatType n,
          S.ev (S.L (averagedSandwichByTypeSubMeas params family n τ).total) := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Fintype.sum_bool, ite_eq_left rfl, ite_eq_right Bool.false_ne_true, ← S.ev_add,
          ← mul_add, ← fromHToG_rightTensor_add, add_sub_cancel, S.rightTensor_one, mul_one]
    _ = 1 := by
        rw [← S.ev_sum, S.leftTensor_finset_sum, fromHToG_sum_averagedSandwichByType_total_eq_one,
          S.leftTensor_one, S.ev_one_of_isNormalized]

end MIPRE.LIDT.Co.Pasting

end
