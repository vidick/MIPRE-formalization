/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG/PaperBounds.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.PaperBounds.SandwichContext

@[expose] public section

/-!
# Section 12 pasting: from-H-to-G collapsed bounds

Collapses the paper endpoint `M₄` to the next Lean stage and records the scalar bounds used by
the final telescope: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperBounds.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The slice family is an `IdxPolyFamily params 𝔓`, so the completed-slice outcomes, the
half-products and the recurrence weights are local operators in `𝔓` (the vendored `Op ι`), and
`ᴴ` is `star`. The vendored bipartite state `ψbi : QuantumState (ι × ι)` both places and
evaluates, so it is the symmetric model `S : SymModel 𝔓 K`, in the vendored argument position;
`leftTensor`/`rightTensor` are `S.L`/`S.R`, and the vendored `qSDDCore ψbi` is `S.qSDDCore`, the
vector-state defect read through the parent `VecState`. No lemma here has a swap, density or
normalization hypothesis.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq PointTuple uniformDistribution avgOver avgOver_congr
  avgOver_uniform_equiv)
open MIPStarRE.LDT.Pasting (GHatType GHatOutcome GHatTupleOutcome SliceQuestion prependTypeBit
  gHatTupleType commuteGHalfSandwichError commuteGHalfSandwichError_mono_length
  gHatSelfConsistencyError fromHToGPointTupleReverseEquiv fromHToGGHatTupleOutcomeReverseEquiv)
open MIPRE.LIDT.Co (SymModel IdxSubMeas IdxPolyFamily averageOperatorOverDistribution)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The branch-averaged recurrence expression that `M₄` collapses to: for each tail type `τ`,
the averaged sandwich total against the two recurrence weights times the branch averages
`G` and `1 - G`. -/
noncomputable def fromHToGAdjacentStageCollapsed (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (k ℓ : ℕ) : ℝ :=
  let n := k - (ℓ + 1)
  ∑ τ : GHatType n,
    S.ev (S.L (averagedSandwichByTypeSubMeas params family n τ).total *
      S.R (fromHToGRecurrenceWeight params family ℓ (prependTypeBit true τ) *
            family.averagedSubMeas.total +
          fromHToGRecurrenceWeight params family ℓ (prependTypeBit false τ) *
            (1 - family.averagedSubMeas.total)))

/-- The collapsed branch expression is exactly the next Lean stage. -/
theorem fromHToGAdjacentStageCollapsed_eq_stage_succ (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (hstageExact : FromHToGAdjacentStageExactFacts params S family) (k ℓ : ℕ) :
    fromHToGAdjacentStageCollapsed params S family k ℓ =
      fromHToGStageMass params S family k (ℓ + 1) :=
  Finset.sum_congr rfl fun τ _ => (hstageExact.tailWeightRecurrence ℓ τ).symm

/-- `M₄` collapses exactly to the branch-averaged recurrence expression. -/
theorem fromHToGAdjacentStageM4_eq_collapsed (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (hcomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total)
    (hincomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total)
    (k ℓ : ℕ) :
    fromHToGAdjacentStageM4 params S family k ℓ =
      fromHToGAdjacentStageCollapsed params S family k ℓ := by
  -- Each branch: collapse the head outcome, fold the tail, then average the head branch.
  have hbranch : ∀ (b : Bool) (τ : GHatType (k - (ℓ + 1))),
      (avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params (k - (ℓ + 1)))) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params (k - (ℓ + 1)))) with
                gHatTupleType gs = τ,
              let W := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family (k - (ℓ + 1)) xs gs
              S.ev (S.L (T * star T) * S.R (W * U * U))) =
        S.ev (S.L (averagedSandwichByTypeSubMeas params family (k - (ℓ + 1)) τ).total *
          S.R (fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ) *
            if b then family.averagedSubMeas.total
            else 1 - family.averagedSubMeas.total)) := fun b τ =>
    (avgOver_congr _ _ _ fun x =>
      (avgOver_congr _ _ _ fun xs =>
        fromHToGAdjacentStageM4_head_sum params S family ℓ _ b τ x xs).trans
        (fromHToG_avgOver_tail_type_ev params S family _ τ _)).trans
      (fromHToG_avgOver_head_branch_ev params S family hcomplete hincomplete b _ _)
  refine Finset.sum_comm.trans <| Finset.sum_congr rfl fun τ _ =>
    (Fintype.sum_bool _).trans <| (congrArg₂ (· + ·) (hbranch true τ) (hbranch false τ)).trans ?_
  rw [← S.ev_add, ← mul_add, ← fromHToG_rightTensor_add]
  rfl

/-- Raw `qSDDCore` form of the half-sandwich commutation hypothesis after
splitting a nonempty sandwich into its head and tail, with the error weakened to
the ambient length `k`. -/
theorem fromHToG_headTail_qSDDCore_bound (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params S family gamma zeta j)
    {n k : ℕ} (hn : 2 ≤ n + 1) (hnk : n + 1 ≤ k) :
    avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
      S.qSDDCore
        (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
          S.L ((gHatIdxMeas params family q.1).outcome ogs.1 *
            gHatHalfProductOutcomeOperator params family n q.2 ogs.2))
        (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
          S.L (gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
            (gHatIdxMeas params family q.1).outcome ogs.1))) ≤
      commuteGHalfSandwichError params gamma zeta k := by
  have hsplit := (commuteGHalfSandwich_split_iff params S family n
    (commuteGHalfSandwichError params gamma zeta (n + 1))).1 (hhalf (n + 1) hn).repeatedCommutation
  refine le_trans (le_of_eq_of_le ?_ hsplit.squaredDistanceBound)
    (commuteGHalfSandwichError_mono_length params gamma zeta hgamma_nonneg hzeta_nonneg hnk)
  exact avgOver_congr _ _ _ fun q =>
    congrArg₂ S.qSDDCore (funext fun _ => map_mul S.L _ _) (funext fun _ => map_mul S.L _ _)

/-- The completed self-consistency estimate used in the first and final move-right
steps, after adjoining an irrelevant uniform suffix-question register. -/
theorem fromHToG_selfConsistency_qSDDCore_bound (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (zeta : ℝ)
    (hcompleted :
      S.SDDRel
        (uniformDistribution (SliceQuestion params))
        (gHatSelfConsistencyLeftFamily S params family)
        (gHatSelfConsistencyRightFamily S params family)
        (gHatSelfConsistencyError zeta))
    {n : ℕ} :
    avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
      S.qSDDCore
        (fun g : GHatOutcome params => S.L ((gHatIdxMeas params family q.1).outcome g))
        (fun g : GHatOutcome params => S.R ((gHatIdxMeas params family q.1).outcome g))) ≤
      2 * zeta :=
  (sddOpRel_uniform_fst (β := PointTuple params n) S.toVecState _ _ _
    (gHatSelfConsistency_sddOpRel params S family zeta hcompleted)).squaredDistanceBound

/-- Adjoint-oriented raw `qSDDCore` form of the half-sandwich commutation
hypothesis.  This is the orientation used by the paper's Cauchy--Schwarz
decompositions in `eq:call-this-later` and `eq:call-again-later-part-dos`. -/
theorem fromHToG_headTail_adjoint_qSDDCore_bound (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params S family gamma zeta j)
    {n k : ℕ} (hn : 2 ≤ n + 1) (hnk : n + 1 ≤ k) :
    avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
      S.qSDDCore
        (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
          S.L (star (gHatHalfProductOutcomeOperator params family n q.2 ogs.2) *
            (gHatIdxMeas params family q.1).outcome ogs.1))
        (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
          S.L ((gHatIdxMeas params family q.1).outcome ogs.1 *
            star (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)))) ≤
      commuteGHalfSandwichError params gamma zeta k := by
  let eQ : (Fq params × PointTuple params n) ≃ (Fq params × PointTuple params n) :=
    (Equiv.refl _).prodCongr (fromHToGPointTupleReverseEquiv params n)
  let eO : (GHatOutcome params × GHatTupleOutcome params n) ≃
      (GHatOutcome params × GHatTupleOutcome params n) :=
    (Equiv.refl _).prodCongr (fromHToGGHatTupleOutcomeReverseEquiv params n)
  refine le_of_eq_of_le ?_ (fromHToG_headTail_qSDDCore_bound params S family gamma zeta
    hgamma_nonneg hzeta_nonneg hhalf hn hnk)
  -- Swap the two families, then reverse the tail outcomes and finally the tail points.
  refine Eq.trans ?_ (avgOver_uniform_equiv eQ.symm _).symm
  refine avgOver_congr _ _ _ fun q => (fromHToG_qSDDCore_symm S.toVecState _ _).trans ?_
  exact Fintype.sum_equiv eO _ _ fun ogs =>
    congrArg (fun T => S.ev (star (S.L ((gHatIdxMeas params family q.1).outcome ogs.1 * T) -
        S.L (T * (gHatIdxMeas params family q.1).outcome ogs.1)) *
      (S.L ((gHatIdxMeas params family q.1).outcome ogs.1 * T) -
        S.L (T * (gHatIdxMeas params family q.1).outcome ogs.1))))
      (fromHToG_gHatHalfProduct_reverse_eq_adjoint params family n q.2 ogs.2).symm

end MIPRE.LIDT.Co.Pasting

end
