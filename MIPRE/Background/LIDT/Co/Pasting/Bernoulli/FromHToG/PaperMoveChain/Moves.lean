/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG/PaperMoveChain/Moves.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.PaperBounds

@[expose] public section

/-!
# Section 12 pasting: from-H-to-G paper moves

The two analytic moves in the adjacent-stage paper chain, `M₂ → M₃` and `M₃ → E`: the
Cauchy--Schwarz and collapse steps in `ld-pasting.tex`, immediately before the adjacent-stage
recurrence is assembled. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperMoveChain/Moves.lean` in the
port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position; `leftTensor`/`rightTensor` are
`S.L`/`S.R`, `ᴴ` is `star`, and the vendored weight operator, also named `S`, is renamed `W`.
Both vendored moves take the normalization hypothesis `hnorm : ψbi.IsNormalized`, used only to
feed `fromHToG_closenessOfIP_avgContext` and `fromHToG_SUS_context_avg_le_one`, whose ported
forms drop it; it is dropped here as well (section "Port conventions"), so vendored callers pass
`strategy.state` where they passed `ψbi hnorm`. No lemma has a swap or density hypothesis.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq PointTuple uniformDistribution avgOver avgOver_congr
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Pasting (GHatOutcome GHatTupleOutcome prependTypeBit gHatTupleType
  commuteGHalfSandwichError fromHToG_sum_product)
open MIPRE.LIDT.Co (SymModel IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The second half-sandwich commutation move `M₂ → M₃` in the paper chain. -/
theorem fromHToGAdjacentStageM2M3_paperMove (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params S family gamma zeta j)
    (hstageExact : FromHToGAdjacentStageExactFacts params S family)
    (k ℓ : ℕ) :
    |fromHToGAdjacentStageM2 params S family k ℓ -
        fromHToGAdjacentStageM3 params S family k ℓ| ≤
      Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
  /- Paper lines 1551--1610: the second half-sandwich commutation, by Cauchy--Schwarz against
  the adjoint half-sandwich commutator (`eq:call-again-later-part-dos`), whose first root is
  the `S U S` context bound (`eq:S-sandwich`). -/
  have h₂ : fromHToGAdjacentStageM2 params S family k ℓ = _ :=
    fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointLeftActionShape params S family k ℓ
  have h₃ : fromHToGAdjacentStageM3 params S family k ℓ = _ :=
    fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointLeftActionShape params S family k ℓ
  rw [h₂, h₃]
  have hnk : k - (ℓ + 1) = 0 ∨ k - (ℓ + 1) + 1 ≤ k := by omega
  generalize k - (ℓ + 1) = n at hnk ⊢
  rcases n with _ | n
  · -- An empty tail: the half-product is the identity and the two scalars agree.
    simp only [gHatHalfProductOutcomeOperator, star_one, mul_one, one_mul, sub_self, abs_zero]
    exact Real.sqrt_nonneg _
  have hnk : n + 1 + 1 ≤ k := hnk.resolve_left (Nat.succ_ne_zero n)
  -- `M₂` and `M₃` are the two Cauchy--Schwarz scalars, over a one-point inner register.
  have hsum : ∀ f : GHatOutcome params → GHatTupleOutcome params (n + 1) → ℝ,
      (∑ g, ∑ gs, f g gs) = ∑ ogs : GHatOutcome params × GHatTupleOutcome params (n + 1),
        ∑ _u : Unit, f ogs.1 ogs.2 := fun f =>
    (fromHToG_sum_product f).trans (Fintype.sum_congr _ _ fun ogs =>
      (Fintype.sum_unique fun _ : Unit => f ogs.1 ogs.2).symm)
  let A : Fq params × PointTuple params (n + 1) →
      GHatOutcome params × GHatTupleOutcome params (n + 1) → K →L[ℂ] K := fun q ogs =>
    S.L (star (gHatHalfProductOutcomeOperator params family (n + 1) q.2 ogs.2) *
      (gHatIdxMeas params family q.1).outcome ogs.1)
  let B : Fq params × PointTuple params (n + 1) →
      GHatOutcome params × GHatTupleOutcome params (n + 1) → K →L[ℂ] K := fun q ogs =>
    S.L ((gHatIdxMeas params family q.1).outcome ogs.1 *
      star (gHatHalfProductOutcomeOperator params family (n + 1) q.2 ogs.2))
  let C : Fq params × PointTuple params (n + 1) →
      GHatOutcome params × GHatTupleOutcome params (n + 1) → Unit → K →L[ℂ] K :=
    fun q ogs _ => S.L (gHatHalfProductOutcomeOperator params family (n + 1) q.2 ogs.2) *
      S.R (fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2)) *
        (gHatIdxMeas params family q.1).outcome ogs.1)
  -- The second root: the adjoint half-sandwich commutator.
  have hAB : avgOver (uniformDistribution (Fq params × PointTuple params (n + 1)))
      (fun q => S.qSDDCore (A q) (B q)) ≤ commuteGHalfSandwichError params gamma zeta k :=
    fromHToG_headTail_adjoint_qSDDCore_bound params S family gamma zeta hgamma_nonneg
      hzeta_nonneg hhalf (by omega) hnk
  -- The first root: the `S U S` context bound.
  have hC : avgOver (uniformDistribution (Fq params × PointTuple params (n + 1))) (fun q =>
      ∑ a, S.ev ((∑ b, C q a b) * star (∑ b, C q a b))) ≤ 1 := by
    simpa only [Fintype.sum_unique] using fromHToG_SUS_context_avg_le_one params S family
        hstageExact.completeBranchAverage hstageExact.incompleteBranchAverage ℓ (n + 1)
  have hcs := fromHToG_closenessOfIP_avgContext S.toVecState
    (uniformDistribution (Fq params × PointTuple params (n + 1)))
    (uniformDistribution_weight_sum_le_one _) A B C _ hAB hC
  refine le_of_eq_of_le ?_ hcs
  rw [abs_sub_comm]
  exact congrArg abs (congrArg₂ (· - ·) (avgOver_congr _ _ _ fun _ => hsum _)
    (avgOver_congr _ _ _ fun _ => hsum _))

/-- The final analytic/collapse move `M₃ → E` in the paper chain. -/
theorem fromHToGAdjacentStageM3E_paperMove (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ)
    (hfacts : GHatFactsStatement params S family gamma zeta)
    (hstageExact : FromHToGAdjacentStageExactFacts params S family)
    (k ℓ : ℕ) :
    |fromHToGAdjacentStageM3 params S family k ℓ -
        fromHToGStageMass params S family k (ℓ + 1)| ≤ Real.sqrt (2 * zeta) := by
  /- Paper lines 1648--1661: move the head outcome to the right register by Cauchy--Schwarz
  against the completed self-consistency, then collapse the head projector, average the two
  head branches and apply `eq:S-recurrence` to reach the next Lean stage. -/
  rw [← fromHToGAdjacentStageCollapsed_eq_stage_succ params S family hstageExact k ℓ,
    ← fromHToGAdjacentStageM4_eq_collapsed params S family hstageExact.completeBranchAverage
      hstageExact.incompleteBranchAverage k ℓ]
  have h₃ : fromHToGAdjacentStageM3 params S family k ℓ = _ :=
    fromHToGAdjacentStageM3_eq_finalLeftShape params S family k ℓ
  have h₄ : fromHToGAdjacentStageM4 params S family k ℓ = _ :=
    fromHToGAdjacentStageM4_eq_finalRightShape params S family k ℓ
  rw [h₃, h₄]
  generalize k - (ℓ + 1) = n
  -- Commute the right factor of the context past the adjoint tail.
  have hcomm : ∀ (T X : 𝔓) (Y : K →L[ℂ] K),
      (S.L (T * star T) * S.R X) * Y = (S.L T * S.R X) * (S.L (star T) * Y) := by
    intro T X Y
    rw [← mul_assoc, mul_assoc (S.L T), ← (S.L_comm_R (star T) X).eq, ← mul_assoc,
      S.leftTensor_mul_leftTensor]
  have hsum : ∀ (f : GHatOutcome params → GHatTupleOutcome params n → ℝ)
      (f' : GHatOutcome params × GHatTupleOutcome params n → Unit → ℝ),
      (∀ g gs, f g gs = f' (g, gs) ()) →
      (∑ g, ∑ gs, f g gs) = ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
        ∑ u : Unit, f' ogs u := fun f f' h =>
    (fromHToG_sum_product f).trans (Fintype.sum_congr _ _ fun ogs =>
      (h ogs.1 ogs.2).trans (Fintype.sum_unique _).symm)
  -- The tail sandwich has total mass at most the identity.
  have hD : ∀ (q : Fq params × PointTuple params n) (_g : GHatOutcome params),
      ∑ gs : GHatTupleOutcome params n,
        star (S.L (star (gHatHalfProductOutcomeOperator params family n q.2 gs))) *
          S.L (star (gHatHalfProductOutcomeOperator params family n q.2 gs)) ≤ 1 :=
    fun q _ => le_of_eq <| by
      rw [← S.leftTensor_one, ← fromHToG_gHatSandwichFamily_sum_eq_one params family n q.2,
        ← S.leftTensor_finset_sum]
      refine Finset.sum_congr rfl fun gs _ => ?_
      rw [S.leftTensor_conjTranspose, star_star, S.leftTensor_mul_leftTensor]
      rfl
  let A : Fq params × PointTuple params n →
      GHatOutcome params × GHatTupleOutcome params n → K →L[ℂ] K := fun q ogs =>
    S.L (star (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)) *
      S.L ((gHatIdxMeas params family q.1).outcome ogs.1)
  let B : Fq params × PointTuple params n →
      GHatOutcome params × GHatTupleOutcome params n → K →L[ℂ] K := fun q ogs =>
    S.L (star (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)) *
      S.R ((gHatIdxMeas params family q.1).outcome ogs.1)
  let C : Fq params × PointTuple params n →
      GHatOutcome params × GHatTupleOutcome params n → Unit → K →L[ℂ] K :=
    fun q ogs _ => S.L (gHatHalfProductOutcomeOperator params family n q.2 ogs.2) *
      S.R (fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2)) *
        (gHatIdxMeas params family q.1).outcome ogs.1)
  -- The second root: the completed self-consistency, multiplied by the adjoint tail.
  have hAB : avgOver (uniformDistribution (Fq params × PointTuple params n))
      (fun q => S.qSDDCore (A q) (B q)) ≤ 2 * zeta :=
    Preliminaries.cabApproxDelta S.toVecState
      (uniformDistribution (Fq params × PointTuple params n))
      (fun q g => S.L ((gHatIdxMeas params family q.1).outcome g))
      (fun q g => S.R ((gHatIdxMeas params family q.1).outcome g))
      (fun q _ gs => S.L (star (gHatHalfProductOutcomeOperator params family n q.2 gs)))
      (2 * zeta)
      (fromHToG_selfConsistency_qSDDCore_bound params S family zeta
        hfacts.completedSelfConsistency)
      hD
  -- The first root: the `S U S` context bound.
  have hC : avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
      ∑ a, S.ev ((∑ b, C q a b) * star (∑ b, C q a b))) ≤ 1 := by
    simpa only [Fintype.sum_unique] using fromHToG_SUS_context_avg_le_one params S family
        hstageExact.completeBranchAverage hstageExact.incompleteBranchAverage ℓ n
  have hcs := fromHToG_closenessOfIP_avgContext S.toVecState
    (uniformDistribution (Fq params × PointTuple params n))
    (uniformDistribution_weight_sum_le_one _) A B C _ hAB hC
  refine le_of_eq_of_le ?_ hcs
  exact congrArg abs (congrArg₂ (· - ·)
    (avgOver_congr _ _ _ fun _ => hsum _ _ fun _ _ => congrArg S.ev (hcomm _ _ _))
    (avgOver_congr _ _ _ fun _ => hsum _ _ fun _ _ => congrArg S.ev (hcomm _ _ _)))

end MIPRE.LIDT.Co.Pasting

end
