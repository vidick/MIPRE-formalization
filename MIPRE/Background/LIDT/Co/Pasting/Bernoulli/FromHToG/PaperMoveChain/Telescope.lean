/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG/PaperMoveChain/Telescope.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.PaperMoveChain.Moves

@[expose] public section

/-!
# Section 12 pasting: from-H-to-G paper telescope

Assembles the adjacent-stage paper move chain `A → M₁ → M₂ → M₃ → E` and records the final
stage-mass telescope for the `fromHToG` reduction: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperMoveChain/Telescope.lean` in
the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position; `leftTensor`/`rightTensor` are
`S.L`/`S.R`, `ᴴ` is `star`, and the vendored weight operator, also named `S`, is `W`. The three
lemmas take the normalization hypothesis `hnorm : ψbi.IsNormalized`, used only to feed
`closenessOfIP`, `closenessOfIPAdjoint` and the two paper moves of `Moves`, whose ported forms
drop it; it is dropped here as well (section "Port conventions"), so vendored callers pass
`strategy.state` where they passed `ψbi hnorm`. No lemma has a swap or density hypothesis.

The two Cauchy--Schwarz context bounds (`A → M₁` and `M₁ → M₂`) are proved with the keystone's
placement positivity (`S.opTensor_nonneg`, `S.opTensor_le_leftTensor`, `S.opTensor_mono_right`)
and the projectivity `gHatIdxMeas_proj` of the completed outcomes, in place of the vendored
Kronecker and `sq_le_self` chains.

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
  commuteGHalfSandwichError fromHToGRecurrenceError fromHToGPaperTotalError abs_sub_le_four
  fromHToG_sum_product)
open MIPRE.LIDT.Co (SymModel IdxPolyFamily Measurement)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- One adjacent `fromHToG` paper step. -/
theorem fromHToGAdjacentStage_paperMoveChain (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hfacts : GHatFactsStatement params S family gamma zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params S family gamma zeta j)
    (hstageExact : FromHToGAdjacentStageExactFacts params S family)
    (k ℓ : ℕ) (hℓ : ℓ < k) :
    |fromHToGStageMass params S family k ℓ -
        fromHToGStageMass params S family k (ℓ + 1)| ≤
      fromHToGRecurrenceError params gamma zeta k := by
  -- The completed outcomes are self-adjoint projections summing to the identity, and the tail
  -- sandwich outcomes sum to the identity.
  have hUsa : ∀ (x : Fq params) (g : GHatOutcome params),
      star ((gHatIdxMeas params family x).outcome g) = (gHatIdxMeas params family x).outcome g :=
    fromHToG_gHatIdxMeas_outcome_isHermitian params family
  have hLUsa : ∀ (x : Fq params) (g : GHatOutcome params),
      IsSelfAdjoint (S.L ((gHatIdxMeas params family x).outcome g)) := fun x g =>
    (S.leftTensor_conjTranspose _).trans (congrArg S.L (hUsa x g))
  have hTT : ∀ (n : ℕ) (xs : PointTuple params n),
      ∑ gs : GHatTupleOutcome params n, gHatHalfProductOutcomeOperator params family n xs gs *
        star (gHatHalfProductOutcomeOperator params family n xs gs) = 1 :=
    fromHToG_gHatSandwichFamily_sum_eq_one params family
  -- `A → M₁`: move the head outcome to the right register (paper lines 1472--1478).
  have hA₁ : |fromHToGStageMass params S family k ℓ -
      fromHToGAdjacentStageM1 params S family k ℓ| ≤ Real.sqrt (2 * zeta) := by
    rw [fromHToGStageMass_eq_adjacentStageA0 params S family hℓ]
    have h₀ : fromHToGAdjacentStageA0 params S family k ℓ = _ :=
      fromHToGAdjacentStageA0_eq_leftShape params S family k ℓ
    have h₁ : fromHToGAdjacentStageM1 params S family k ℓ = _ :=
      fromHToGAdjacentStageM1_eq_rightShape params S family k ℓ
    rw [h₀, h₁]
    generalize k - (ℓ + 1) = n
    let C : Fq params × PointTuple params n → GHatOutcome params →
        GHatTupleOutcome params n → K →L[ℂ] K := fun q g gs =>
      S.L ((gHatIdxMeas params family q.1).outcome g *
          gHatHalfProductOutcomeOperator params family n q.2 gs *
          star (gHatHalfProductOutcomeOperator params family n q.2 gs)) *
        S.R (fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs)))
    -- The first root (`eq:call-again-later-part-tres`): the context is `L(U) · Y` with
    -- `0 ≤ Y ≤ 1` the suffix `Ĥ ⊗ S` block, so its square is dominated by `L(U)`.
    have hC : ∀ q : Fq params × PointTuple params n,
        ∑ g : GHatOutcome params, (∑ gs : GHatTupleOutcome params n, C q g gs) *
          star (∑ gs : GHatTupleOutcome params n, C q g gs) ≤ 1 := by
      intro q
      let Y : GHatOutcome params → K →L[ℂ] K := fun g =>
        ∑ gs : GHatTupleOutcome params n,
          S.L (gHatHalfProductOutcomeOperator params family n q.2 gs *
              star (gHatHalfProductOutcomeOperator params family n q.2 gs)) *
            S.R (fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs)))
      have hY0 : ∀ g, 0 ≤ Y g := fun g => Finset.sum_nonneg fun gs _ =>
        S.opTensor_nonneg (mul_star_self_nonneg _) (fromHToGRecurrenceWeight_nonneg _ _ _ _)
      have hY1 : ∀ g, Y g ≤ 1 := fun g => by
        calc Y g ≤ ∑ gs : GHatTupleOutcome params n,
              S.L (gHatHalfProductOutcomeOperator params family n q.2 gs *
                star (gHatHalfProductOutcomeOperator params family n q.2 gs)) :=
              Finset.sum_le_sum fun gs _ => S.opTensor_le_leftTensor (mul_star_self_nonneg _)
                (fromHToGRecurrenceWeight_le_one _ _ _ _)
          _ = 1 := by rw [S.leftTensor_finset_sum, hTT, S.leftTensor_one]
      have hsplit : ∀ g, ∑ gs : GHatTupleOutcome params n, C q g gs =
          S.L ((gHatIdxMeas params family q.1).outcome g) * Y g := fun g => by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun gs _ => ?_
        rw [← mul_assoc, S.leftTensor_mul_leftTensor, ← mul_assoc]
      calc ∑ g : GHatOutcome params, (∑ gs : GHatTupleOutcome params n, C q g gs) *
            star (∑ gs : GHatTupleOutcome params n, C q g gs)
          ≤ ∑ g : GHatOutcome params, S.L ((gHatIdxMeas params family q.1).outcome g) :=
            Finset.sum_le_sum fun g _ => by
              rw [hsplit, star_mul, (IsSelfAdjoint.of_nonneg (hY0 g)).star_eq, (hLUsa _ g).star_eq,
                mul_assoc, ← mul_assoc (Y g)]
              calc S.L ((gHatIdxMeas params family q.1).outcome g) * (Y g * Y g *
                    S.L ((gHatIdxMeas params family q.1).outcome g))
                  = S.L ((gHatIdxMeas params family q.1).outcome g) * (Y g * Y g) *
                      S.L ((gHatIdxMeas params family q.1).outcome g) := (mul_assoc _ _ _).symm
                _ ≤ S.L ((gHatIdxMeas params family q.1).outcome g) * 1 *
                      S.L ((gHatIdxMeas params family q.1).outcome g) :=
                    IsSelfAdjoint.conjugate_le_conjugate
                      ((sq_le_self (hY0 g) (hY1 g)).trans (hY1 g)) (hLUsa _ g)
                _ = S.L ((gHatIdxMeas params family q.1).outcome g) := by
                    rw [mul_one, S.leftTensor_mul_leftTensor, gHatIdxMeas_proj]
        _ = 1 := by
            rw [S.leftTensor_finset_sum, Measurement.sum_eq, S.leftTensor_one]
    exact Preliminaries.closenessOfIP S.toVecState
      (uniformDistribution (Fq params × PointTuple params n))
      (uniformDistribution_weight_sum_le_one _)
      (fun q g => S.L ((gHatIdxMeas params family q.1).outcome g))
      (fun q g => S.R ((gHatIdxMeas params family q.1).outcome g)) C (2 * zeta)
      (fromHToG_selfConsistency_qSDDCore_bound params S family zeta
        hfacts.completedSelfConsistency) hC
  -- `M₁ → M₂`: the first half-sandwich commutation (paper lines 1495--1550).
  have h₁₂ : |fromHToGAdjacentStageM1 params S family k ℓ -
      fromHToGAdjacentStageM2 params S family k ℓ| ≤
        Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
    have h₁ : fromHToGAdjacentStageM1 params S family k ℓ = _ :=
      fromHToGAdjacentStageM1_eq_halfSandwichLeftShape params S family k ℓ
    have h₂ : fromHToGAdjacentStageM2 params S family k ℓ = _ :=
      fromHToGAdjacentStageM2_eq_halfSandwichRightShape params S family k ℓ
    rw [h₁, h₂]
    have hnk : k - (ℓ + 1) = 0 ∨ k - (ℓ + 1) + 1 ≤ k := by omega
    generalize k - (ℓ + 1) = n at hnk ⊢
    rcases n with _ | n
    · -- An empty tail: the half-product is the identity and the two scalars agree.
      simp only [gHatHalfProductOutcomeOperator, star_one, mul_one, one_mul, sub_self, abs_zero]
      exact Real.sqrt_nonneg _
    have hnk : n + 1 + 1 ≤ k := hnk.resolve_left (Nat.succ_ne_zero n)
    -- `M₁` and `M₂` are the two adjoint Cauchy--Schwarz scalars, over a one-point register.
    have hsum : ∀ f : GHatOutcome params → GHatTupleOutcome params (n + 1) → ℝ,
        (∑ g, ∑ gs, f g gs) = ∑ ogs : GHatOutcome params × GHatTupleOutcome params (n + 1),
          ∑ _u : Unit, f ogs.1 ogs.2 := fun f =>
      (fromHToG_sum_product f).trans (Fintype.sum_congr _ _ fun ogs =>
        (Fintype.sum_unique fun _ : Unit => f ogs.1 ogs.2).symm)
    let A : Fq params × PointTuple params (n + 1) →
        GHatOutcome params × GHatTupleOutcome params (n + 1) → K →L[ℂ] K := fun q ogs =>
      S.L ((gHatIdxMeas params family q.1).outcome ogs.1 *
        gHatHalfProductOutcomeOperator params family (n + 1) q.2 ogs.2)
    let B : Fq params × PointTuple params (n + 1) →
        GHatOutcome params × GHatTupleOutcome params (n + 1) → K →L[ℂ] K := fun q ogs =>
      S.L (gHatHalfProductOutcomeOperator params family (n + 1) q.2 ogs.2 *
        (gHatIdxMeas params family q.1).outcome ogs.1)
    let C : Fq params × PointTuple params (n + 1) →
        GHatOutcome params × GHatTupleOutcome params (n + 1) → Unit → K →L[ℂ] K :=
      fun q ogs _ => S.L (star (gHatHalfProductOutcomeOperator params family (n + 1) q.2 ogs.2)) *
        S.R (fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2)) *
          (gHatIdxMeas params family q.1).outcome ogs.1)
    -- The second root (`eq:call-this-later`): the adjoint half-sandwich commutator.
    have hAB : avgOver (uniformDistribution (Fq params × PointTuple params (n + 1)))
        (fun q => S.qSDDCore (fun a => star (A q a)) (fun a => star (B q a))) ≤
          commuteGHalfSandwichError params gamma zeta k := by
      refine le_of_eq_of_le (avgOver_congr _ _ _ fun q => congrArg₂ S.qSDDCore
        (funext fun ogs => ?_) (funext fun ogs => ?_))
        (fromHToG_headTail_adjoint_qSDDCore_bound params S family gamma zeta hgamma_nonneg
          hzeta_nonneg hhalf (by omega) hnk)
      · exact (S.leftTensor_conjTranspose _).trans (congrArg S.L (by rw [star_mul, hUsa]))
      · exact (S.leftTensor_conjTranspose _).trans (congrArg S.L (by rw [star_mul, hUsa]))
    -- The first root: `S ≤ I`, projectivity `U² = U`, and the two submeasurements
    -- (paper lines 1531--1550).
    have hC : ∀ q : Fq params × PointTuple params (n + 1),
        ∑ ogs : GHatOutcome params × GHatTupleOutcome params (n + 1),
          star (∑ u : Unit, C q ogs u) * (∑ u : Unit, C q ogs u) ≤ 1 := by
      intro q
      have hterm : ∀ ogs : GHatOutcome params × GHatTupleOutcome params (n + 1),
          star (∑ u : Unit, C q ogs u) * (∑ u : Unit, C q ogs u) ≤
            S.L (gHatHalfProductOutcomeOperator params family (n + 1) q.2 ogs.2 *
                star (gHatHalfProductOutcomeOperator params family (n + 1) q.2 ogs.2)) *
              S.R ((gHatIdxMeas params family q.1).outcome ogs.1) := fun ogs => by
        set T := gHatHalfProductOutcomeOperator params family (n + 1) q.2 ogs.2
        set U := (gHatIdxMeas params family q.1).outcome ogs.1 with hU
        set W := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2)) with hW
        have hWsa : star W = W := fromHToGRecurrenceWeight_isHermitian _ _ _ _
        have hWU : star (W * U) * (W * U) ≤ U := by
          rw [star_mul, hWsa, hU, hUsa, ← hU, mul_assoc, ← mul_assoc W]
          calc U * (W * W * U) = U * (W * W) * U := (mul_assoc _ _ _).symm
            _ ≤ U * 1 * U := IsSelfAdjoint.conjugate_le_conjugate
                ((sq_le_self (fromHToGRecurrenceWeight_nonneg _ _ _ _)
                  (fromHToGRecurrenceWeight_le_one _ _ _ _)).trans
                  (fromHToGRecurrenceWeight_le_one _ _ _ _)) (hUsa q.1 ogs.1)
            _ = U := by rw [mul_one, hU, gHatIdxMeas_proj]
        have hexp : star (∑ u : Unit, C q ogs u) * (∑ u : Unit, C q ogs u) =
            S.L (T * star T) * S.R (star (W * U) * (W * U)) := by
          rw [Fintype.sum_unique, star_mul, S.leftTensor_conjTranspose,
            S.rightTensor_conjTranspose, star_star, mul_assoc, ← mul_assoc (S.L T),
            S.leftTensor_mul_leftTensor, ← mul_assoc, ← (S.L_comm_R _ _).eq, mul_assoc,
            S.rightTensor_mul_rightTensor]
        rw [hexp]
        exact S.opTensor_mono_right (mul_star_self_nonneg T) hWU
      calc ∑ ogs : GHatOutcome params × GHatTupleOutcome params (n + 1),
            star (∑ u : Unit, C q ogs u) * (∑ u : Unit, C q ogs u)
          ≤ ∑ ogs : GHatOutcome params × GHatTupleOutcome params (n + 1),
              S.L (gHatHalfProductOutcomeOperator params family (n + 1) q.2 ogs.2 *
                  star (gHatHalfProductOutcomeOperator params family (n + 1) q.2 ogs.2)) *
                S.R ((gHatIdxMeas params family q.1).outcome ogs.1) :=
            Finset.sum_le_sum fun ogs _ => hterm ogs
        _ = 1 := by
            rw [Fintype.sum_prod_type]
            simp only [← Finset.sum_mul, S.leftTensor_finset_sum, hTT, S.leftTensor_one,
              one_mul]
            rw [S.rightTensor_finset_sum, Measurement.sum_eq, S.rightTensor_one]
    have hcs := Preliminaries.closenessOfIPAdjoint S.toVecState
      (uniformDistribution (Fq params × PointTuple params (n + 1)))
      (uniformDistribution_weight_sum_le_one _) A B C _ hAB hC
    refine le_of_eq_of_le ?_ hcs
    exact congrArg abs (congrArg₂ (· - ·) (avgOver_congr _ _ _ fun _ => hsum _)
      (avgOver_congr _ _ _ fun _ => hsum _))
  -- `M₂ → M₃` and `M₃ → E`: the two moves of `Moves`.
  have h₂₃ := fromHToGAdjacentStageM2M3_paperMove params S family gamma zeta
    hgamma_nonneg hzeta_nonneg hhalf hstageExact k ℓ
  have h₃₄ := fromHToGAdjacentStageM3E_paperMove params S family gamma zeta
    hfacts hstageExact k ℓ
  have htel := abs_sub_le_four (fromHToGStageMass params S family k ℓ)
    (fromHToGAdjacentStageM1 params S family k ℓ) (fromHToGAdjacentStageM2 params S family k ℓ)
    (fromHToGAdjacentStageM3 params S family k ℓ) (fromHToGStageMass params S family k (ℓ + 1))
  have herr : fromHToGRecurrenceError params gamma zeta k =
      2 * Real.sqrt (2 * zeta) + 2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rfl
  rw [herr]
  linarith

/-- Adjacent-stage recurrence obtained by applying the paper move chain at every
nonterminal stage. -/
theorem fromHToG_recurrenceStep_of_paperMoveChain (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hfacts : GHatFactsStatement params S family gamma zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params S family gamma zeta j)
    (hstageExact : FromHToGAdjacentStageExactFacts params S family)
    (k : ℕ) :
    ∀ ℓ : ℕ, ℓ < k →
      |fromHToGStageMass params S family k ℓ -
          fromHToGStageMass params S family k (ℓ + 1)| ≤
        fromHToGRecurrenceError params gamma zeta k :=
  fun ℓ hℓ => fromHToGAdjacentStage_paperMoveChain params S family gamma zeta
    hgamma_nonneg hzeta_nonneg hfacts hhalf hstageExact k ℓ hℓ

/-- The paper-total stage-mass telescope for `fromHToG`.

This follows the iteration in `ld-pasting.tex:1354--1372`: applying the adjacent-stage
estimate over all `k` stages gives `k` copies of the per-stage error.  Lean records
that literal telescope before the final scalar bound `fromHToGPaperTotalError_le`
absorbs it into `fromHToGError`. -/
theorem fromHToG_stageMassTelescope_of_paperMoveChain (params : Parameters)
    [FieldModel params.q] (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (gamma zeta : ℝ) (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hfacts : GHatFactsStatement params S family gamma zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params S family gamma zeta j)
    (hstageExact : FromHToGAdjacentStageExactFacts params S family)
    (k : ℕ) :
    |fromHToGStageMass params S family k 0 -
        fromHToGStageMass params S family k k| ≤
      fromHToGPaperTotalError params gamma zeta k :=
  fromHToGStageMass_telescope params S family gamma zeta k
    (fromHToG_recurrenceStep_of_paperMoveChain params S family gamma zeta
      hgamma_nonneg hzeta_nonneg hfacts hhalf hstageExact k)

end MIPRE.LIDT.Co.Pasting

end
