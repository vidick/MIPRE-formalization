/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG/AdjacentStages/Chain/FinalMove.lean, to the symmetric model of `planning/c6b-plan.md`;
not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.AdjacentStages.Chain.HalfSandwich

@[expose] public section

/-!
# Section 12 pasting: from-H-to-G final move-right chain

Definition for `M₄` and the final move-right rewrite lemmas connecting `M₃ → M₄`: the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/AdjacentStages/Chain/FinalMove.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The preceding half-sandwich chain `M₁ → M₂ → M₃` lives in `Chain.HalfSandwich`.

As in `AdjacentStages.StageA0M1`, the vendored state `ψbi : QuantumState (ι × ι)` is the symmetric
model `S : SymModel 𝔓 K`, in the vendored argument position; `leftTensor`/`rightTensor` are
`S.L`/`S.R`, `ᴴ` is `star`, and the vendored weight operator, also named `S`, is renamed `W` in
every `let`. The algebra lemmas of `StageA0M1` take the model as their first argument. No vendored
lemma here has a swap, density or normalization hypothesis.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq PointTuple uniformDistribution avgOver)
open MIPStarRE.LDT.Pasting (GHatType GHatOutcome GHatTupleOutcome prependTypeBit gHatTupleType
  fromHToG_bool_type_filtered_outcome_sum fromHToGAdjacentStage_globalize_pointwiseShape)
open MIPRE.LIDT.Co (SymModel IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Pointwise rewrite of `M₃` to the left-action shape for the final move-right step. -/
theorem fromHToGAdjacentStageM3_pointwise_finalLeftShape (params : Parameters)
    [FieldModel params.q] (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let W := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          S.ev (S.L (T * star T * U) * S.R (W * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let W := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        S.ev ((S.L (T * star T) * S.R (W * U)) * S.L U) := by
  rw [fromHToG_bool_type_filtered_outcome_sum]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun gs _ =>
    congrArg S.ev (fromHToG_moveRight_final_left_term S _ _ _).symm

/-- Pointwise rewrite of `M₄` to the right-action shape for the final move-right step. -/
theorem fromHToGAdjacentStageM4_pointwise_finalRightShape (params : Parameters)
    [FieldModel params.q] (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let W := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          S.ev (S.L (T * star T) * S.R (W * U * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let W := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        S.ev ((S.L (T * star T) * S.R (W * U)) * S.R U) := by
  rw [fromHToG_bool_type_filtered_outcome_sum]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun gs _ =>
    congrArg S.ev (fromHToG_moveRight_final_right_term S _ _ _).symm

/-- The paper endpoint intermediate `M₄`: the head completed-slice outcome has
moved to the right tensor factor. -/
noncomputable def fromHToGAdjacentStageM4 (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (k ℓ : ℕ) : ℝ :=
  let n := k - (ℓ + 1)
  ∑ b : Bool,
    ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let W := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              S.ev (S.L (T * star T) * S.R (W * U * U))

/-- Global rewrite of `M₃` to the left-action shape for the final move-right step. -/
theorem fromHToGAdjacentStageM3_eq_finalLeftShape (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM3 params S family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let W := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          S.ev ((S.L (T * star T) * S.R (W * U)) * S.L U) :=
  fromHToGAdjacentStage_globalize_pointwiseShape params _ _ fun x xs =>
    fromHToGAdjacentStageM3_pointwise_finalLeftShape params S family ℓ _ x xs

/-- Global rewrite of `M₄` to the right-action shape for the final move-right step. -/
theorem fromHToGAdjacentStageM4_eq_finalRightShape (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM4 params S family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let W := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          S.ev ((S.L (T * star T) * S.R (W * U)) * S.R U) :=
  fromHToGAdjacentStage_globalize_pointwiseShape params _ _ fun x xs =>
    fromHToGAdjacentStageM4_pointwise_finalRightShape params S family ℓ _ x xs

end MIPRE.LIDT.Co.Pasting

end
