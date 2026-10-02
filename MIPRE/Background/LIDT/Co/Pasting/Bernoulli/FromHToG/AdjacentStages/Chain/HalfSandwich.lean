/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG/AdjacentStages/Chain/HalfSandwich.lean, to the symmetric model of `planning/c6b-plan.md`;
not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.AdjacentStages.StageA0M1

@[expose] public section

/-!
# Section 12 pasting: from-H-to-G half-sandwich chain

Definitions for `M₂` and `M₃`, and the half-sandwich rewrite lemmas connecting `M₁ → M₂ → M₃`
via approximate commutation of the G-half sandwich: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/AdjacentStages/Chain/HalfSandwich.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The final move-right chain `M₃ → M₄` lives in `Chain.FinalMove`.

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

open MIPStarRE.LDT (Parameters FieldModel Fq PointTuple uniformDistribution avgOver
  avgOver_congr)
open MIPStarRE.LDT.Pasting (GHatType GHatOutcome GHatTupleOutcome prependTypeBit gHatTupleType
  fromHToG_bool_type_filtered_outcome_sum fromHToGAdjacentStage_globalize_pointwiseShape)
open MIPRE.LIDT.Co (SymModel IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The paper's second adjacent-stage intermediate scalar `M₂`: after the first
half-sandwich commutation. -/
noncomputable def fromHToGAdjacentStageM2 (params : Parameters) [FieldModel params.q]
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
              S.ev (S.L (T * U * star T) * S.R (W * U))

/-- The paper's third adjacent-stage intermediate scalar `M₃`: after the second
half-sandwich commutation. -/
noncomputable def fromHToGAdjacentStageM3 (params : Parameters) [FieldModel params.q]
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
              S.ev (S.L (T * star T * U) * S.R (W * U))

/-- Pointwise rewrite of `M₁` to the half-sandwich source shape. -/
theorem fromHToGAdjacentStageM1_pointwise_halfSandwichLeftShape (params : Parameters)
    [FieldModel params.q] (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let W := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          S.ev (S.L (U * T * star T) * S.R (W * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let W := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        S.ev (S.L (U * T) * (S.L (star T) * S.R (W * U))) := by
  rw [fromHToG_bool_type_filtered_outcome_sum]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun gs _ =>
    congrArg S.ev (fromHToG_halfSandwich_left_context_term S _ _ _).symm

/-- Pointwise rewrite of `M₂` to the half-sandwich target shape. -/
theorem fromHToGAdjacentStageM2_pointwise_halfSandwichRightShape (params : Parameters)
    [FieldModel params.q] (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let W := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          S.ev (S.L (T * U * star T) * S.R (W * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let W := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        S.ev (S.L (T * U) * (S.L (star T) * S.R (W * U))) := by
  rw [fromHToG_bool_type_filtered_outcome_sum]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun gs _ =>
    congrArg S.ev (fromHToG_halfSandwich_right_context_term S _ _ _).symm

/-- Pointwise rewrite of `M₂` to the adjoint half-sandwich source shape. -/
theorem fromHToGAdjacentStageM2_pointwise_halfSandwichRightAdjointShape (params : Parameters)
    [FieldModel params.q] (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let W := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          S.ev (S.L (T * U * star T) * S.R (W * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let W := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        S.ev (S.L T * (S.L (U * star T) * S.R (W * U))) := by
  rw [fromHToG_bool_type_filtered_outcome_sum]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun gs _ =>
    congrArg S.ev (fromHToG_halfSandwich_adjoint_right_context_term S _ _ _).symm

/-- Pointwise rewrite of `M₃` to the adjoint half-sandwich target shape. -/
theorem fromHToGAdjacentStageM3_pointwise_halfSandwichLeftAdjointShape (params : Parameters)
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
        S.ev (S.L T * (S.L (star T * U) * S.R (W * U))) := by
  rw [fromHToG_bool_type_filtered_outcome_sum]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun gs _ =>
    congrArg S.ev (fromHToG_halfSandwich_adjoint_left_context_term S _ _ _).symm

/-- Global rewrite of `M₁` to the half-sandwich source shape. -/
theorem fromHToGAdjacentStageM1_eq_halfSandwichLeftShape (params : Parameters)
    [FieldModel params.q] (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM1 params S family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let W := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          S.ev (S.L (U * T) * (S.L (star T) * S.R (W * U))) :=
  fromHToGAdjacentStage_globalize_pointwiseShape params _ _ fun x xs =>
    fromHToGAdjacentStageM1_pointwise_halfSandwichLeftShape params S family ℓ _ x xs

/-- Global rewrite of `M₂` to the half-sandwich target shape. -/
theorem fromHToGAdjacentStageM2_eq_halfSandwichRightShape (params : Parameters)
    [FieldModel params.q] (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM2 params S family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let W := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          S.ev (S.L (T * U) * (S.L (star T) * S.R (W * U))) :=
  fromHToGAdjacentStage_globalize_pointwiseShape params _ _ fun x xs =>
    fromHToGAdjacentStageM2_pointwise_halfSandwichRightShape params S family ℓ _ x xs

/-- Global rewrite of `M₂` to the adjoint half-sandwich source shape. -/
theorem fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointShape (params : Parameters)
    [FieldModel params.q] (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM2 params S family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let W := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          S.ev (S.L T * (S.L (U * star T) * S.R (W * U))) :=
  fromHToGAdjacentStage_globalize_pointwiseShape params _ _ fun x xs =>
    fromHToGAdjacentStageM2_pointwise_halfSandwichRightAdjointShape params S family ℓ _ x xs

/-- Global rewrite of `M₃` to the adjoint half-sandwich target shape. -/
theorem fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointShape (params : Parameters)
    [FieldModel params.q] (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM3 params S family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let W := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          S.ev (S.L T * (S.L (star T * U) * S.R (W * U))) :=
  fromHToGAdjacentStage_globalize_pointwiseShape params _ _ fun x xs =>
    fromHToGAdjacentStageM3_pointwise_halfSandwichLeftAdjointShape params S family ℓ _ x xs

/-- Global rewrite of `M₂` to the left-action adjoint half-sandwich source shape. -/
theorem fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointLeftActionShape
    (params : Parameters) [FieldModel params.q] (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM2 params S family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let W := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          S.ev ((S.L T * S.R (W * U)) * S.L (U * star T)) :=
  (fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointShape params S family k ℓ).trans <|
    avgOver_congr _ _ _ fun _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      congrArg S.ev (fromHToG_halfSandwich_adjoint_right_leftAction_term S _ _ _).symm

/-- Global rewrite of `M₃` to the left-action adjoint half-sandwich target shape. -/
theorem fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointLeftActionShape
    (params : Parameters) [FieldModel params.q] (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM3 params S family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let W := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          S.ev ((S.L T * S.R (W * U)) * S.L (star T * U)) :=
  (fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointShape params S family k ℓ).trans <|
    avgOver_congr _ _ _ fun _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      congrArg S.ev (fromHToG_halfSandwich_adjoint_left_leftAction_term S _ _ _).symm

end MIPRE.LIDT.Co.Pasting

end
