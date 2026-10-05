/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG/AdjacentStages/StageA0M1.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.MoveLemmas.TailStage
public import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.AdjacentStages.StageA0M1

@[expose] public section

/-!
# Section 12 pasting: from-H-to-G adjacent-stage source scalars

Definitions for the paper's adjacent-stage source scalars `A₀` and `M₁`, together with their shape
rewrites and the supporting move-right and half-sandwich context algebra lemmas: the counterpart
of `MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/AdjacentStages/StageA0M1.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The slice family is an `IdxPolyFamily params 𝔓`, so the completed-slice outcomes, the
half-products and the recurrence weights are local operators in `𝔓` (the vendored `Op ι`), and
`ᴴ` is `star`. The vendored second bipartite state `ψbi : QuantumState (ι × ι)` both places and
evaluates, so it is the symmetric model `S : SymModel 𝔓 K`, in the vendored argument position;
`leftTensor (ι₂ := ι)`/`rightTensor (ι₁ := ι)` are `S.L`/`S.R`. The vendored weight operator,
also named `S` (a `let` in the definitions and shape lemmas, the third explicit argument of the
ten algebra lemmas), is renamed `W`. The ten algebra lemmas read no state in the vendored file,
whose placements are state-free; here the placements belong to the model, so each takes
`(S : SymModel 𝔓 K)` as a new explicit first argument, followed by the vendored `U T W`. No
vendored lemma here has a swap, density or normalization hypothesis.

## Not ported

- `fromHToGAdjacentStage_globalize_pointwiseShape`: classical, imported.

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

/-- The paper's adjacent-stage source scalar `A₀`: the head completed-slice outcome
sandwiches the tail half-product on the left factor, against the recurrence weight on the
right factor. -/
noncomputable def fromHToGAdjacentStageA0 (params : Parameters) [FieldModel params.q]
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
              S.ev (S.L (U * T * star T * U) * S.R W)

/-- A nonterminal Lean stage is exactly the paper's adjacent-stage source scalar. -/
theorem fromHToGStageMass_eq_adjacentStageA0 (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) {k ℓ : ℕ} (hℓ : ℓ < k) :
    fromHToGStageMass params S family k ℓ = fromHToGAdjacentStageA0 params S family k ℓ :=
  (fromHToGStageMass_split_succ params S family hℓ).trans <|
    (Fintype.sum_prod_type _).trans <|
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun τ _ =>
        fromHToGTailStageMass_cons_eq_adjacentStageA0_branch params S family ℓ _ b τ

/-- The paper's first adjacent-stage intermediate scalar `M₁`: the head
completed-slice outcome has been moved to the right tensor factor. -/
noncomputable def fromHToGAdjacentStageM1 (params : Parameters) [FieldModel params.q]
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
              S.ev (S.L (U * T * star T) * S.R (W * U))

/-- Algebra for the left-action term in the first move-right estimate. -/
theorem fromHToG_moveRight_left_term (S : SymModel 𝔓 K) (U T W : 𝔓) :
    (S.L (U * T * star T) * S.R W) * S.L U = S.L (U * T * star T * U) * S.R W := by
  rw [mul_assoc, ← (S.L_comm_R U W).eq, ← mul_assoc, S.leftTensor_mul_leftTensor]

/-- Algebra for the right-action term in the first move-right estimate. -/
theorem fromHToG_moveRight_right_term (S : SymModel 𝔓 K) (U T W : 𝔓) :
    (S.L (U * T * star T) * S.R W) * S.R U = S.L (U * T * star T) * S.R (W * U) := by
  rw [mul_assoc, S.rightTensor_mul_rightTensor]

/-- Algebra for the left-action term in the final move-right estimate. -/
theorem fromHToG_moveRight_final_left_term (S : SymModel 𝔓 K) (U T W : 𝔓) :
    (S.L (T * star T) * S.R (W * U)) * S.L U = S.L (T * star T * U) * S.R (W * U) := by
  rw [mul_assoc, ← (S.L_comm_R U (W * U)).eq, ← mul_assoc, S.leftTensor_mul_leftTensor]

/-- Algebra for the right-action term in the final move-right estimate. -/
theorem fromHToG_moveRight_final_right_term (S : SymModel 𝔓 K) (U T W : 𝔓) :
    (S.L (T * star T) * S.R (W * U)) * S.R U = S.L (T * star T) * S.R (W * U * U) := by
  rw [mul_assoc, S.rightTensor_mul_rightTensor]

/-- Algebra for the `M₁` half-sandwich commutation source term. -/
theorem fromHToG_halfSandwich_left_context_term (S : SymModel 𝔓 K) (U T W : 𝔓) :
    S.L (U * T) * (S.L (star T) * S.R (W * U)) = S.L (U * T * star T) * S.R (W * U) := by
  rw [← mul_assoc, S.leftTensor_mul_leftTensor]

/-- Algebra for the `M₂` half-sandwich commutation target term. -/
theorem fromHToG_halfSandwich_right_context_term (S : SymModel 𝔓 K) (U T W : 𝔓) :
    S.L (T * U) * (S.L (star T) * S.R (W * U)) = S.L (T * U * star T) * S.R (W * U) := by
  rw [← mul_assoc, S.leftTensor_mul_leftTensor]

/-- Algebra for the `M₂` adjoint half-sandwich commutation source term. -/
theorem fromHToG_halfSandwich_adjoint_right_context_term (S : SymModel 𝔓 K) (U T W : 𝔓) :
    S.L T * (S.L (U * star T) * S.R (W * U)) = S.L (T * U * star T) * S.R (W * U) := by
  rw [← mul_assoc, S.leftTensor_mul_leftTensor, ← mul_assoc T]

/-- Algebra for the `M₃` adjoint half-sandwich commutation target term. -/
theorem fromHToG_halfSandwich_adjoint_left_context_term (S : SymModel 𝔓 K) (U T W : 𝔓) :
    S.L T * (S.L (star T * U) * S.R (W * U)) = S.L (T * star T * U) * S.R (W * U) := by
  rw [← mul_assoc, S.leftTensor_mul_leftTensor, ← mul_assoc T]

/-- Normalize the `M₂` adjoint half-sandwich source to `C * A` form. -/
theorem fromHToG_halfSandwich_adjoint_right_leftAction_term (S : SymModel 𝔓 K) (U T W : 𝔓) :
    (S.L T * S.R (W * U)) * S.L (U * star T) =
      S.L T * (S.L (U * star T) * S.R (W * U)) := by
  rw [mul_assoc, ← (S.L_comm_R (U * star T) (W * U)).eq]

/-- Normalize the `M₃` adjoint half-sandwich target to `C * B` form. -/
theorem fromHToG_halfSandwich_adjoint_left_leftAction_term (S : SymModel 𝔓 K) (U T W : 𝔓) :
    (S.L T * S.R (W * U)) * S.L (star T * U) =
      S.L T * (S.L (star T * U) * S.R (W * U)) := by
  rw [mul_assoc, ← (S.L_comm_R (star T * U) (W * U)).eq]

/-- Pointwise rewrite of `A0` to the left-action shape used by `closenessOfIP`. -/
theorem fromHToGAdjacentStageA0_pointwise_leftShape (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let W := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          S.ev (S.L (U * T * star T * U) * S.R W)) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let W := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        S.ev ((S.L (U * T * star T) * S.R W) * S.L U) := by
  rw [fromHToG_bool_type_filtered_outcome_sum]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun gs _ =>
    congrArg S.ev (fromHToG_moveRight_left_term S _ _ _).symm

/-- Pointwise rewrite of `M₁` to the right-action shape used by `closenessOfIP`. -/
theorem fromHToGAdjacentStageM1_pointwise_rightShape (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
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
        S.ev ((S.L (U * T * star T) * S.R W) * S.R U) := by
  rw [fromHToG_bool_type_filtered_outcome_sum]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun gs _ =>
    congrArg S.ev (fromHToG_moveRight_right_term S _ _ _).symm

/-- Global rewrite of `A0` to the left-action shape used by `closenessOfIP`. -/
theorem fromHToGAdjacentStageA0_eq_leftShape (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageA0 params S family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let W := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          S.ev ((S.L (U * T * star T) * S.R W) * S.L U) :=
  fromHToGAdjacentStage_globalize_pointwiseShape params _ _ fun x xs =>
    fromHToGAdjacentStageA0_pointwise_leftShape params S family ℓ _ x xs

/-- Global rewrite of `M₁` to the right-action shape used by `closenessOfIP`. -/
theorem fromHToGAdjacentStageM1_eq_rightShape (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM1 params S family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let W := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          S.ev ((S.L (U * T * star T) * S.R W) * S.R U) :=
  fromHToGAdjacentStage_globalize_pointwiseShape params _ _ fun x xs =>
    fromHToGAdjacentStageM1_pointwise_rightShape params S family ℓ _ x xs

end MIPRE.LIDT.Co.Pasting

end
