/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG/Core/AveragesAndOps.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Statements
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.Weights

@[expose] public section

/-!
# Section 12 pasting: operator averages and projective submeasurement lemmas

Averages over uniform distributions, tensor placement identities, and projective
submeasurement algebraic lemmas for the `fromHToG` reduction: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/AveragesAndOps.lean` in the
port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The slice family is an `IdxPolyFamily params 𝔓`, so its complete and incomplete parts, the
completed slices `\widehat G^x` and the sandwiched family are local operators in `𝔓` (the
vendored `Op ι`). The average of the constant identity reads no state and holds over any ring
with a real module structure, so it serves `𝔓` and `K →L[ℂ] K` alike (vendored callers that
name `(ι := ι)` write `(R := 𝔓)`). The three placement identities take the symmetric model
`S : SymModel 𝔓 K` as their first explicit argument, in place of the vendored named carriers
`(ι₂ := ι)`, `(ι₁ := ι)`, and are `S.L`/`S.R` facts: the conjugate transpose of a left placement
is `star (S.L A) = S.L (star A)`, which is not `@[simp]` (it would loop with `map_star`). In the
two expectation-level lemmas the vendored second state `ψbi : QuantumState (ι × ι)` both places
and evaluates, so it is the model `S`, in the vendored argument position; the vendored weight
operator, also named `S` there, is renamed `W` in those two lemmas.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq PointTuple uniformDistribution
  uniformDistribution_isProbability)
open MIPStarRE.LDT.Pasting (GHatOutcome GHatTupleOutcome GHatType outcomesByType)
open MIPRE.LIDT.Co (SymModel IdxPolyFamily postprocess averageIdxSubMeas completeSubMeas
  averageOperatorOverDistribution averageOperatorOverDistribution_const_of_isProbability
  averageOperatorOverDistribution_congr)

/-- The uniform average of the constant identity operator is the identity. -/
theorem fromHToG_averageOperator_uniform_const_one {R : Type*} [Ring R] [Module ℝ R]
    (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    averageOperatorOverDistribution (uniformDistribution α) (fun _ : α => (1 : R)) = 1 :=
  averageOperatorOverDistribution_const_of_isProbability
    (uniformDistribution α) (uniformDistribution_isProbability α) 1

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The completed branch of `\widehat G` averages to the operator `G` used in the
Bernoulli recurrence, matching `references/ldt-paper/ld-pasting.tex:1408--1415`
for the `τ_ℓ = 1` case. -/
theorem fromHToG_completePart_average_total_eq (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total :=
  rfl

/-- The incomplete branch of `\widehat G` averages to `I - G`, matching
`references/ldt-paper/ld-pasting.tex:1408--1415` for the `τ_ℓ = 0` case. -/
theorem fromHToG_incompletePart_average_total_eq (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) :
    averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total := by
  rw [← fromHToG_averageOperator_uniform_const_one (R := 𝔓) (Fq params),
    ← fromHToG_completePart_average_total_eq]
  unfold averageOperatorOverDistribution
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => smul_sub _ _ _

/-- A zero-length type restriction of the sandwiched family has total identity.
This isolates the `tailLen = 0` collapse of `outcomesByType`, `restrictSubMeas`,
and the empty half-sandwich product. -/
theorem fromHToG_emptyRestrictedSandwichTotal_eq_one (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (xs : PointTuple params 0)
    (τ : GHatType 0) :
    open Classical in
    (postprocess
      (restrictSubMeas (gHatSandwichFamily params family 0 xs)
        (fun gs => gs ∈ outcomesByType τ))
      (fun _ => ())).total = 1 := by
  simp only [postprocess_total, restrictSubMeas, outcomesByType, IsEmpty.forall_iff,
    Set.ofPred_true, Set.mem_univ, Finset.filter_true, Fintype.sum_unique]
  change gHatHalfProductOutcomeOperator params family 0 xs default *
      star (gHatHalfProductOutcomeOperator params family 0 xs default) = 1
  rw [gHatHalfProductOutcomeOperator, star_one, mul_one]

/-- The empty suffix sandwich has total identity. -/
theorem fromHToG_averagedSandwichByTypeSubMeas_zero_total_eq_one (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (τ : GHatType 0) :
    (averagedSandwichByTypeSubMeas params family 0 τ).total = 1 :=
  (averageOperatorOverDistribution_congr _ _ (fun _ => (1 : 𝔓))
    fun xs => fromHToG_emptyRestrictedSandwichTotal_eq_one params family xs τ).trans
    (fromHToG_averageOperator_uniform_const_one (PointTuple params 0))

/-- Tensor placement collapses to the left factor when the right recurrence weight
is the stage-`0` eligibility indicator. -/
theorem fromHToG_leftTensor_mul_rightTensor_indicator (S : SymModel 𝔓 K) (A : 𝔓) (p : Prop)
    [Decidable p] :
    S.L A * S.R (if p then 1 else 0 : 𝔓) = S.L (if p then A else 0) := by
  by_cases hp : p <;> simp [hp]

/-- Right tensor placement distributes over addition. -/
theorem fromHToG_rightTensor_add (S : SymModel 𝔓 K) (A B : 𝔓) :
    S.R (A + B) = S.R A + S.R B :=
  map_add S.R A B

/-- Conjugate transpose commutes with left tensor placement. -/
theorem fromHToG_leftTensor_conjTranspose (S : SymModel 𝔓 K) (A : 𝔓) :
    star (S.L A) = S.L (star A) :=
  (map_star S.L A).symm

/-- Summing completed outcomes with `isSome = true` gives the complete branch. -/
theorem fromHToG_gHatIdxMeas_sum_isSome_true (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (x : Fq params) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        (gHatIdxMeas params family x).outcome g) =
      (completePartSubMeas params family x).total := by
  rw [Finset.sum_filter, Fintype.sum_option]
  exact (zero_add _).trans (family.meas x).sum_eq_total

/-- Summing completed outcomes with `isSome = false` gives the incomplete branch. -/
theorem fromHToG_gHatIdxMeas_sum_isSome_false (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) (x : Fq params) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        (gHatIdxMeas params family x).outcome g) =
      (incompletePartSubMeas params family x).total := by
  rw [Finset.sum_filter, Fintype.sum_option]
  simp only [Option.isSome_none, Option.isSome_some, ite_true, Bool.true_eq_false, ite_false,
    Finset.sum_const_zero, add_zero]
  rfl

/-- Weighted complete-branch sum after using completed-outcome projectivity. -/
theorem fromHToG_gHatIdxMeas_sum_isSome_true_weight (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (x : Fq params) (S : 𝔓) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        S * (gHatIdxMeas params family x).outcome g *
          (gHatIdxMeas params family x).outcome g) =
      S * (completePartSubMeas params family x).total := by
  simp only [mul_assoc, gHatIdxMeas_proj params family x, ← Finset.mul_sum,
    fromHToG_gHatIdxMeas_sum_isSome_true]

/-- Weighted incomplete-branch sum after using completed-outcome projectivity. -/
theorem fromHToG_gHatIdxMeas_sum_isSome_false_weight (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params 𝔓) (x : Fq params) (S : 𝔓) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        S * (gHatIdxMeas params family x).outcome g *
          (gHatIdxMeas params family x).outcome g) =
      S * (incompletePartSubMeas params family x).total := by
  simp only [mul_assoc, gHatIdxMeas_proj params family x, ← Finset.mul_sum,
    fromHToG_gHatIdxMeas_sum_isSome_false]

/-- Expectation-level weighted complete-branch sum. -/
theorem fromHToG_ev_sum_isSome_true_weight (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (x : Fq params) (A W : 𝔓) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        S.ev (S.L A * S.R (W * (gHatIdxMeas params family x).outcome g *
          (gHatIdxMeas params family x).outcome g))) =
      S.ev (S.L A * S.R (W * (completePartSubMeas params family x).total)) := by
  rw [← S.ev_finset_sum, ← Finset.mul_sum, S.rightTensor_finset_sum,
    fromHToG_gHatIdxMeas_sum_isSome_true_weight]

/-- Expectation-level weighted incomplete-branch sum. -/
theorem fromHToG_ev_sum_isSome_false_weight (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (x : Fq params) (A W : 𝔓) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        S.ev (S.L A * S.R (W * (gHatIdxMeas params family x).outcome g *
          (gHatIdxMeas params family x).outcome g))) =
      S.ev (S.L A * S.R (W * (incompletePartSubMeas params family x).total)) := by
  rw [← S.ev_finset_sum, ← Finset.mul_sum, S.rightTensor_finset_sum,
    fromHToG_gHatIdxMeas_sum_isSome_false_weight]

end MIPRE.LIDT.Co.Pasting

end
