/-
Copyright (c) 2026 the openai/ten-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/openai/ten-proofs (commit 94bc0feb, 2026-08-01) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: QuantumParallelRepetition.lean
-/
import Mathlib
import MIPRE.Background.Repetition.TenProofs.QuantumParallelRepetition.Part06

-- Part 7 of 8 of upstream's single module `QuantumParallelRepetition.lean`: its lines
-- 53490-62420, cut between top-level `noncomputable section` blocks by
-- scripts/vendor-repetition.py (the Palomar registry caps a Lean file at 10,000 lines).
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset


noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactStrategyStableBobQuestionCode_joint_factor
    {C : Type*} [Fintype C] [DecidableEq C]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (coordinate : Fin n)
    (code : (Fin n → X) → (Fin n → Y) → C)
    (target : C) (question : X) (next : Y)
    (stable : ∀ (xs : Fin n → X)
      (tail : {j : Fin n // j ≠ coordinate} → Y)
      (y y' : Y),
      code xs ((Equiv.funSplitAt coordinate Y).symm (y, tail)) =
        code xs ((Equiv.funSplitAt coordinate Y).symm (y', tail)))
    (determines : ∀ (xs : Fin n → X) (ys : Fin n → Y),
      code xs ys = target → xs coordinate = question) :
    groupedMass
        (fun outcome : ExactOutcome X Y A B n =>
          (code outcome.1 outcome.2.1,
            outcome.2.1 coordinate))
        (strategyEventLaw (G.repeat n) S).weight
        (target, next) =
      G.conditionalYGivenX question next *
        groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            code outcome.1 outcome.2.1)
          (strategyEventLaw (G.repeat n) S).weight target := by
  classical
  rw [exactStrategyQuestionCodeGroupedMass
    G n S (fun xs ys => (code xs ys, ys coordinate))
    (target, next),
    exactStrategyQuestionCodeGroupedMass G n S code target]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xs _
  let split := Equiv.funSplitAt coordinate Y
  have hsplit (f : (Fin n → Y) → ℝ) :
      (∑ ys : Fin n → Y, f ys) =
        ∑ pair : Y × ({j : Fin n // j ≠ coordinate} → Y),
          f (split.symm pair) :=
    (split.symm.sum_comp f).symm
  rw [hsplit
    (fun ys => if (code xs ys, ys coordinate) = (target, next)
      then (G.repeat n).questionWeight xs ys else 0),
    hsplit
      (fun ys => if code xs ys = target
        then (G.repeat n).questionWeight xs ys else 0)]
  simp only [Fintype.sum_prod_type]
  conv_lhs =>
    rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  have same_code (y : Y) :
      code xs (split.symm (y, tail)) =
        code xs (split.symm (next, tail)) :=
    stable xs tail y next
  have same_tail (y : Y) :
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
        G.questionWeight (xs j)
          (split.symm (y, tail) j)) =
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
        G.questionWeight (xs j)
          (split.symm (next, tail) j) :=
    exactRepeatedQuestionTail_splitAt_bob
      G n coordinate xs y next tail
  by_cases compatible :
      code xs (split.symm (next, tail)) = target
  · have hx : xs coordinate = question :=
      determines xs (split.symm (next, tail)) compatible
    have marked (y : Y) : split.symm (y, tail) coordinate = y := by
      simp [split, Equiv.funSplitAt, Equiv.piSplitAt]
    simp_rw [same_code, marked]
    simp only [compatible, Prod.mk.injEq, true_and, ↓reduceIte]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hweight (y : Y) :
        (G.repeat n).questionWeight xs (split.symm (y, tail)) =
          G.questionWeight (xs coordinate) y *
            (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
              G.questionWeight (xs j)
                (split.symm (next, tail) j)) := by
      calc
        (G.repeat n).questionWeight xs (split.symm (y, tail)) =
          G.questionWeight (xs coordinate) y *
            (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
              G.questionWeight (xs j)
                (split.symm (y, tail) j)) := by
            exact exactRepeatedQuestionWeight_splitAt_bob
              G n coordinate xs y tail
        _ = _ := by rw [same_tail y]
    simp_rw [hweight]
    rw [← Finset.sum_mul]
    change
      G.questionWeight (xs coordinate) next * _ =
        G.conditionalYGivenX question next *
          (G.marginalX (xs coordinate) * _)
    rw [hx]
    rw [← G.marginalX_mul_conditionalYGivenX question next]
    ring
  · simp_rw [same_code]
    simp [compatible]

theorem exactRepeatedQuestionWeight_splitAt_alice
    (G : Game X Y A B) (n : ℕ)
    (coordinate : Fin n) (ys : Fin n → Y)
    (x : X) (tail : {j : Fin n // j ≠ coordinate} → X) :
    (G.repeat n).questionWeight
        ((Equiv.funSplitAt coordinate X).symm (x, tail)) ys =
      G.questionWeight x (ys coordinate) *
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
          G.questionWeight
            ((Equiv.funSplitAt coordinate X).symm (x, tail) j)
            (ys j) := by
  classical
  rw [Game.repeat_questionWeight]
  rw [← Finset.mul_prod_erase
    (Finset.univ : Finset (Fin n))
    (fun j : Fin n =>
      G.questionWeight
        ((Equiv.funSplitAt coordinate X).symm (x, tail) j)
        (ys j))
    (Finset.mem_univ coordinate)]
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

theorem exactRepeatedQuestionTail_splitAt_alice
    (G : Game X Y A B) (n : ℕ)
    (coordinate : Fin n) (ys : Fin n → Y)
    (x x' : X) (tail : {j : Fin n // j ≠ coordinate} → X) :
    (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
      G.questionWeight
        ((Equiv.funSplitAt coordinate X).symm (x, tail) j)
        (ys j)) =
    ∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
      G.questionWeight
        ((Equiv.funSplitAt coordinate X).symm (x', tail) j)
        (ys j) := by
  classical
  apply Finset.prod_congr rfl
  intro j hj
  have different : j ≠ coordinate := (Finset.mem_erase.mp hj).1
  simp [Equiv.funSplitAt, Equiv.piSplitAt, different]

theorem exactStrategyStableAliceQuestionCode_joint_factor
    {C : Type*} [Fintype C] [DecidableEq C]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (coordinate : Fin n)
    (code : (Fin n → X) → (Fin n → Y) → C)
    (target : C) (question : Y) (next : X)
    (stable : ∀ (ys : Fin n → Y)
      (tail : {j : Fin n // j ≠ coordinate} → X)
      (x x' : X),
      code ((Equiv.funSplitAt coordinate X).symm (x, tail)) ys =
        code ((Equiv.funSplitAt coordinate X).symm (x', tail)) ys)
    (determines : ∀ (xs : Fin n → X) (ys : Fin n → Y),
      code xs ys = target → ys coordinate = question) :
    groupedMass
        (fun outcome : ExactOutcome X Y A B n =>
          (code outcome.1 outcome.2.1,
            outcome.1 coordinate))
        (strategyEventLaw (G.repeat n) S).weight
        (target, next) =
      G.conditionalXGivenY question next *
        groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            code outcome.1 outcome.2.1)
          (strategyEventLaw (G.repeat n) S).weight target := by
  classical
  rw [exactStrategyQuestionCodeGroupedMass
    G n S (fun xs ys => (code xs ys, xs coordinate))
    (target, next),
    exactStrategyQuestionCodeGroupedMass G n S code target]
  conv_lhs =>
    rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ys _
  let split := Equiv.funSplitAt coordinate X
  have hsplit (f : (Fin n → X) → ℝ) :
      (∑ xs : Fin n → X, f xs) =
        ∑ pair : X × ({j : Fin n // j ≠ coordinate} → X),
          f (split.symm pair) :=
    (split.symm.sum_comp f).symm
  rw [hsplit
    (fun xs => if (code xs ys, xs coordinate) = (target, next)
      then (G.repeat n).questionWeight xs ys else 0),
    hsplit
      (fun xs => if code xs ys = target
        then (G.repeat n).questionWeight xs ys else 0)]
  simp only [Fintype.sum_prod_type]
  conv_lhs =>
    rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  have same_code (x : X) :
      code (split.symm (x, tail)) ys =
        code (split.symm (next, tail)) ys :=
    stable ys tail x next
  have same_tail (x : X) :
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
        G.questionWeight
          (split.symm (x, tail) j) (ys j)) =
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
        G.questionWeight
          (split.symm (next, tail) j) (ys j) :=
    exactRepeatedQuestionTail_splitAt_alice
      G n coordinate ys x next tail
  by_cases compatible :
      code (split.symm (next, tail)) ys = target
  · have hy : ys coordinate = question :=
      determines (split.symm (next, tail)) ys compatible
    have marked (x : X) : split.symm (x, tail) coordinate = x := by
      simp [split, Equiv.funSplitAt, Equiv.piSplitAt]
    simp_rw [same_code, marked]
    simp only [compatible, Prod.mk.injEq, true_and, ↓reduceIte]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hweight (x : X) :
        (G.repeat n).questionWeight (split.symm (x, tail)) ys =
          G.questionWeight x (ys coordinate) *
            (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
              G.questionWeight
                (split.symm (next, tail) j) (ys j)) := by
      calc
        (G.repeat n).questionWeight (split.symm (x, tail)) ys =
          G.questionWeight x (ys coordinate) *
            (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
              G.questionWeight
                (split.symm (x, tail) j) (ys j)) := by
            exact exactRepeatedQuestionWeight_splitAt_alice
              G n coordinate ys x tail
        _ = _ := by rw [same_tail x]
    simp_rw [hweight]
    rw [← Finset.sum_mul]
    change
      G.questionWeight next (ys coordinate) * _ =
        G.conditionalXGivenY question next *
          (G.marginalY (ys coordinate) * _)
    rw [hy]
    rw [← G.marginalY_mul_conditionalXGivenY next question]
    ring
  · simp_rw [same_code]
    simp [compatible]

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactAliceSourceAtomCode
    {n : ℕ} (D : Finset (Fin n)) :
    ExactJointOutcome X Y A B D →
      (SourceRemainingCoordinate D × X) ×
        (ExactHistoryFlag X Y A B D × Y) :=
  fun point =>
    ((point.1.coordinate, point.2.1 point.1.coordinate.val),
      (exactHistoryCode D point,
        point.2.2.1 point.1.coordinate.val))

def exactBobSourceAtomCode
    {n : ℕ} (D : Finset (Fin n)) :
    ExactJointOutcome X Y A B D →
      (SourceRemainingCoordinate D × Y) ×
        (ExactHistoryFlag X Y A B D × X) :=
  fun point =>
    ((point.1.coordinate, point.2.2.1 point.1.coordinate.val),
      (exactHistoryCode D point,
        point.2.1 point.1.coordinate.val))

theorem exactAliceInformationPosterior_eq_jointPushforward
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    exactAliceInformationPosterior G n S D =
      groupedMass
        (exactAliceSourceAtomCode
          (X := X) (Y := Y) (A := A) (B := B) D)
        (exactPostselectedJointLaw G n S D) := by
  classical
  funext target
  unfold exactAliceInformationPosterior
    exactLocallySampleableLaw
    exactSourcePushforward groupedMass
  apply Finset.sum_congr
  · ext point
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change
      (exactLocallySampleableCode D point =
        (exactAliceInformationEquiv
          (X := X) (Y := Y) (A := A) (B := B) D).symm target) ↔
      (exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D)
          (exactLocallySampleableCode D point) = target
    exact
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).apply_eq_iff_eq_symm_apply).symm
  · intro point _
    rfl

theorem exactBobInformationPosterior_eq_jointPushforward
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    exactBobInformationPosterior G n S D =
      groupedMass
        (exactBobSourceAtomCode
          (X := X) (Y := Y) (A := A) (B := B) D)
        (exactPostselectedJointLaw G n S D) := by
  classical
  funext target
  unfold exactBobInformationPosterior
    exactLocallySampleableLaw
    exactSourcePushforward groupedMass
  apply Finset.sum_congr
  · ext point
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change
      (exactLocallySampleableCode D point =
        (exactBobInformationEquiv
          (X := X) (Y := Y) (A := A) (B := B) D).symm target) ↔
      (exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D)
          (exactLocallySampleableCode D point) = target
    exact
      ((exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).apply_eq_iff_eq_symm_apply).symm
  · intro point _
    rfl

theorem exactAliceSourceConditionalInformation_eq_joint_atom_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceConditionalInformation G n S D base =
      ∑ point : ExactJointOutcome X Y A B D,
        exactPostselectedJointLaw G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom :
                ((SourceRemainingCoordinate D × X) ×
                  ExactHistoryFlag X Y A B D) × Y =>
                exactAliceInformationPosterior G n S D
                  (atom.1.1, (atom.1.2, atom.2)))
              ((point.1.coordinate,
                point.2.1 point.1.coordinate.val),
                exactHistoryCode D point))
            (G.conditionalYGivenX
              (point.2.1 point.1.coordinate.val)) := by
  classical
  let posterior := exactAliceInformationPosterior G n S D
  let code := exactAliceSourceAtomCode
    (X := X) (Y := Y) (A := A) (B := B) D
  let joint := exactPostselectedJointLaw G n S D
  let score : (SourceRemainingCoordinate D × X) ×
      (ExactHistoryFlag X Y A B D × Y) → ℝ :=
    fun point =>
      finiteRelativeEntropy
        (jointConditional
          (fun atom :
            ((SourceRemainingCoordinate D × X) ×
              ExactHistoryFlag X Y A B D) × Y =>
            posterior (atom.1.1, (atom.1.2, atom.2)))
          (point.1, point.2.1))
        (G.conditionalYGivenX point.1.2)
  have hsource := exactAliceSourceConditionalInformation_eq_atom_sum
    G n S D remaining positive base
  change
    exactAliceSourceConditionalInformation G n S D base =
      ∑ point, posterior point * score point at hsource
  have hposterior : posterior = groupedMass code joint :=
    exactAliceInformationPosterior_eq_jointPushforward
      G n S D
  calc
    exactAliceSourceConditionalInformation G n S D base =
      ∑ point, posterior point * score point := hsource
    _ = ∑ point : ExactJointOutcome X Y A B D,
        joint point * score (code point) := by
          rw [hposterior]
          exact finiteGroupedExpectation_eq_atom_sum
            code joint score
    _ = _ := rfl

theorem exactBobSourceConditionalInformation_eq_joint_atom_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactBobSourceConditionalInformation G n S D base =
      ∑ point : ExactJointOutcome X Y A B D,
        exactPostselectedJointLaw G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom :
                ((SourceRemainingCoordinate D × Y) ×
                  ExactHistoryFlag X Y A B D) × X =>
                exactBobInformationPosterior G n S D
                  (atom.1.1, (atom.1.2, atom.2)))
              ((point.1.coordinate,
                point.2.2.1 point.1.coordinate.val),
                exactHistoryCode D point))
            (G.conditionalXGivenY
              (point.2.2.1 point.1.coordinate.val)) := by
  classical
  let posterior := exactBobInformationPosterior G n S D
  let code := exactBobSourceAtomCode
    (X := X) (Y := Y) (A := A) (B := B) D
  let joint := exactPostselectedJointLaw G n S D
  let score : (SourceRemainingCoordinate D × Y) ×
      (ExactHistoryFlag X Y A B D × X) → ℝ :=
    fun point =>
      finiteRelativeEntropy
        (jointConditional
          (fun atom :
            ((SourceRemainingCoordinate D × Y) ×
              ExactHistoryFlag X Y A B D) × X =>
            posterior (atom.1.1, (atom.1.2, atom.2)))
          (point.1, point.2.1))
        (G.conditionalXGivenY point.1.2)
  have hsource := exactBobSourceConditionalInformation_eq_atom_sum
    G n S D remaining positive base
  change
    exactBobSourceConditionalInformation G n S D base =
      ∑ point, posterior point * score point at hsource
  have hposterior : posterior = groupedMass code joint :=
    exactBobInformationPosterior_eq_jointPushforward
      G n S D
  calc
    exactBobSourceConditionalInformation G n S D base =
      ∑ point, posterior point * score point := hsource
    _ = ∑ point : ExactJointOutcome X Y A B D,
        joint point * score (code point) := by
          rw [hposterior]
          exact finiteGroupedExpectation_eq_atom_sum
            code joint score
    _ = _ := rfl

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem exactSeedWeight_pos_of_seed
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    0 < exactSeedWeight seed := by
  have nonempty : 0 < Fintype.card M :=
    Fintype.card_pos_iff.mpr ⟨seed.coordinate⟩
  have bits : 0 < Fintype.card (M → Bool) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  have left :
      0 < Fintype.card
        (Equiv.Perm
          {j : M // j ∈
            exactLeft seed.coordinate seed.partition}) :=
    Fintype.card_pos_iff.mpr ⟨Equiv.refl _⟩
  have right :
      0 < Fintype.card
        (Equiv.Perm
          {j : M // j ∈
            exactRight seed.coordinate seed.partition}) :=
    Fintype.card_pos_iff.mpr ⟨Equiv.refl _⟩
  unfold exactSeedWeight
  positivity

theorem jointConditional_product_context_seed
    {K Ω C V : Type*}
    [Fintype K] [Fintype Ω] [Fintype C] [Fintype V]
    (context : K → Ω → C)
    (next : K → Ω → V)
    (seedWeight : K → ℝ)
    (outcomeWeight : Ω → ℝ)
    (seed : K) (target : C)
    (nonzero : seedWeight seed ≠ 0) :
    jointConditional
        (groupedMass
          (fun q : K × Ω =>
            ((q.1, context q.1 q.2), next q.1 q.2))
          (fun q : K × Ω =>
            seedWeight q.1 * outcomeWeight q.2))
        (seed, target) =
      jointConditional
        (groupedMass
          (fun outcome : Ω =>
            (context seed outcome, next seed outcome))
          outcomeWeight)
        target := by
  classical
  have atom (value : V) :
      groupedMass
          (fun q : K × Ω =>
            ((q.1, context q.1 q.2), next q.1 q.2))
          (fun q : K × Ω =>
            seedWeight q.1 * outcomeWeight q.2)
          ((seed, target), value) =
        seedWeight seed *
          groupedMass
            (fun outcome : Ω =>
              (context seed outcome, next seed outcome))
            outcomeWeight (target, value) := by
    calc
      groupedMass
          (fun q : K × Ω =>
            ((q.1, context q.1 q.2), next q.1 q.2))
          (fun q : K × Ω =>
            seedWeight q.1 * outcomeWeight q.2)
          ((seed, target), value) =
        groupedMass
          (fun q : K × Ω =>
            (q.1, (context q.1 q.2, next q.1 q.2)))
          (fun q : K × Ω =>
            seedWeight q.1 * outcomeWeight q.2)
          (seed, (target, value)) := by
            unfold groupedMass
            apply Finset.sum_congr
            · ext q
              simp [and_assoc]
            · intro q _
              rfl
      _ = seedWeight seed *
          groupedMass
            (fun outcome : Ω =>
              (context seed outcome, next seed outcome))
            outcomeWeight (target, value) := by
            exact groupedMass_product_injective_seed
              (fun k : K => k) (fun _ _ equal => equal)
              (fun k outcome =>
                (context k outcome, next k outcome))
              seedWeight outcomeWeight seed (target, value)
  funext value
  unfold jointConditional jointFirstMarginal
  simp_rw [atom]
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ nonzero

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactAliceSourceContextNextPosterior_eq_groupedMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (fun atom :
      ((SourceRemainingCoordinate D × X) ×
        ExactHistoryFlag X Y A B D) × Y =>
      exactAliceInformationPosterior G n S D
        (atom.1.1, (atom.1.2, atom.2))) =
      groupedMass
        (fun point : ExactJointOutcome X Y A B D =>
          (((point.1.coordinate,
              point.2.1 point.1.coordinate.val),
            exactHistoryCode D point),
            point.2.2.1 point.1.coordinate.val))
        (exactPostselectedJointLaw G n S D) := by
  classical
  funext atom
  rcases atom with ⟨⟨⟨coordinate, question⟩, history⟩, next⟩
  rw [exactAliceInformationPosterior_eq_jointPushforward]
  unfold groupedMass
  apply Finset.sum_congr
  · ext point
    simp [exactAliceSourceAtomCode, and_assoc]
  · intro point _
    rfl

theorem exactBobSourceContextNextPosterior_eq_groupedMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (fun atom :
      ((SourceRemainingCoordinate D × Y) ×
        ExactHistoryFlag X Y A B D) × X =>
      exactBobInformationPosterior G n S D
        (atom.1.1, (atom.1.2, atom.2))) =
      groupedMass
        (fun point : ExactJointOutcome X Y A B D =>
          (((point.1.coordinate,
              point.2.2.1 point.1.coordinate.val),
            exactHistoryCode D point),
            point.2.1 point.1.coordinate.val))
        (exactPostselectedJointLaw G n S D) := by
  classical
  funext atom
  rcases atom with ⟨⟨⟨coordinate, question⟩, history⟩, next⟩
  rw [exactBobInformationPosterior_eq_jointPushforward]
  unfold groupedMass
  apply Finset.sum_congr
  · ext point
    simp [exactBobSourceAtomCode, and_assoc]
  · intro point _
    rfl

theorem exactAliceSourcePosteriorConditional_eq_fixedSeedFiber
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (fun atom :
          ((SourceRemainingCoordinate D × X) ×
            ExactHistoryFlag X Y A B D) × Y =>
          exactAliceInformationPosterior G n S D
            (atom.1.1, (atom.1.2, atom.2)))
        ((seed.coordinate, reference.1 seed.coordinate.val),
          exactHistoryCode D (seed, reference)) =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            ((outcome.1 seed.coordinate.val,
              exactHistoryCode D (seed, outcome)),
              outcome.2.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (reference.1 seed.coordinate.val,
          exactHistoryCode D (seed, reference)) := by
  classical
  rw [exactAliceSourceContextNextPosterior_eq_groupedMass]
  have fiber :
      jointConditional
          (groupedMass
            (fun point : ExactJointOutcome X Y A B D =>
              (((point.1.coordinate,
                  point.2.1 point.1.coordinate.val),
                exactHistoryCode D point),
                point.2.2.1 point.1.coordinate.val))
            (exactPostselectedJointLaw G n S D))
          ((seed.coordinate, reference.1 seed.coordinate.val),
            exactHistoryCode D (seed, reference)) =
        jointConditional
          (groupedMass
            (fun point : ExactJointOutcome X Y A B D =>
              ((point.1,
                (point.2.1 point.1.coordinate.val,
                  exactHistoryCode D point)),
                point.2.2.1 point.1.coordinate.val))
            (exactPostselectedJointLaw G n S D))
          (seed,
            (reference.1 seed.coordinate.val,
              exactHistoryCode D (seed, reference))) := by
    apply jointConditional_groupedMass_eq_of_fiber
      (exactPostselectedJointLaw G n S D)
      (fun point : ExactJointOutcome X Y A B D =>
        ((point.1.coordinate,
          point.2.1 point.1.coordinate.val),
          exactHistoryCode D point))
      (fun point : ExactJointOutcome X Y A B D =>
        (point.1,
          (point.2.1 point.1.coordinate.val,
            exactHistoryCode D point)))
      (fun point : ExactJointOutcome X Y A B D =>
        point.2.2.1 point.1.coordinate.val)
      ((seed.coordinate, reference.1 seed.coordinate.val),
        exactHistoryCode D (seed, reference))
      (seed,
        (reference.1 seed.coordinate.val,
          exactHistoryCode D (seed, reference)))
    intro point
    constructor
    · intro same
      have history :
          exactHistoryCode D point =
            exactHistoryCode D (seed, reference) :=
        congrArg Prod.snd same
      have seed_eq : point.1 = seed := by
        simpa only [exactHistoryCode] using
          congrArg
            (fun r : ExactHistoryFlag X Y A B D => r.seed)
            history
      have question :
          point.2.1 point.1.coordinate.val =
            reference.1 seed.coordinate.val :=
        congrArg
          (fun t :
            (SourceRemainingCoordinate D × X) ×
              ExactHistoryFlag X Y A B D => t.1.2)
          same
      exact Prod.ext seed_eq (Prod.ext question history)
    · intro same
      have seed_eq : point.1 = seed := congrArg Prod.fst same
      have question :
          point.2.1 point.1.coordinate.val =
            reference.1 seed.coordinate.val :=
        congrArg
          (fun t : ExactRemainingSeed D ×
            (X × ExactHistoryFlag X Y A B D) => t.2.1)
          same
      have history :
          exactHistoryCode D point =
            exactHistoryCode D (seed, reference) :=
        congrArg
          (fun t : ExactRemainingSeed D ×
            (X × ExactHistoryFlag X Y A B D) => t.2.2)
          same
      apply Prod.ext
      · exact Prod.ext
          (congrArg
            (fun s : ExactRemainingSeed D => s.coordinate)
            seed_eq)
          question
      · exact history
  calc
    _ = jointConditional
          (groupedMass
            (fun point : ExactJointOutcome X Y A B D =>
              ((point.1,
                (point.2.1 point.1.coordinate.val,
                  exactHistoryCode D point)),
                point.2.2.1 point.1.coordinate.val))
            (exactPostselectedJointLaw G n S D))
          (seed,
            (reference.1 seed.coordinate.val,
              exactHistoryCode D (seed, reference))) := fiber
    _ = _ := by
      unfold exactPostselectedJointLaw
      convert (jointConditional_product_context_seed
          (fun (source : ExactRemainingSeed D)
            (outcome : ExactOutcome X Y A B n) =>
            (outcome.1 source.coordinate.val,
              exactHistoryCode D (source, outcome)))
          (fun (source : ExactRemainingSeed D)
            (outcome : ExactOutcome X Y A B n) =>
            outcome.2.1 source.coordinate.val)
          exactSeedWeight
          (repeatedConditionedOutcomeLaw G n S D)
          seed
          (reference.1 seed.coordinate.val,
            exactHistoryCode D (seed, reference))
          (ne_of_gt (exactSeedWeight_pos_of_seed seed))) using 1
      · congr 1
        exact exactGroupedMass_decidableEq_irrel _ _ _ _
      · congr 1
        exact exactGroupedMass_decidableEq_irrel _ _ _ _

theorem exactBobSourcePosteriorConditional_eq_fixedSeedFiber
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (fun atom :
          ((SourceRemainingCoordinate D × Y) ×
            ExactHistoryFlag X Y A B D) × X =>
          exactBobInformationPosterior G n S D
            (atom.1.1, (atom.1.2, atom.2)))
        ((seed.coordinate, reference.2.1 seed.coordinate.val),
          exactHistoryCode D (seed, reference)) =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            ((outcome.2.1 seed.coordinate.val,
              exactHistoryCode D (seed, outcome)),
              outcome.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (reference.2.1 seed.coordinate.val,
          exactHistoryCode D (seed, reference)) := by
  classical
  rw [exactBobSourceContextNextPosterior_eq_groupedMass]
  have fiber :
      jointConditional
          (groupedMass
            (fun point : ExactJointOutcome X Y A B D =>
              (((point.1.coordinate,
                  point.2.2.1 point.1.coordinate.val),
                exactHistoryCode D point),
                point.2.1 point.1.coordinate.val))
            (exactPostselectedJointLaw G n S D))
          ((seed.coordinate, reference.2.1 seed.coordinate.val),
            exactHistoryCode D (seed, reference)) =
        jointConditional
          (groupedMass
            (fun point : ExactJointOutcome X Y A B D =>
              ((point.1,
                (point.2.2.1 point.1.coordinate.val,
                  exactHistoryCode D point)),
                point.2.1 point.1.coordinate.val))
            (exactPostselectedJointLaw G n S D))
          (seed,
            (reference.2.1 seed.coordinate.val,
              exactHistoryCode D (seed, reference))) := by
    apply jointConditional_groupedMass_eq_of_fiber
      (exactPostselectedJointLaw G n S D)
      (fun point : ExactJointOutcome X Y A B D =>
        ((point.1.coordinate,
          point.2.2.1 point.1.coordinate.val),
          exactHistoryCode D point))
      (fun point : ExactJointOutcome X Y A B D =>
        (point.1,
          (point.2.2.1 point.1.coordinate.val,
            exactHistoryCode D point)))
      (fun point : ExactJointOutcome X Y A B D =>
        point.2.1 point.1.coordinate.val)
      ((seed.coordinate, reference.2.1 seed.coordinate.val),
        exactHistoryCode D (seed, reference))
      (seed,
        (reference.2.1 seed.coordinate.val,
          exactHistoryCode D (seed, reference)))
    intro point
    constructor
    · intro same
      have history :
          exactHistoryCode D point =
            exactHistoryCode D (seed, reference) :=
        congrArg Prod.snd same
      have seed_eq : point.1 = seed := by
        simpa only [exactHistoryCode] using
          congrArg
            (fun r : ExactHistoryFlag X Y A B D => r.seed)
            history
      have question :
          point.2.2.1 point.1.coordinate.val =
            reference.2.1 seed.coordinate.val :=
        congrArg
          (fun t :
            (SourceRemainingCoordinate D × Y) ×
              ExactHistoryFlag X Y A B D => t.1.2)
          same
      exact Prod.ext seed_eq (Prod.ext question history)
    · intro same
      have seed_eq : point.1 = seed := congrArg Prod.fst same
      have question :
          point.2.2.1 point.1.coordinate.val =
            reference.2.1 seed.coordinate.val :=
        congrArg
          (fun t : ExactRemainingSeed D ×
            (Y × ExactHistoryFlag X Y A B D) => t.2.1)
          same
      have history :
          exactHistoryCode D point =
            exactHistoryCode D (seed, reference) :=
        congrArg
          (fun t : ExactRemainingSeed D ×
            (Y × ExactHistoryFlag X Y A B D) => t.2.2)
          same
      apply Prod.ext
      · exact Prod.ext
          (congrArg
            (fun s : ExactRemainingSeed D => s.coordinate)
            seed_eq)
          question
      · exact history
  calc
    _ = jointConditional
          (groupedMass
            (fun point : ExactJointOutcome X Y A B D =>
              ((point.1,
                (point.2.2.1 point.1.coordinate.val,
                  exactHistoryCode D point)),
                point.2.1 point.1.coordinate.val))
            (exactPostselectedJointLaw G n S D))
          (seed,
            (reference.2.1 seed.coordinate.val,
              exactHistoryCode D (seed, reference))) := fiber
    _ = _ := by
      unfold exactPostselectedJointLaw
      convert (jointConditional_product_context_seed
          (fun (source : ExactRemainingSeed D)
            (outcome : ExactOutcome X Y A B n) =>
            (outcome.2.1 source.coordinate.val,
              exactHistoryCode D (source, outcome)))
          (fun (source : ExactRemainingSeed D)
            (outcome : ExactOutcome X Y A B n) =>
            outcome.1 source.coordinate.val)
          exactSeedWeight
          (repeatedConditionedOutcomeLaw G n S D)
          seed
          (reference.2.1 seed.coordinate.val,
            exactHistoryCode D (seed, reference))
          (ne_of_gt (exactSeedWeight_pos_of_seed seed))) using 1
      · congr 1
        exact exactGroupedMass_decidableEq_irrel _ _ _ _
      · congr 1
        exact exactGroupedMass_decidableEq_irrel _ _ _ _

theorem exactReverseAliceMarkedPosteriorConditional_eq_sourcePosterior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : Y)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseAliceMarkedHistoryContext
              G n S D default seed outcome,
              outcome.2.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (fun atom :
          ((SourceRemainingCoordinate D × X) ×
            ExactHistoryFlag X Y A B D) × Y =>
          exactAliceInformationPosterior G n S D
            (atom.1.1, (atom.1.2, atom.2)))
        ((seed.coordinate, reference.1 seed.coordinate.val),
          exactHistoryCode D (seed, reference)) := by
  exact
    (exactReverseAliceMarkedPosteriorConditional_eq_sourceFiber
      G n S D default seed reference).trans
      (exactAliceSourcePosteriorConditional_eq_fixedSeedFiber
        G n S D seed reference).symm

theorem exactReverseBobMarkedPosteriorConditional_eq_sourcePosterior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseBobMarkedHistoryContext
              G n S D default seed outcome,
              outcome.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (fun atom :
          ((SourceRemainingCoordinate D × Y) ×
            ExactHistoryFlag X Y A B D) × X =>
          exactBobInformationPosterior G n S D
            (atom.1.1, (atom.1.2, atom.2)))
        ((seed.coordinate, reference.2.1 seed.coordinate.val),
          exactHistoryCode D (seed, reference)) := by
  exact
    (exactReverseBobMarkedPosteriorConditional_eq_sourceFiber
      G n S D default seed reference).trans
      (exactBobSourcePosteriorConditional_eq_fixedSeedFiber
        G n S D seed reference).symm

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem exactReverseAliceSideWeightedPrefix_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (score : (side : Finset M) →
      ExactForwardSeed M → Fin side.card → ℝ) :
    (∑ side : Finset M,
      reversePartitionWeight side *
        ((∑ marker : Fin side.card,
          ∑ seed : ExactForwardSeed M,
            (exactReverseAliceConditionalSeedLaw
              nonempty side).weight seed *
              score side seed marker) /
          (side.card : ℝ))) =
      ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseLeftSide seed).card,
            score (exactReverseLeftSide seed) seed marker) /
            ((exactReverseLeftSide seed).card : ℝ)) := by
  classical
  calc
    (∑ side : Finset M,
      reversePartitionWeight side *
        ((∑ marker : Fin side.card,
          ∑ seed : ExactForwardSeed M,
            (exactReverseAliceConditionalSeedLaw
              nonempty side).weight seed *
              score side seed marker) /
          (side.card : ℝ))) =
      ∑ side : Finset M,
        ∑ seed : ExactForwardSeed M,
          (reversePartitionWeight side *
            (exactReverseAliceConditionalSeedLaw
              nonempty side).weight seed) *
            ((∑ marker : Fin side.card,
              score side seed marker) / (side.card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro side _
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_div, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro seed _
        ring
    _ = ∑ side : Finset M,
        ∑ seed : ExactForwardSeed M,
          (if exactReverseLeftSide seed = side
           then exactSeedWeight seed else 0) *
            ((∑ marker : Fin side.card,
              score side seed marker) / (side.card : ℝ)) := by
        simp_rw [exactReverseAliceConditionalSeedLaw_weight_cancel
          nonempty]
    _ = ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseLeftSide seed).card,
            score (exactReverseLeftSide seed) seed marker) /
            ((exactReverseLeftSide seed).card : ℝ)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro seed _
        simp

theorem exactReverseBobSideWeightedPrefix_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (score : (side : Finset M) →
      ExactForwardSeed M → Fin side.card → ℝ) :
    (∑ side : Finset M,
      reversePartitionWeight side *
        ((∑ marker : Fin side.card,
          ∑ seed : ExactForwardSeed M,
            (exactReverseBobConditionalSeedLaw
              nonempty side).weight seed *
              score side seed marker) /
          (side.card : ℝ))) =
      ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseRightSide seed).card,
            score (exactReverseRightSide seed) seed marker) /
            ((exactReverseRightSide seed).card : ℝ)) := by
  classical
  calc
    (∑ side : Finset M,
      reversePartitionWeight side *
        ((∑ marker : Fin side.card,
          ∑ seed : ExactForwardSeed M,
            (exactReverseBobConditionalSeedLaw
              nonempty side).weight seed *
              score side seed marker) /
          (side.card : ℝ))) =
      ∑ side : Finset M,
        ∑ seed : ExactForwardSeed M,
          (reversePartitionWeight side *
            (exactReverseBobConditionalSeedLaw
              nonempty side).weight seed) *
            ((∑ marker : Fin side.card,
              score side seed marker) / (side.card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro side _
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_div, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro seed _
        ring
    _ = ∑ side : Finset M,
        ∑ seed : ExactForwardSeed M,
          (if exactReverseRightSide seed = side
           then exactSeedWeight seed else 0) *
            ((∑ marker : Fin side.card,
              score side seed marker) / (side.card : ℝ)) := by
        simp_rw [exactReverseBobConditionalSeedLaw_weight_cancel
          nonempty]
    _ = ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseRightSide seed).card,
            score (exactReverseRightSide seed) seed marker) /
            ((exactReverseRightSide seed).card : ℝ)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro seed _
        simp

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem groupedMass_product_stable_context_fiber
    {K Ω I C V : Type*}
    [Fintype K] [Fintype Ω] [Fintype I] [Fintype C] [Fintype V]
    (index : K → I)
    (context : I → Ω → C)
    (next : I → Ω → V)
    (extract : C → I)
    (extract_context : ∀ (i : I) (outcome : Ω),
      extract (context i outcome) = i)
    (seedWeight : K → ℝ)
    (outcomeWeight : Ω → ℝ)
    (target : C) (value : V) :
    groupedMass
        (fun point : K × Ω =>
          (context (index point.1) point.2,
            next (index point.1) point.2))
        (fun point : K × Ω =>
          seedWeight point.1 * outcomeWeight point.2)
        (target, value) =
      groupedMass index seedWeight (extract target) *
        groupedMass
          (fun outcome : Ω =>
            (context (extract target) outcome,
              next (extract target) outcome))
          outcomeWeight (target, value) := by
  classical
  unfold groupedMass
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro seed _
  by_cases same : index seed = extract target
  · simp [same, Prod.mk.injEq, Finset.mul_sum, mul_ite]
  · have different (outcome : Ω) :
        context (index seed) outcome ≠ target := by
        intro equal
        apply same
        calc
          index seed = extract (context (index seed) outcome) :=
            (extract_context (index seed) outcome).symm
          _ = extract target := congrArg extract equal
    simp [same, different, Prod.mk.injEq]

theorem jointConditional_product_stable_context_seed
    {K Ω I C V : Type*}
    [Fintype K] [Fintype Ω] [Fintype I] [Fintype C] [Fintype V]
    (index : K → I)
    (context : I → Ω → C)
    (next : I → Ω → V)
    (extract : C → I)
    (extract_context : ∀ (i : I) (outcome : Ω),
      extract (context i outcome) = i)
    (seedWeight : K → ℝ)
    (outcomeWeight : Ω → ℝ)
    (seed : K) (target : C)
    (target_index : extract target = index seed)
    (nonzero : groupedMass index seedWeight (index seed) ≠ 0) :
    jointConditional
        (groupedMass
          (fun point : K × Ω =>
            (context (index point.1) point.2,
              next (index point.1) point.2))
          (fun point : K × Ω =>
            seedWeight point.1 * outcomeWeight point.2))
        target =
      jointConditional
        (groupedMass
          (fun outcome : Ω =>
            (context (index seed) outcome,
              next (index seed) outcome))
          outcomeWeight)
        target := by
  classical
  have atom (value : V) :
      groupedMass
          (fun point : K × Ω =>
            (context (index point.1) point.2,
              next (index point.1) point.2))
          (fun point : K × Ω =>
            seedWeight point.1 * outcomeWeight point.2)
          (target, value) =
        groupedMass index seedWeight (index seed) *
          groupedMass
            (fun outcome : Ω =>
              (context (index seed) outcome,
                next (index seed) outcome))
            outcomeWeight (target, value) := by
    simpa only [target_index] using
      groupedMass_product_stable_context_fiber
        index context next extract extract_context
        seedWeight outcomeWeight target value
  funext value
  unfold jointConditional jointFirstMarginal
  simp_rw [atom]
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ nonzero

theorem groupedMass_pos_of_supported_atom
    {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (code : K → I) (weight : K → ℝ)
    (nonnegative : ∀ seed : K, 0 ≤ weight seed)
    (seed : K) (positive : 0 < weight seed) :
    0 < groupedMass code weight (code seed) := by
  unfold groupedMass
  apply lt_of_lt_of_le positive
  apply Finset.single_le_sum
  · intro other _
    exact nonnegative other
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ seed, rfl⟩

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactReverseAliceContextOutcomeProjection
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseAliceFixedInformation X Y D side ×
      (Fin side.card → Y) :=
  (⟨context,
     (fun j => outcome.1 j.val),
     (fun j => outcome.2.1 j.val),
     (fun j => outcome.1 j.val.val),
     (fun j => outcome.2.1 j.val.val),
     (fun j => outcome.1 j.val.val)⟩,
    fun marker =>
      outcome.2.1 (context.sideRank.symm marker).val.val)

def exactReverseBobContextOutcomeProjection
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseBobFixedInformation X Y D side ×
      (Fin side.card → X) :=
  (⟨context,
     (fun j => outcome.1 j.val),
     (fun j => outcome.2.1 j.val),
     (fun j => outcome.2.1 j.val.val),
     (fun j => outcome.1 j.val.val),
     (fun j => outcome.2.1 j.val.val)⟩,
    fun marker =>
      outcome.1 (context.sideRank.symm marker).val.val)

theorem reweightedSeedPrefixNextJoint_as_actual_pushforward
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ}
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (marker : Fin h) :
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixJoint
          seedLaw G n S D projection) =
      groupedMass
        (fun point : K × ExactOutcome X Y A B n =>
          exactPrefixNextCode default marker
            (((projection point).1,
              repeatedConditionedAnswerFlag
                G n S D point.2),
              (projection point).2))
        (reweightedSeedPosterior seedLaw G n S D) := by
  classical
  let augmented :
      K × ExactOutcome X Y A B n →
        (Ω × ConditionedAnswerFlag A B D) ×
          (Fin h → V) :=
    fun point =>
      (((projection point).1,
        repeatedConditionedAnswerFlag G n S D point.2),
        (projection point).2)
  have actual :
      reweightedSeedPrefixJoint
          seedLaw G n S D projection =
        groupedMass augmented
          (reweightedSeedPosterior seedLaw G n S D) := by
    funext target
    exact reweightedSeedPrefixJoint_as_actual_flagged_pushforward
      seedLaw G n S D projection target
  rw [actual]
  exact groupedMass_comp augmented
    (exactPrefixNextCode default marker)
    (reweightedSeedPosterior seedLaw G n S D)

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem groupedMass_productCode_weighted_sum
    {K Ω C : Type*} [Fintype K] [Fintype Ω]
    [Fintype C] [DecidableEq C]
    (code : K → Ω → C)
    (weight : K → ℝ) (mass : Ω → ℝ) (target : C) :
    groupedMass (fun point : K × Ω => code point.1 point.2)
        (fun point : K × Ω => weight point.1 * mass point.2)
        target =
      ∑ index : K, weight index * groupedMass (code index) mass target := by
  classical
  unfold groupedMass
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro index _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  split <;> simp_all

theorem groupedMass_flagSeedOutcome_reassoc
    {F K Ω C : Type*}
    [Fintype F] [Fintype K] [Fintype Ω]
    [Fintype C] [DecidableEq C]
    (code : F → K → Ω → C)
    (flagWeight : F → ℝ) (seedWeight : K → ℝ)
    (outcomeWeight : Ω → ℝ) (target : C) :
    groupedMass
        (fun point : F × (K × Ω) =>
          code point.1 point.2.1 point.2.2)
        (fun point : F × (K × Ω) =>
          flagWeight point.1 *
            (seedWeight point.2.1 * outcomeWeight point.2.2))
        target =
      groupedMass
        (fun point : (F × K) × Ω =>
          code point.1.1 point.1.2 point.2)
        (fun point : (F × K) × Ω =>
          (flagWeight point.1.1 * seedWeight point.1.2) *
            outcomeWeight point.2)
        target := by
  classical
  unfold groupedMass
  simp only [Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (Equiv.prodAssoc F K Ω)
  intro point
  change
    (if code point.1.1 point.1.2 point.2 = target then
      (flagWeight point.1.1 * seedWeight point.1.2) *
        outcomeWeight point.2 else 0) =
    (if code point.1.1 point.1.2 point.2 = target then
      flagWeight point.1.1 *
        (seedWeight point.1.2 * outcomeWeight point.2) else 0)
  split <;> simp [mul_assoc]

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem mixedStableBobQuestionCode_joint_factor
    {K C : Type*} [Fintype K] [Fintype C] [DecidableEq C]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (weight : K → ℝ)
    (coordinate : K → Fin n)
    (code : K → (Fin n → X) → (Fin n → Y) → C)
    (target : C) (question : X) (next : Y)
    (stable : ∀ (index : K) (xs : Fin n → X)
      (tail : {j : Fin n // j ≠ coordinate index} → Y)
      (y y' : Y),
      code index xs
          ((Equiv.funSplitAt (coordinate index) Y).symm (y, tail)) =
        code index xs
          ((Equiv.funSplitAt (coordinate index) Y).symm (y', tail)))
    (determines : ∀ (index : K)
      (xs : Fin n → X) (ys : Fin n → Y),
      code index xs ys = target → xs (coordinate index) = question) :
    groupedMass
        (fun point : K × ExactOutcome X Y A B n =>
          (code point.1 point.2.1 point.2.2.1,
            point.2.2.1 (coordinate point.1)))
        (fun point : K × ExactOutcome X Y A B n =>
          weight point.1 *
            (strategyEventLaw (G.repeat n) S).weight point.2)
        (target, next) =
      G.conditionalYGivenX question next *
        groupedMass
          (fun point : K × ExactOutcome X Y A B n =>
            code point.1 point.2.1 point.2.2.1)
          (fun point : K × ExactOutcome X Y A B n =>
            weight point.1 *
              (strategyEventLaw (G.repeat n) S).weight point.2)
          target := by
  classical
  calc
    groupedMass
        (fun point : K × ExactOutcome X Y A B n =>
          (code point.1 point.2.1 point.2.2.1,
            point.2.2.1 (coordinate point.1)))
        (fun point : K × ExactOutcome X Y A B n =>
          weight point.1 *
            (strategyEventLaw (G.repeat n) S).weight point.2)
        (target, next) =
      ∑ index : K, weight index *
        groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (code index outcome.1 outcome.2.1,
              outcome.2.1 (coordinate index)))
          (strategyEventLaw (G.repeat n) S).weight
          (target, next) :=
      groupedMass_productCode_weighted_sum
        (fun index (outcome : ExactOutcome X Y A B n) =>
          (code index outcome.1 outcome.2.1,
            outcome.2.1 (coordinate index)))
        weight (strategyEventLaw (G.repeat n) S).weight (target, next)
    _ = ∑ index : K, weight index *
        (G.conditionalYGivenX question next *
          groupedMass
            (fun outcome : ExactOutcome X Y A B n =>
              code index outcome.1 outcome.2.1)
            (strategyEventLaw (G.repeat n) S).weight target) := by
      apply Finset.sum_congr rfl
      intro index _
      congr 1
      exact exactStrategyStableBobQuestionCode_joint_factor
        G n S (coordinate index) (code index) target question next
        (stable index) (determines index)
    _ = G.conditionalYGivenX question next *
          (∑ index : K, weight index *
            groupedMass
              (fun outcome : ExactOutcome X Y A B n =>
                code index outcome.1 outcome.2.1)
              (strategyEventLaw (G.repeat n) S).weight target) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      ring
    _ = G.conditionalYGivenX question next *
        groupedMass
          (fun point : K × ExactOutcome X Y A B n =>
            code point.1 point.2.1 point.2.2.1)
          (fun point : K × ExactOutcome X Y A B n =>
            weight point.1 *
              (strategyEventLaw (G.repeat n) S).weight point.2)
          target := by
      congr 1
      exact (groupedMass_productCode_weighted_sum
        (fun index (outcome : ExactOutcome X Y A B n) =>
          code index outcome.1 outcome.2.1)
        weight (strategyEventLaw (G.repeat n) S).weight target).symm

theorem mixedStableAliceQuestionCode_joint_factor
    {K C : Type*} [Fintype K] [Fintype C] [DecidableEq C]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (weight : K → ℝ)
    (coordinate : K → Fin n)
    (code : K → (Fin n → X) → (Fin n → Y) → C)
    (target : C) (question : Y) (next : X)
    (stable : ∀ (index : K) (ys : Fin n → Y)
      (tail : {j : Fin n // j ≠ coordinate index} → X)
      (x x' : X),
      code index
          ((Equiv.funSplitAt (coordinate index) X).symm (x, tail)) ys =
        code index
          ((Equiv.funSplitAt (coordinate index) X).symm (x', tail)) ys)
    (determines : ∀ (index : K)
      (xs : Fin n → X) (ys : Fin n → Y),
      code index xs ys = target → ys (coordinate index) = question) :
    groupedMass
        (fun point : K × ExactOutcome X Y A B n =>
          (code point.1 point.2.1 point.2.2.1,
            point.2.1 (coordinate point.1)))
        (fun point : K × ExactOutcome X Y A B n =>
          weight point.1 *
            (strategyEventLaw (G.repeat n) S).weight point.2)
        (target, next) =
      G.conditionalXGivenY question next *
        groupedMass
          (fun point : K × ExactOutcome X Y A B n =>
            code point.1 point.2.1 point.2.2.1)
          (fun point : K × ExactOutcome X Y A B n =>
            weight point.1 *
              (strategyEventLaw (G.repeat n) S).weight point.2)
          target := by
  classical
  calc
    groupedMass
        (fun point : K × ExactOutcome X Y A B n =>
          (code point.1 point.2.1 point.2.2.1,
            point.2.1 (coordinate point.1)))
        (fun point : K × ExactOutcome X Y A B n =>
          weight point.1 *
            (strategyEventLaw (G.repeat n) S).weight point.2)
        (target, next) =
      ∑ index : K, weight index *
        groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (code index outcome.1 outcome.2.1,
              outcome.1 (coordinate index)))
          (strategyEventLaw (G.repeat n) S).weight
          (target, next) :=
      groupedMass_productCode_weighted_sum
        (fun index (outcome : ExactOutcome X Y A B n) =>
          (code index outcome.1 outcome.2.1,
            outcome.1 (coordinate index)))
        weight (strategyEventLaw (G.repeat n) S).weight (target, next)
    _ = ∑ index : K, weight index *
        (G.conditionalXGivenY question next *
          groupedMass
            (fun outcome : ExactOutcome X Y A B n =>
              code index outcome.1 outcome.2.1)
            (strategyEventLaw (G.repeat n) S).weight target) := by
      apply Finset.sum_congr rfl
      intro index _
      congr 1
      exact exactStrategyStableAliceQuestionCode_joint_factor
        G n S (coordinate index) (code index) target question next
        (stable index) (determines index)
    _ = G.conditionalXGivenY question next *
          (∑ index : K, weight index *
            groupedMass
              (fun outcome : ExactOutcome X Y A B n =>
                code index outcome.1 outcome.2.1)
              (strategyEventLaw (G.repeat n) S).weight target) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      ring
    _ = G.conditionalXGivenY question next *
        groupedMass
          (fun point : K × ExactOutcome X Y A B n =>
            code point.1 point.2.1 point.2.2.1)
          (fun point : K × ExactOutcome X Y A B n =>
            weight point.1 *
              (strategyEventLaw (G.repeat n) S).weight point.2)
          target := by
      congr 1
      exact (groupedMass_productCode_weighted_sum
        (fun index (outcome : ExactOutcome X Y A B n) =>
          code index outcome.1 outcome.2.1)
        weight (strategyEventLaw (G.repeat n) S).weight target).symm

def exactReverseAliceMaskedQuestionRegister
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (xs : Fin n → X) (ys : Fin n → Y) :
    ExactReverseAliceNextContext X Y A B D side :=
  let context := exactReverseAliceContextAt side seed
  let fixed : ExactReverseAliceFixedInformation X Y D side :=
    ⟨context,
      (fun j => xs j.val),
      (fun j => ys j.val),
      (fun j => xs j.val.val),
      (fun j => ys j.val.val),
      (fun j => xs j.val.val)⟩
  finitePrefixMask default marker.castSucc
    ((fixed, flag),
      fun position => ys (context.sideRank.symm position).val.val)

def exactReverseBobMaskedQuestionRegister
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (xs : Fin n → X) (ys : Fin n → Y) :
    ExactReverseBobNextContext X Y A B D side :=
  let context := exactReverseBobContextAt side seed
  let fixed : ExactReverseBobFixedInformation X Y D side :=
    ⟨context,
      (fun j => xs j.val),
      (fun j => ys j.val),
      (fun j => ys j.val.val),
      (fun j => xs j.val.val),
      (fun j => ys j.val.val)⟩
  finitePrefixMask default marker.castSucc
    ((fixed, flag),
      fun position => xs (context.sideRank.symm position).val.val)

theorem exactReverseAliceMaskedQuestionRegister_stable
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (xs : Fin n → X)
    (tail : {j : Fin n //
      j ≠ ((exactReverseAliceContextAt side seed).sideRank.symm
        marker).val.val} → Y)
    (y y' : Y) :
    exactReverseAliceMaskedQuestionRegister
        D side default marker flag seed xs
        ((Equiv.funSplitAt
          ((exactReverseAliceContextAt side seed).sideRank.symm
            marker).val.val Y).symm (y, tail)) =
      exactReverseAliceMaskedQuestionRegister
        D side default marker flag seed xs
        ((Equiv.funSplitAt
          ((exactReverseAliceContextAt side seed).sideRank.symm
            marker).val.val Y).symm (y', tail)) := by
  classical
  let context := exactReverseAliceContextAt side seed
  let marked : SourceRemainingCoordinate D :=
    (context.sideRank.symm marker).val
  let coordinate : Fin n := marked.val
  have outsideD : coordinate ∉ D := by
    exact (Finset.mem_sdiff.mp marked.property).2
  have outsideOther : marked ∉ context.otherSide := by
    rw [context.otherSide_eq_complement]
    simp [marked, (context.sideRank.symm marker).property]
  change
    exactReverseAliceMaskedQuestionRegister
        D side default marker flag seed xs
        ((Equiv.funSplitAt coordinate Y).symm (y, tail)) =
      exactReverseAliceMaskedQuestionRegister
        D side default marker flag seed xs
        ((Equiv.funSplitAt coordinate Y).symm (y', tail))
  unfold exactReverseAliceMaskedQuestionRegister
    finitePrefixMask
  apply Prod.ext
  · apply Prod.ext
    · apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Prod.ext
        · rfl
        apply Prod.ext
        · funext j
          have different : j.val ≠ coordinate := by
            intro same
            exact outsideD (same ▸ j.property)
          simp [Equiv.funSplitAt, Equiv.piSplitAt, different]
        apply Prod.ext
        · rfl
        apply Prod.ext
        · funext j
          have different : j.val.val ≠ coordinate := by
            intro same
            apply outsideOther
            have actual : j.val = marked := by
              apply Subtype.ext
              exact same
            exact actual ▸ j.property
          simp [Equiv.funSplitAt, Equiv.piSplitAt, different]
        · rfl
    · rfl
  · funext position
    by_cases before : position.val < marker.val
    · have different :
          ((context.sideRank.symm position).val.val) ≠ coordinate := by
        intro same
        have sameMarked :
            context.sideRank.symm position =
              context.sideRank.symm marker := by
          apply Subtype.ext
          apply Subtype.ext
          exact same
        have samePosition :=
          context.sideRank.symm.injective sameMarked
        exact (Nat.ne_of_lt before)
          (congrArg Fin.val samePosition)
      simp [before, context, Equiv.funSplitAt,
        Equiv.piSplitAt, different]
    · simp [before]

theorem exactConditionedReverseAliceNextPrior_flagged_mixture
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card) :
    groupedMass (exactPrefixNextCode default marker)
        (exactConditionedReverseAliceNextPrior
          G n S D remaining side) =
      groupedMass
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          (exactReverseAliceMaskedQuestionRegister
            D side default marker point.1.1 point.1.2
            point.2.1 point.2.2.1,
            point.2.2.1
              (((exactReverseAliceContextAt
                side point.1.2).sideRank.symm marker).val.val)))
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          (finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (exactReverseAliceConditionalSeedLaw
              (exactRemainingCoordinate_card_pos
                D remaining) side).weight point.1.2) *
            (strategyEventLaw (G.repeat n) S).weight point.2) := by
  classical
  funext target
  let seedLaw := exactReverseAliceConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseAliceSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  change
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixPrior
          seedLaw G n S D projection) target = _
  calc
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixPrior
          seedLaw G n S D projection) target =
      groupedMass
        (fun point : ConditionedAnswerFlag A B D ×
          (ExactRemainingSeed D ×
            ExactOutcome X Y A B n) =>
          exactPrefixNextCode default marker
            (((projection point.2).1, point.1),
              (projection point.2).2))
        (fun point : ConditionedAnswerFlag A B D ×
          (ExactRemainingSeed D ×
            ExactOutcome X Y A B n) =>
          finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (reweightedSeedPriorEventLaw
              seedLaw G n S).weight point.2)
        target :=
      reweightedSeedPrefixPrior_next_flagged_pushforward
        seedLaw G n S D projection default marker target
    _ = _ := by
      change
        groupedMass
          (fun point : ConditionedAnswerFlag A B D ×
            (ExactRemainingSeed D ×
              ExactOutcome X Y A B n) =>
            (exactReverseAliceMaskedQuestionRegister
              D side default marker point.1 point.2.1
              point.2.2.1 point.2.2.2.1,
              point.2.2.2.1
                (((exactReverseAliceContextAt
                  side point.2.1).sideRank.symm marker).val.val)))
          (fun point : ConditionedAnswerFlag A B D ×
            (ExactRemainingSeed D ×
              ExactOutcome X Y A B n) =>
            finiteUniformWeight
                (ConditionedAnswerFlag A B D) *
              (seedLaw.weight point.2.1 *
                (strategyEventLaw (G.repeat n) S).weight point.2.2))
          target = _
      exact groupedMass_flagSeedOutcome_reassoc
        (fun flag seed (outcome : ExactOutcome X Y A B n) =>
          (exactReverseAliceMaskedQuestionRegister
            D side default marker flag seed outcome.1 outcome.2.1,
            outcome.2.1
              (((exactReverseAliceContextAt
                side seed).sideRank.symm marker).val.val)))
        (fun _ : ConditionedAnswerFlag A B D =>
          finiteUniformWeight
            (ConditionedAnswerFlag A B D))
        seedLaw.weight
        (strategyEventLaw (G.repeat n) S).weight target

theorem exactReverseAliceMaskedQuestionRegister_determines
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (xs : Fin n → X) (ys : Fin n → Y)
    (target : ExactReverseAliceNextContext X Y A B D side)
    (same :
      exactReverseAliceMaskedQuestionRegister
        D side default marker flag seed xs ys = target) :
    xs (((exactReverseAliceContextAt
        side seed).sideRank.symm marker).val.val) =
      target.1.1.2.2.2.1
        (target.1.1.1.sideRank.symm marker) := by
  have actual := congrArg
    (fun context : ExactReverseAliceNextContext
      X Y A B D side =>
      context.1.1.2.2.2.1
        (context.1.1.1.sideRank.symm marker)) same
  exact actual

theorem exactConditionedReverseAliceNextPrior_marked_joint_factor
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (target : ExactReverseAliceNextContext X Y A B D side)
    (next : Y) :
    groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseAliceNextPrior
          G n S D remaining side)
        (target, next) =
      G.conditionalYGivenX
          (target.1.1.2.2.2.1
            (target.1.1.1.sideRank.symm marker)) next *
        jointFirstMarginal
          (groupedMass
            (exactPrefixNextCode default marker)
            (exactConditionedReverseAliceNextPrior
              G n S D remaining side))
          target := by
  classical
  let seedLaw := exactReverseAliceConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let mixedWeight :
      ConditionedAnswerFlag A B D ×
        ExactRemainingSeed D → ℝ :=
    fun index =>
      finiteUniformWeight
        (ConditionedAnswerFlag A B D) *
        seedLaw.weight index.2
  let coordinate :
      ConditionedAnswerFlag A B D ×
        ExactRemainingSeed D → Fin n :=
    fun index =>
      ((exactReverseAliceContextAt
        side index.2).sideRank.symm marker).val.val
  let code :
      (ConditionedAnswerFlag A B D ×
        ExactRemainingSeed D) →
          (Fin n → X) → (Fin n → Y) →
            ExactReverseAliceNextContext X Y A B D side :=
    fun index xs ys =>
      exactReverseAliceMaskedQuestionRegister
        D side default marker index.1 index.2 xs ys
  let question : X :=
    target.1.1.2.2.2.1
      (target.1.1.1.sideRank.symm marker)
  have stable :
      ∀ (index : ConditionedAnswerFlag A B D ×
          ExactRemainingSeed D)
        (xs : Fin n → X)
        (tail : {j : Fin n // j ≠ coordinate index} → Y)
        (y y' : Y),
        code index xs
            ((Equiv.funSplitAt (coordinate index) Y).symm (y, tail)) =
          code index xs
            ((Equiv.funSplitAt (coordinate index) Y).symm (y', tail)) := by
    intro index xs tail y y'
    exact exactReverseAliceMaskedQuestionRegister_stable
      D side default marker index.1 index.2 xs tail y y'
  have determines :
      ∀ (index : ConditionedAnswerFlag A B D ×
          ExactRemainingSeed D)
        (xs : Fin n → X) (ys : Fin n → Y),
        code index xs ys = target →
          xs (coordinate index) = question := by
    intro index xs ys same
    exact exactReverseAliceMaskedQuestionRegister_determines
      D side default marker index.1 index.2 xs ys target same
  have mixed := mixedStableBobQuestionCode_joint_factor
    G n S mixedWeight coordinate code target question next
    stable determines
  rw [exactConditionedReverseAliceNextPrior_flagged_mixture
    G n S D remaining side default marker]
  change
    groupedMass
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          (code point.1 point.2.1 point.2.2.1,
            point.2.2.1 (coordinate point.1)))
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          mixedWeight point.1 *
            (strategyEventLaw (G.repeat n) S).weight point.2)
        (target, next) =
      G.conditionalYGivenX question next *
        jointFirstMarginal
          (groupedMass
            (fun point :
              (ConditionedAnswerFlag A B D ×
                ExactRemainingSeed D) ×
                  ExactOutcome X Y A B n =>
              (code point.1 point.2.1 point.2.2.1,
                point.2.2.1 (coordinate point.1)))
            (fun point :
              (ConditionedAnswerFlag A B D ×
                ExactRemainingSeed D) ×
                  ExactOutcome X Y A B n =>
              mixedWeight point.1 *
                (strategyEventLaw (G.repeat n) S).weight point.2))
          target
  rw [jointFirstMarginal_groupedContextNext]
  convert mixed using 1
  exact congrFun (exactGroupedMass_decidableEq_irrel
    _ _ _ _) (target, next)

theorem exactConditionedReverseAliceNextPrior_marked_conditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (target : ExactReverseAliceNextContext X Y A B D side)
    (supported :
      jointFirstMarginal
        (groupedMass
          (exactPrefixNextCode default marker)
          (exactConditionedReverseAliceNextPrior
            G n S D remaining side))
        target ≠ 0) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default marker)
          (exactConditionedReverseAliceNextPrior
            G n S D remaining side))
        target =
      G.conditionalYGivenX
        (target.1.1.2.2.2.1
          (target.1.1.1.sideRank.symm marker)) := by
  funext next
  unfold jointConditional
  rw [exactConditionedReverseAliceNextPrior_marked_joint_factor
    G n S D remaining side default marker target next]
  exact mul_div_cancel_right₀ _ supported

theorem exactReverseAliceMarkedPriorConditional_eq_game
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : Y)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n)
    (supported :
      jointFirstMarginal
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩))
          (exactConditionedReverseAliceNextPrior
            G n S D remaining
            (exactReverseLeftSide seed)))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) ≠ 0) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩))
          (exactConditionedReverseAliceNextPrior
            G n S D remaining
            (exactReverseLeftSide seed)))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) =
      G.conditionalYGivenX
        (reference.1 seed.coordinate.val) := by
  have actual := exactConditionedReverseAliceNextPrior_marked_conditional
    G n S D remaining
    (exactReverseLeftSide seed) default
    ((exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩)
    (exactReverseAliceMarkedHistoryContext
      G n S D default seed reference) supported
  simpa [exactReverseAliceMarkedHistoryContext,
    finitePrefixMask,
    exactReverseAliceSourceProjection] using actual

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactReverseAliceMaskedOutcomeContext
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseAliceNextContext X Y A B D side :=
  let projection :=
    exactReverseAliceContextOutcomeProjection
      (X := X) (Y := Y) (A := A) (B := B)
      D side context outcome
  finitePrefixMask default marker.castSucc
    ((projection.1,
      repeatedConditionedAnswerFlag G n S D outcome),
      projection.2)

theorem exactReverseAliceMaskedOutcomeContext_extract
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    (exactReverseAliceMaskedOutcomeContext
      G n S D side default marker context outcome).1.1.1 =
      context := by
  rfl

theorem exactConditionedReverseAliceNextJoint_marked_mixture
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card) :
    groupedMass (exactPrefixNextCode default marker)
        (exactConditionedReverseAliceNextJoint
          G n S D remaining side) =
      groupedMass
        (fun point : ExactJointOutcome X Y A B D =>
          (exactReverseAliceMaskedOutcomeContext
            G n S D side default marker
            (exactReverseAliceContextAt side point.1)
            point.2,
            point.2.2.1
              (((exactReverseAliceContextAt
                side point.1).sideRank.symm marker).val.val)))
        (fun point : ExactJointOutcome X Y A B D =>
          (exactReverseAliceConditionalSeedLaw
            (exactRemainingCoordinate_card_pos
              D remaining) side).weight point.1 *
            repeatedConditionedOutcomeLaw G n S D point.2) := by
  classical
  let law := exactReverseAliceConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseAliceSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  change
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixJoint
          law G n S D projection) = _
  rw [reweightedSeedPrefixNextJoint_as_actual_pushforward]
  funext target
  unfold groupedMass
  apply Finset.sum_congr
  · ext point
    simp [exactPrefixNextCode,
      exactReverseAliceMaskedOutcomeContext,
      exactReverseAliceContextOutcomeProjection,
      exactReverseAliceSourceProjection,
      projection]
  · intro point _
    exact reweightedSeedPosterior_eq_product
      law G n S D point

theorem exactReverseAliceActualConditionalSeedWeight_pos
    {n : ℕ} (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (seed : ExactRemainingSeed D) :
    0 <
      (exactReverseAliceConditionalSeedLaw
        (exactRemainingCoordinate_card_pos D remaining)
        (exactReverseLeftSide seed)).weight seed := by
  have side :
      (exactReverseLeftSide seed).Nonempty :=
    ⟨seed.coordinate,
      exactReverseLeftSide_coordinate_mem seed⟩
  rw [exactReverseAliceConditionalSeedLaw_weight
    (exactRemainingCoordinate_card_pos D remaining)
    (exactReverseLeftSide seed) side seed]
  unfold exactReverseAliceConditionalSeedWeight
  simp only [↓reduceIte]
  exact div_pos
    (exactSeedWeight_pos_of_seed seed)
    ((reversePartitionWeight_pos_iff
      (exactRemainingCoordinate_card_pos D remaining)
      (exactReverseLeftSide seed)).mpr side)

theorem exactReverseAliceMaskedOutcomeContext_actual
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : Y)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n) :
    exactReverseAliceMaskedOutcomeContext
        G n S D (exactReverseLeftSide seed) default
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩)
        (exactReverseAliceContextAt
          (exactReverseLeftSide seed) seed)
        outcome =
      exactReverseAliceMarkedHistoryContext
        G n S D default seed outcome := by
  simp [exactReverseAliceMaskedOutcomeContext,
    exactReverseAliceContextOutcomeProjection,
    exactReverseAliceMarkedHistoryContext,
    exactReverseAliceSourceProjection]

theorem exactReverseAliceSideMarkedPosteriorConditional_eq_fixedSeedFiber
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : Y)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩))
          (exactConditionedReverseAliceNextJoint
            G n S D remaining (exactReverseLeftSide seed)))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseAliceMarkedHistoryContext
              G n S D default seed outcome,
              outcome.2.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) := by
  classical
  let side := exactReverseLeftSide seed
  let marker : Fin side.card :=
    (exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
  let law := exactReverseAliceConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let index : ExactRemainingSeed D →
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side :=
    exactReverseAliceContextAt side
  let context :
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side →
          ExactOutcome X Y A B n →
            ExactReverseAliceNextContext X Y A B D side :=
    exactReverseAliceMaskedOutcomeContext
      G n S D side default marker
  let next :
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side →
          ExactOutcome X Y A B n → Y :=
    fun current outcome =>
      outcome.2.1 (current.sideRank.symm marker).val.val
  let extract :
      ExactReverseAliceNextContext X Y A B D side →
        ExactReverseSideContext
          (SourceRemainingCoordinate D) side :=
    fun current => current.1.1.1
  let target := exactReverseAliceMarkedHistoryContext
    G n S D default seed reference
  have extracts : ∀ current outcome,
      extract (context current outcome) = current := by
    intro current outcome
    exact exactReverseAliceMaskedOutcomeContext_extract
      G n S D side default marker current outcome
  have target_index : extract target = index seed := by
    rfl
  have positive :
      0 < groupedMass index law.weight (index seed) := by
    apply groupedMass_pos_of_supported_atom
      index law.weight law.weight_nonneg seed
    exact exactReverseAliceActualConditionalSeedWeight_pos
      D remaining seed
  have stable :=
    jointConditional_product_stable_context_seed
      index context next extract extracts law.weight
      (repeatedConditionedOutcomeLaw G n S D)
      seed target target_index (ne_of_gt positive)
  rw [exactConditionedReverseAliceNextJoint_marked_mixture
    G n S D remaining side default marker]
  change
    jointConditional
        (groupedMass
          (fun point : ExactJointOutcome X Y A B D =>
            (context (index point.1) point.2,
              next (index point.1) point.2))
          (fun point : ExactJointOutcome X Y A B D =>
            law.weight point.1 *
              repeatedConditionedOutcomeLaw
                G n S D point.2))
        target =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseAliceMarkedHistoryContext
              G n S D default seed outcome,
              outcome.2.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        target
  calc
    jointConditional
        (groupedMass
          (fun point : ExactJointOutcome X Y A B D =>
            (context (index point.1) point.2,
              next (index point.1) point.2))
          (fun point : ExactJointOutcome X Y A B D =>
            law.weight point.1 *
              repeatedConditionedOutcomeLaw
                G n S D point.2))
        target =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (context (index seed) outcome,
              next (index seed) outcome))
          (repeatedConditionedOutcomeLaw G n S D))
        target := by
          convert stable using 1
          · congr 1
            exact exactGroupedMass_decidableEq_irrel
              _ _ _ _
          · congr 1
            exact exactGroupedMass_decidableEq_irrel
              _ _ _ _
    _ = jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseAliceMarkedHistoryContext
              G n S D default seed outcome,
              outcome.2.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        target := by
          congr 1
          apply congrArg
            (fun code =>
              groupedMass code
                (repeatedConditionedOutcomeLaw G n S D))
          funext outcome
          apply Prod.ext
          · exact exactReverseAliceMaskedOutcomeContext_actual
              G n S D default seed outcome
          · simp [next, index, side, marker]

theorem exactReverseAliceSideMarkedPosteriorConditional_eq_sourcePosterior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : Y)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩))
          (exactConditionedReverseAliceNextJoint
            G n S D remaining (exactReverseLeftSide seed)))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (fun atom :
          ((SourceRemainingCoordinate D × X) ×
            ExactHistoryFlag X Y A B D) × Y =>
          exactAliceInformationPosterior G n S D
            (atom.1.1, (atom.1.2, atom.2)))
        ((seed.coordinate, reference.1 seed.coordinate.val),
          exactHistoryCode D (seed, reference)) := by
  exact
    (exactReverseAliceSideMarkedPosteriorConditional_eq_fixedSeedFiber
      G n S D remaining default seed reference).trans
      (exactReverseAliceMarkedPosteriorConditional_eq_sourcePosterior
        G n S D default seed reference)

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem reweightedSeedPrefixPriorMarginal_ne_zero_of_positive_atom
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ}
    (law : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (marker : Fin h)
    (point : K × ExactOutcome X Y A B n)
    (atom_positive :
      0 < reweightedSeedPosterior law G n S D point) :
    jointFirstMarginal
        (groupedMass (exactPrefixNextCode default marker)
          (reweightedSeedPrefixPrior
            law G n S D projection))
        (finitePrefixMask default marker.castSucc
          (((projection point).1,
            repeatedConditionedAnswerFlag
              G n S D point.2),
            (projection point).2)) ≠ 0 := by
  classical
  let augmented :
      K × ExactOutcome X Y A B n →
        (Ω × ConditionedAnswerFlag A B D) ×
          (Fin h → V) :=
    fun source =>
      (((projection source).1,
        repeatedConditionedAnswerFlag
          G n S D source.2),
        (projection source).2)
  let target :=
    finitePrefixMask default marker.castSucc
      (augmented point)
  let posterior := reweightedSeedPosterior law G n S D
  let joint := reweightedSeedPrefixJoint
    law G n S D projection
  let prior := reweightedSeedPrefixPrior
    law G n S D projection
  have joint_pushforward : joint = groupedMass augmented posterior := by
    funext outcome
    exact reweightedSeedPrefixJoint_as_actual_flagged_pushforward
      law G n S D projection outcome
  have posterior_nonnegative : ∀ source, 0 ≤ posterior source := by
    intro source
    unfold posterior reweightedSeedPosterior
    apply conditionedEventDistribution_nonneg
    rw [reweightedSeedWinEventMass]
    exact positive
  have masked_posterior_positive :
      0 < groupedMass
        (finitePrefixMask default marker.castSucc)
        joint target := by
    rw [joint_pushforward, groupedMass_comp]
    exact groupedMass_pos_of_supported_atom
      (finitePrefixMask default marker.castSucc ∘ augmented)
      posterior posterior_nonnegative point atom_positive
  intro zero
  have masked_prior_zero :
      groupedMass
        (finitePrefixMask default marker.castSucc)
        prior target = 0 := by
    have first := congrFun
      (exactPrefixNext_firstMarginal
        prior default marker) target
    calc
      groupedMass
          (finitePrefixMask default marker.castSucc)
          prior target =
        jointFirstMarginal
          (groupedMass (exactPrefixNextCode default marker)
            prior) target := by
          convert first.symm using 1
          · exact congrFun
              (exactGroupedMass_decidableEq_irrel
                _ _ (finitePrefixMask
                  default marker.castSucc) prior)
              target
          · exact congrArg
              (fun mass => jointFirstMarginal mass target)
              (exactGroupedMass_decidableEq_irrel
                _ _ (exactPrefixNextCode
                  default marker) prior)
      _ = 0 := zero
  have masked_posterior_zero :
      groupedMass
        (finitePrefixMask default marker.castSucc)
        joint target = 0 :=
    groupedMass_absolute_continuity
      (finitePrefixMask default marker.castSucc)
      joint prior
      (reweightedSeedPrefixPrior_nonneg
        law G n S D positive projection)
      (reweightedSeedPrefix_absolute_continuity
        law G n S D positive projection)
      target masked_prior_zero
  exact (ne_of_gt masked_posterior_positive)
    masked_posterior_zero

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 3072

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactReverseAliceContextMarkerInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : Y)
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  ∑ outcome : ExactOutcome X Y A B n,
    repeatedConditionedOutcomeLaw G n S D outcome *
      finiteRelativeEntropy
        (jointConditional
          (groupedMass
            (exactPrefixNextCode default marker)
            (exactConditionedReverseAliceNextJoint
              G n S D remaining side))
          (exactReverseAliceMaskedOutcomeContext
            G n S D side default marker context outcome))
        (jointConditional
          (groupedMass
            (exactPrefixNextCode default marker)
            (exactConditionedReverseAliceNextPrior
              G n S D remaining side))
          (exactReverseAliceMaskedOutcomeContext
            G n S D side default marker context outcome))

theorem exactReverseAlicePrefixIncrement_eq_contextMarkerInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card) :
    exactConditionedReverseAlicePrefixEntropyIncrement
        G n S D remaining side default marker =
      ∑ seed : ExactRemainingSeed D,
        (exactReverseAliceConditionalSeedLaw
          (exactRemainingCoordinate_card_pos
            D remaining) side).weight seed *
          exactReverseAliceContextMarkerInformation
            G n S D remaining default side
            (exactReverseAliceContextAt side seed) marker := by
  classical
  let law := exactReverseAliceConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseAliceSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  have actual :=
    reweightedSeedPrefixEntropyIncrement_eq_actual_atom_sum
      law G n S D positive projection default marker
  have actual_joint :
      reweightedSeedPrefixJoint
          law G n S D projection =
        exactConditionedReverseAliceNextJoint
          G n S D remaining side := by
    rfl
  have actual_prior :
      reweightedSeedPrefixPrior
          law G n S D projection =
        exactConditionedReverseAliceNextPrior
          G n S D remaining side := by
    rfl
  rw [actual_joint, actual_prior] at actual
  change
    reweightedSeedPrefixEntropyIncrement
        law G n S D projection default marker = _
  rw [actual, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro seed _
  unfold exactReverseAliceContextMarkerInformation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  rw [reweightedSeedPosterior_eq_product]
  have same_context :
      finitePrefixMask default marker.castSucc
          (((projection (seed, outcome)).1,
            repeatedConditionedAnswerFlag
              G n S D outcome),
            (projection (seed, outcome)).2) =
        exactReverseAliceMaskedOutcomeContext
          G n S D side default marker
          (exactReverseAliceContextAt side seed)
          outcome := by
    rfl
  rw [same_context]
  change
    (law.weight seed *
      repeatedConditionedOutcomeLaw G n S D outcome) * _ =
      law.weight seed *
        (repeatedConditionedOutcomeLaw G n S D outcome * _)
  ring

theorem exactReverseAlicePrefixInformation_eq_seedMarkerAverage
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : Y) :
    exactConditionedReverseAlicePrefixInformation
        G n S D remaining default =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseLeftSide seed).card,
            exactReverseAliceContextMarkerInformation
              G n S D remaining default
              (exactReverseLeftSide seed)
              (exactReverseAliceContextAt
                (exactReverseLeftSide seed) seed)
              marker) /
            ((exactReverseLeftSide seed).card : ℝ)) := by
  classical
  calc
    exactConditionedReverseAlicePrefixInformation
        G n S D remaining default =
      ∑ side : Finset (SourceRemainingCoordinate D),
        reversePartitionWeight side *
          ((∑ marker : Fin side.card,
            ∑ seed : ExactRemainingSeed D,
              (exactReverseAliceConditionalSeedLaw
                (exactRemainingCoordinate_card_pos
                  D remaining) side).weight seed *
                exactReverseAliceContextMarkerInformation
                  G n S D remaining default side
                  (exactReverseAliceContextAt side seed)
                  marker) / (side.card : ℝ)) := by
      unfold exactConditionedReverseAlicePrefixInformation
      apply Finset.sum_congr rfl
      intro side _
      congr 1
      apply congrArg (fun total : ℝ => total / (side.card : ℝ))
      apply Finset.sum_congr rfl
      intro marker _
      exact exactReverseAlicePrefixIncrement_eq_contextMarkerInformation
        G n S D remaining positive side default marker
    _ = _ := by
      exact exactReverseAliceSideWeightedPrefix_sum
        (exactRemainingCoordinate_card_pos D remaining)
        (fun side seed marker =>
          exactReverseAliceContextMarkerInformation
            G n S D remaining default side
            (exactReverseAliceContextAt side seed) marker)

theorem exactReverseAlicePrefixInformation_eq_markedSeedAverage
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : Y) :
    exactConditionedReverseAlicePrefixInformation
        G n S D remaining default =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          exactReverseAliceContextMarkerInformation
            G n S D remaining default
            (exactReverseLeftSide seed)
            (exactReverseAliceContext seed)
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩) := by
  classical
  calc
    exactConditionedReverseAlicePrefixInformation
        G n S D remaining default =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseLeftSide seed).card,
            exactReverseAliceContextMarkerInformation
              G n S D remaining default
              (exactReverseLeftSide seed)
              (exactReverseAliceContextAt
                (exactReverseLeftSide seed) seed)
              marker) /
            ((exactReverseLeftSide seed).card : ℝ)) :=
      exactReverseAlicePrefixInformation_eq_seedMarkerAverage
        G n S D remaining positive default
    _ = ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseLeftSide seed).card,
            exactReverseAliceContextMarkerInformation
              G n S D remaining default
              (exactReverseLeftSide seed)
              (exactReverseAliceContext seed)
              marker) /
            ((exactReverseLeftSide seed).card : ℝ)) := by
        simp_rw [exactReverseAliceContextAt_actual]
    _ = _ :=
      exactReverseAliceUniformMarkedSeed_sum
        (exactRemainingCoordinate_card_pos D remaining)
        (fun side context marker =>
          exactReverseAliceContextMarkerInformation
            G n S D remaining default side context marker)

theorem repeatedConditionedOutcomeLaw_pos_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (outcome : ExactOutcome X Y A B n)
    (nonzero : repeatedConditionedOutcomeLaw
      G n S D outcome ≠ 0) :
    0 < repeatedConditionedOutcomeLaw G n S D outcome := by
  have nonnegative :
      0 ≤ repeatedConditionedOutcomeLaw
        G n S D outcome := by
    exact conditionedEventDistribution_nonneg
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive outcome
  exact lt_of_le_of_ne nonnegative nonzero.symm

theorem exactReverseAliceMarkedPriorMarginal_ne_zero_of_outcome
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : Y)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n)
    (outcome_nonzero :
      repeatedConditionedOutcomeLaw G n S D outcome ≠ 0) :
    jointFirstMarginal
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩))
          (exactConditionedReverseAliceNextPrior
            G n S D remaining
            (exactReverseLeftSide seed)))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed outcome) ≠ 0 := by
  classical
  let side := exactReverseLeftSide seed
  let marker : Fin side.card :=
    (exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
  let law := exactReverseAliceConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseAliceSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  have atom_positive :
      0 < reweightedSeedPosterior
        law G n S D (seed, outcome) := by
    rw [reweightedSeedPosterior_eq_product]
    exact mul_pos
      (exactReverseAliceActualConditionalSeedWeight_pos
        D remaining seed)
      (repeatedConditionedOutcomeLaw_pos_of_ne_zero
        G n S D positive outcome outcome_nonzero)
  have supported :=
    reweightedSeedPrefixPriorMarginal_ne_zero_of_positive_atom
      law G n S D positive projection default marker
      (seed, outcome) atom_positive
  simpa [law, projection, side, marker,
    exactConditionedReverseAliceNextPrior,
    exactReverseAliceMarkedHistoryContext,
    exactReverseAliceSourceProjection] using supported

def exactAliceSourceSeedBornInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) : ℝ :=
  ∑ outcome : ExactOutcome X Y A B n,
    repeatedConditionedOutcomeLaw G n S D outcome *
      finiteRelativeEntropy
        (jointConditional
          (fun atom :
            ((SourceRemainingCoordinate D × X) ×
              ExactHistoryFlag X Y A B D) × Y =>
            exactAliceInformationPosterior G n S D
              (atom.1.1, (atom.1.2, atom.2)))
          ((seed.coordinate, outcome.1 seed.coordinate.val),
            exactHistoryCode D (seed, outcome)))
        (G.conditionalYGivenX
          (outcome.1 seed.coordinate.val))

theorem exactReverseAliceMarkedContextInformation_eq_source
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : Y)
    (seed : ExactRemainingSeed D) :
    exactReverseAliceContextMarkerInformation
        G n S D remaining default
        (exactReverseLeftSide seed)
        (exactReverseAliceContext seed)
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩) =
      exactAliceSourceSeedBornInformation
        G n S D seed := by
  classical
  unfold exactReverseAliceContextMarkerInformation
    exactAliceSourceSeedBornInformation
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases zero :
      repeatedConditionedOutcomeLaw G n S D outcome = 0
  · simp [zero]
  · have actual_context :
        exactReverseAliceMaskedOutcomeContext
            G n S D (exactReverseLeftSide seed) default
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩)
            (exactReverseAliceContext seed) outcome =
          exactReverseAliceMarkedHistoryContext
            G n S D default seed outcome := by
        simpa only [exactReverseAliceContextAt_actual] using
          exactReverseAliceMaskedOutcomeContext_actual
            G n S D default seed outcome
    rw [actual_context]
    congr 1
    exact congrArg₂ finiteRelativeEntropy
      (exactReverseAliceSideMarkedPosteriorConditional_eq_sourcePosterior
        G n S D remaining default seed outcome)
      (exactReverseAliceMarkedPriorConditional_eq_game
        G n S D remaining default seed outcome
        (exactReverseAliceMarkedPriorMarginal_ne_zero_of_outcome
          G n S D remaining positive default seed outcome zero))

theorem exactAliceSourceConditionalInformation_eq_seedBornAverage
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceConditionalInformation G n S D base =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          exactAliceSourceSeedBornInformation G n S D seed := by
  classical
  rw [exactAliceSourceConditionalInformation_eq_joint_atom_sum
    G n S D remaining positive base, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro seed _
  unfold exactAliceSourceSeedBornInformation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  unfold exactPostselectedJointLaw
  ring

theorem exactReverseAliceConditionalHistoryIdentification_proved
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (default : Y) :
    ExactReverseAliceConditionalHistoryIdentification
      G n S D remaining base default := by
  unfold ExactReverseAliceConditionalHistoryIdentification
  rw [exactAliceSourceConditionalInformation_eq_seedBornAverage
    G n S D remaining positive base,
    exactReverseAlicePrefixInformation_eq_markedSeedAverage
      G n S D remaining positive default]
  apply Finset.sum_congr rfl
  intro seed _
  congr 1
  exact
    (exactReverseAliceMarkedContextInformation_eq_source
      G n S D remaining positive default seed).symm

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactReverseBobMaskedQuestionRegister_stable
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (ys : Fin n → Y)
    (tail : {j : Fin n //
      j ≠ ((exactReverseBobContextAt side seed).sideRank.symm
        marker).val.val} → X)
    (x x' : X) :
    exactReverseBobMaskedQuestionRegister
        D side default marker flag seed
        ((Equiv.funSplitAt
          ((exactReverseBobContextAt side seed).sideRank.symm
            marker).val.val X).symm (x, tail)) ys =
      exactReverseBobMaskedQuestionRegister
        D side default marker flag seed
        ((Equiv.funSplitAt
          ((exactReverseBobContextAt side seed).sideRank.symm
            marker).val.val X).symm (x', tail)) ys := by
  classical
  let context := exactReverseBobContextAt side seed
  let marked : SourceRemainingCoordinate D :=
    (context.sideRank.symm marker).val
  let coordinate : Fin n := marked.val
  have outsideD : coordinate ∉ D := by
    exact (Finset.mem_sdiff.mp marked.property).2
  have outsideOther : marked ∉ context.otherSide := by
    rw [context.otherSide_eq_complement]
    simp [marked, (context.sideRank.symm marker).property]
  change
    exactReverseBobMaskedQuestionRegister
        D side default marker flag seed
        ((Equiv.funSplitAt coordinate X).symm (x, tail)) ys =
      exactReverseBobMaskedQuestionRegister
        D side default marker flag seed
        ((Equiv.funSplitAt coordinate X).symm (x', tail)) ys
  unfold exactReverseBobMaskedQuestionRegister
    finitePrefixMask
  apply Prod.ext
  · apply Prod.ext
    · apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Prod.ext
        · funext j
          have different : j.val ≠ coordinate := by
            intro same
            exact outsideD (same ▸ j.property)
          simp [Equiv.funSplitAt, Equiv.piSplitAt, different]
        apply Prod.ext
        · rfl
        apply Prod.ext
        · rfl
        apply Prod.ext
        · funext j
          have different : j.val.val ≠ coordinate := by
            intro same
            apply outsideOther
            have actual : j.val = marked := by
              apply Subtype.ext
              exact same
            exact actual ▸ j.property
          simp [Equiv.funSplitAt, Equiv.piSplitAt, different]
        · rfl
    · rfl
  · funext position
    by_cases before : position.val < marker.val
    · have different :
          ((context.sideRank.symm position).val.val) ≠ coordinate := by
        intro same
        have sameMarked :
            context.sideRank.symm position =
              context.sideRank.symm marker := by
          apply Subtype.ext
          apply Subtype.ext
          exact same
        have samePosition :=
          context.sideRank.symm.injective sameMarked
        exact (Nat.ne_of_lt before)
          (congrArg Fin.val samePosition)
      simp [before, context, Equiv.funSplitAt,
        Equiv.piSplitAt, different]
    · simp [before]

theorem exactConditionedReverseBobNextPrior_flagged_mixture
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card) :
    groupedMass (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextPrior
          G n S D remaining side) =
      groupedMass
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          (exactReverseBobMaskedQuestionRegister
            D side default marker point.1.1 point.1.2
            point.2.1 point.2.2.1,
            point.2.1
              (((exactReverseBobContextAt
                side point.1.2).sideRank.symm marker).val.val)))
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          (finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (exactReverseBobConditionalSeedLaw
              (exactRemainingCoordinate_card_pos
                D remaining) side).weight point.1.2) *
            (strategyEventLaw (G.repeat n) S).weight point.2) := by
  classical
  funext target
  let seedLaw := exactReverseBobConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseBobSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  change
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixPrior
          seedLaw G n S D projection) target = _
  calc
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixPrior
          seedLaw G n S D projection) target =
      groupedMass
        (fun point : ConditionedAnswerFlag A B D ×
          (ExactRemainingSeed D ×
            ExactOutcome X Y A B n) =>
          exactPrefixNextCode default marker
            (((projection point.2).1, point.1),
              (projection point.2).2))
        (fun point : ConditionedAnswerFlag A B D ×
          (ExactRemainingSeed D ×
            ExactOutcome X Y A B n) =>
          finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (reweightedSeedPriorEventLaw
              seedLaw G n S).weight point.2)
        target :=
      reweightedSeedPrefixPrior_next_flagged_pushforward
        seedLaw G n S D projection default marker target
    _ = _ := by
      change
        groupedMass
          (fun point : ConditionedAnswerFlag A B D ×
            (ExactRemainingSeed D ×
              ExactOutcome X Y A B n) =>
            (exactReverseBobMaskedQuestionRegister
              D side default marker point.1 point.2.1
              point.2.2.1 point.2.2.2.1,
              point.2.2.1
                (((exactReverseBobContextAt
                  side point.2.1).sideRank.symm marker).val.val)))
          (fun point : ConditionedAnswerFlag A B D ×
            (ExactRemainingSeed D ×
              ExactOutcome X Y A B n) =>
            finiteUniformWeight
                (ConditionedAnswerFlag A B D) *
              (seedLaw.weight point.2.1 *
                (strategyEventLaw (G.repeat n) S).weight point.2.2))
          target = _
      exact groupedMass_flagSeedOutcome_reassoc
        (fun flag seed (outcome : ExactOutcome X Y A B n) =>
          (exactReverseBobMaskedQuestionRegister
            D side default marker flag seed outcome.1 outcome.2.1,
            outcome.1
              (((exactReverseBobContextAt
                side seed).sideRank.symm marker).val.val)))
        (fun _ : ConditionedAnswerFlag A B D =>
          finiteUniformWeight
            (ConditionedAnswerFlag A B D))
        seedLaw.weight
        (strategyEventLaw (G.repeat n) S).weight target

theorem exactReverseBobMaskedQuestionRegister_determines
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (xs : Fin n → X) (ys : Fin n → Y)
    (target : ExactReverseBobNextContext X Y A B D side)
    (same :
      exactReverseBobMaskedQuestionRegister
        D side default marker flag seed xs ys = target) :
    ys (((exactReverseBobContextAt
        side seed).sideRank.symm marker).val.val) =
      target.1.1.2.2.2.1
        (target.1.1.1.sideRank.symm marker) := by
  have actual := congrArg
    (fun context : ExactReverseBobNextContext
      X Y A B D side =>
      context.1.1.2.2.2.1
        (context.1.1.1.sideRank.symm marker)) same
  exact actual

theorem exactConditionedReverseBobNextPrior_marked_joint_factor
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (target : ExactReverseBobNextContext X Y A B D side)
    (next : X) :
    groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextPrior
          G n S D remaining side)
        (target, next) =
      G.conditionalXGivenY
          (target.1.1.2.2.2.1
            (target.1.1.1.sideRank.symm marker)) next *
        jointFirstMarginal
          (groupedMass
            (exactPrefixNextCode default marker)
            (exactConditionedReverseBobNextPrior
              G n S D remaining side))
          target := by
  classical
  let seedLaw := exactReverseBobConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let mixedWeight :
      ConditionedAnswerFlag A B D ×
        ExactRemainingSeed D → ℝ :=
    fun index =>
      finiteUniformWeight
        (ConditionedAnswerFlag A B D) *
        seedLaw.weight index.2
  let coordinate :
      ConditionedAnswerFlag A B D ×
        ExactRemainingSeed D → Fin n :=
    fun index =>
      ((exactReverseBobContextAt
        side index.2).sideRank.symm marker).val.val
  let code :
      (ConditionedAnswerFlag A B D ×
        ExactRemainingSeed D) →
          (Fin n → X) → (Fin n → Y) →
            ExactReverseBobNextContext X Y A B D side :=
    fun index xs ys =>
      exactReverseBobMaskedQuestionRegister
        D side default marker index.1 index.2 xs ys
  let question : Y :=
    target.1.1.2.2.2.1
      (target.1.1.1.sideRank.symm marker)
  have stable :
      ∀ (index : ConditionedAnswerFlag A B D ×
          ExactRemainingSeed D)
        (ys : Fin n → Y)
        (tail : {j : Fin n // j ≠ coordinate index} → X)
        (x x' : X),
        code index
            ((Equiv.funSplitAt (coordinate index) X).symm (x, tail)) ys =
          code index
            ((Equiv.funSplitAt (coordinate index) X).symm (x', tail)) ys := by
    intro index ys tail x x'
    exact exactReverseBobMaskedQuestionRegister_stable
      D side default marker index.1 index.2 ys tail x x'
  have determines :
      ∀ (index : ConditionedAnswerFlag A B D ×
          ExactRemainingSeed D)
        (xs : Fin n → X) (ys : Fin n → Y),
        code index xs ys = target →
          ys (coordinate index) = question := by
    intro index xs ys same
    exact exactReverseBobMaskedQuestionRegister_determines
      D side default marker index.1 index.2 xs ys target same
  have mixed := mixedStableAliceQuestionCode_joint_factor
    G n S mixedWeight coordinate code target question next
    stable determines
  rw [exactConditionedReverseBobNextPrior_flagged_mixture
    G n S D remaining side default marker]
  change
    groupedMass
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          (code point.1 point.2.1 point.2.2.1,
            point.2.1 (coordinate point.1)))
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          mixedWeight point.1 *
            (strategyEventLaw (G.repeat n) S).weight point.2)
        (target, next) =
      G.conditionalXGivenY question next *
        jointFirstMarginal
          (groupedMass
            (fun point :
              (ConditionedAnswerFlag A B D ×
                ExactRemainingSeed D) ×
                  ExactOutcome X Y A B n =>
              (code point.1 point.2.1 point.2.2.1,
                point.2.1 (coordinate point.1)))
            (fun point :
              (ConditionedAnswerFlag A B D ×
                ExactRemainingSeed D) ×
                  ExactOutcome X Y A B n =>
              mixedWeight point.1 *
                (strategyEventLaw (G.repeat n) S).weight point.2))
          target
  rw [jointFirstMarginal_groupedContextNext]
  convert mixed using 1
  exact congrFun (exactGroupedMass_decidableEq_irrel
    _ _ _ _) (target, next)

theorem exactConditionedReverseBobNextPrior_marked_conditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (target : ExactReverseBobNextContext X Y A B D side)
    (supported :
      jointFirstMarginal
        (groupedMass
          (exactPrefixNextCode default marker)
          (exactConditionedReverseBobNextPrior
            G n S D remaining side))
        target ≠ 0) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default marker)
          (exactConditionedReverseBobNextPrior
            G n S D remaining side))
        target =
      G.conditionalXGivenY
        (target.1.1.2.2.2.1
          (target.1.1.1.sideRank.symm marker)) := by
  funext next
  unfold jointConditional
  rw [exactConditionedReverseBobNextPrior_marked_joint_factor
    G n S D remaining side default marker target next]
  exact mul_div_cancel_right₀ _ supported

theorem exactReverseBobMarkedPriorConditional_eq_game
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n)
    (supported :
      jointFirstMarginal
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩))
          (exactConditionedReverseBobNextPrior
            G n S D remaining
            (exactReverseRightSide seed)))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) ≠ 0) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩))
          (exactConditionedReverseBobNextPrior
            G n S D remaining
            (exactReverseRightSide seed)))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) =
      G.conditionalXGivenY
        (reference.2.1 seed.coordinate.val) := by
  have actual := exactConditionedReverseBobNextPrior_marked_conditional
    G n S D remaining
    (exactReverseRightSide seed) default
    ((exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩)
    (exactReverseBobMarkedHistoryContext
      G n S D default seed reference) supported
  simpa [exactReverseBobMarkedHistoryContext,
    finitePrefixMask,
    exactReverseBobSourceProjection] using actual

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactReverseBobMaskedOutcomeContext
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseBobNextContext X Y A B D side :=
  let projection :=
    exactReverseBobContextOutcomeProjection
      (X := X) (Y := Y) (A := A) (B := B)
      D side context outcome
  finitePrefixMask default marker.castSucc
    ((projection.1,
      repeatedConditionedAnswerFlag G n S D outcome),
      projection.2)

theorem exactReverseBobMaskedOutcomeContext_extract
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    (exactReverseBobMaskedOutcomeContext
      G n S D side default marker context outcome).1.1.1 =
      context := by
  rfl

theorem exactConditionedReverseBobNextJoint_marked_mixture
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card) :
    groupedMass (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextJoint
          G n S D remaining side) =
      groupedMass
        (fun point : ExactJointOutcome X Y A B D =>
          (exactReverseBobMaskedOutcomeContext
            G n S D side default marker
            (exactReverseBobContextAt side point.1)
            point.2,
            point.2.1
              (((exactReverseBobContextAt
                side point.1).sideRank.symm marker).val.val)))
        (fun point : ExactJointOutcome X Y A B D =>
          (exactReverseBobConditionalSeedLaw
            (exactRemainingCoordinate_card_pos
              D remaining) side).weight point.1 *
            repeatedConditionedOutcomeLaw G n S D point.2) := by
  classical
  let law := exactReverseBobConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseBobSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  change
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixJoint
          law G n S D projection) = _
  rw [reweightedSeedPrefixNextJoint_as_actual_pushforward]
  funext target
  unfold groupedMass
  apply Finset.sum_congr
  · ext point
    simp [exactPrefixNextCode,
      exactReverseBobMaskedOutcomeContext,
      exactReverseBobContextOutcomeProjection,
      exactReverseBobSourceProjection,
      projection]
  · intro point _
    exact reweightedSeedPosterior_eq_product
      law G n S D point

theorem exactReverseBobConditionalSeedLaw_actual_pos
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (seed : ExactForwardSeed M) :
    0 < (exactReverseBobConditionalSeedLaw
      nonempty (exactReverseRightSide seed)).weight seed := by
  have sideNonempty :
      (exactReverseRightSide seed).Nonempty :=
    ⟨seed.coordinate,
      exactReverseRightSide_coordinate_mem seed⟩
  rw [exactReverseBobConditionalSeedLaw_weight
    nonempty (exactReverseRightSide seed)
    sideNonempty seed]
  unfold exactReverseBobConditionalSeedWeight
  rw [if_pos rfl]
  exact div_pos
    (exactSeedWeight_pos_of_seed seed)
    ((reversePartitionWeight_pos_iff nonempty
      (exactReverseRightSide seed)).mpr sideNonempty)

theorem exactReverseBobMaskedOutcomeContext_actual
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n) :
    exactReverseBobMaskedOutcomeContext
        G n S D (exactReverseRightSide seed) default
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩)
        (exactReverseBobContextAt
          (exactReverseRightSide seed) seed)
        outcome =
      exactReverseBobMarkedHistoryContext
        G n S D default seed outcome := by
  simp [exactReverseBobMaskedOutcomeContext,
    exactReverseBobContextOutcomeProjection,
    exactReverseBobMarkedHistoryContext,
    exactReverseBobSourceProjection]

theorem exactConditionedReverseBobNextJoint_marked_conditional_eq_fixedOutcome
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩))
          (exactConditionedReverseBobNextJoint
            G n S D remaining
            (exactReverseRightSide seed)))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseBobMarkedHistoryContext
              G n S D default seed outcome,
              outcome.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) := by
  classical
  let side := exactReverseRightSide seed
  let marker : Fin side.card :=
    (exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
  let law := exactReverseBobConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let index : ExactRemainingSeed D →
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side :=
    exactReverseBobContextAt side
  let context :
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side →
          ExactOutcome X Y A B n →
            ExactReverseBobNextContext X Y A B D side :=
    exactReverseBobMaskedOutcomeContext
      G n S D side default marker
  let next :
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side →
          ExactOutcome X Y A B n → X :=
    fun reverseContext outcome =>
      outcome.1
        ((reverseContext.sideRank.symm marker).val.val)
  let extract :
      ExactReverseBobNextContext X Y A B D side →
        ExactReverseSideContext
          (SourceRemainingCoordinate D) side :=
    fun target => target.1.1.1
  let target :=
    exactReverseBobMarkedHistoryContext
      G n S D default seed reference
  have extract_context :
      ∀ (reverseContext : ExactReverseSideContext
          (SourceRemainingCoordinate D) side)
        (outcome : ExactOutcome X Y A B n),
        extract (context reverseContext outcome) = reverseContext := by
    intro reverseContext outcome
    exact exactReverseBobMaskedOutcomeContext_extract
      G n S D side default marker reverseContext outcome
  have target_index : extract target = index seed := by
    rfl
  have positive :
      0 < groupedMass index law.weight (index seed) := by
    apply groupedMass_pos_of_supported_atom
      index law.weight law.weight_nonneg seed
    exact exactReverseBobConditionalSeedLaw_actual_pos
      (exactRemainingCoordinate_card_pos D remaining) seed
  have stable := jointConditional_product_stable_context_seed
    index context next extract extract_context
    law.weight (repeatedConditionedOutcomeLaw G n S D)
    seed target target_index (ne_of_gt positive)
  rw [exactConditionedReverseBobNextJoint_marked_mixture
    G n S D remaining side default marker]
  change
    jointConditional
        (groupedMass
          (fun point : ExactJointOutcome X Y A B D =>
            (context (index point.1) point.2,
              next (index point.1) point.2))
          (fun point : ExactJointOutcome X Y A B D =>
            law.weight point.1 *
              repeatedConditionedOutcomeLaw
                G n S D point.2))
        target =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseBobMarkedHistoryContext
              G n S D default seed outcome,
              outcome.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        target
  calc
    jointConditional
        (groupedMass
          (fun point : ExactJointOutcome X Y A B D =>
            (context (index point.1) point.2,
              next (index point.1) point.2))
          (fun point : ExactJointOutcome X Y A B D =>
            law.weight point.1 *
              repeatedConditionedOutcomeLaw
                G n S D point.2))
        target =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (context (index seed) outcome,
              next (index seed) outcome))
          (repeatedConditionedOutcomeLaw G n S D))
        target := by
          convert stable using 1
          · congr 1
            exact exactGroupedMass_decidableEq_irrel
              _ _ _ _
          · congr 1
            exact exactGroupedMass_decidableEq_irrel
              _ _ _ _
    _ = jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseBobMarkedHistoryContext
              G n S D default seed outcome,
              outcome.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        target := by
          congr 1
          apply congrArg
            (fun code =>
              groupedMass code
                (repeatedConditionedOutcomeLaw G n S D))
          funext outcome
          apply Prod.ext
          · exact exactReverseBobMaskedOutcomeContext_actual
              G n S D default seed outcome
          · simp [next, index, side, marker]

theorem exactConditionedReverseBobNextJoint_marked_conditional_eq_sourcePosterior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩))
          (exactConditionedReverseBobNextJoint
            G n S D remaining
            (exactReverseRightSide seed)))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (fun atom :
          ((SourceRemainingCoordinate D × Y) ×
            ExactHistoryFlag X Y A B D) × X =>
          exactBobInformationPosterior G n S D
            (atom.1.1, (atom.1.2, atom.2)))
        ((seed.coordinate, reference.2.1 seed.coordinate.val),
          exactHistoryCode D (seed, reference)) := by
  exact
    (exactConditionedReverseBobNextJoint_marked_conditional_eq_fixedOutcome
      G n S D remaining default seed reference).trans
      (exactReverseBobMarkedPosteriorConditional_eq_sourcePosterior
        G n S D default seed reference)

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactReverseBobContextMarkedEntropyScore
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card)
    (outcome : ExactOutcome X Y A B n) : ℝ :=
  let target :=
    exactReverseBobMaskedOutcomeContext
      G n S D side default marker context outcome
  finiteRelativeEntropy
    (jointConditional
      (groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextJoint
          G n S D remaining side))
      target)
    (jointConditional
      (groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextPrior
          G n S D remaining side))
      target)

def exactReverseBobActualMarkedEntropyScore
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (side : Finset (SourceRemainingCoordinate D))
    (seed : ExactRemainingSeed D)
    (marker : Fin side.card)
    (outcome : ExactOutcome X Y A B n) : ℝ :=
  let target :=
    exactReverseBobMaskedOutcomeContext
      G n S D side default marker
      (exactReverseBobContextAt side seed)
      outcome
  finiteRelativeEntropy
    (jointConditional
      (groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextJoint
          G n S D remaining side))
      target)
    (jointConditional
      (groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextPrior
          G n S D remaining side))
      target)

theorem exactReverseBobActualMarkedEntropyScore_eq_context
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (side : Finset (SourceRemainingCoordinate D))
    (seed : ExactRemainingSeed D)
    (marker : Fin side.card)
    (outcome : ExactOutcome X Y A B n) :
    exactReverseBobActualMarkedEntropyScore
        G n S D remaining default side seed marker outcome =
      exactReverseBobContextMarkedEntropyScore
        G n S D remaining default side
        (exactReverseBobContextAt side seed)
        marker outcome := by
  rfl

theorem exactConditionedReverseBobPrefixEntropyIncrement_eq_markedOutcomeScore
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X)
    (marker : Fin side.card) :
    exactConditionedReverseBobPrefixEntropyIncrement
        G n S D remaining side default marker =
      ∑ seed : ExactRemainingSeed D,
        (exactReverseBobConditionalSeedLaw
          (exactRemainingCoordinate_card_pos
            D remaining) side).weight seed *
          ∑ outcome : ExactOutcome X Y A B n,
            repeatedConditionedOutcomeLaw G n S D outcome *
              exactReverseBobActualMarkedEntropyScore
                G n S D remaining default side seed marker outcome := by
  classical
  let law := exactReverseBobConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseBobSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  change
    reweightedSeedPrefixEntropyIncrement
        law G n S D projection default marker = _
  rw [reweightedSeedPrefixEntropyIncrement_eq_actual_atom_sum
    law G n S D positive projection default marker]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro seed _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  rw [reweightedSeedPosterior_eq_product]
  change
    (law.weight seed *
      repeatedConditionedOutcomeLaw G n S D outcome) *
        exactReverseBobActualMarkedEntropyScore
          G n S D remaining default side seed marker outcome =
      law.weight seed *
        (repeatedConditionedOutcomeLaw G n S D outcome *
          exactReverseBobActualMarkedEntropyScore
            G n S D remaining default side seed marker outcome)
  ring

theorem exactConditionedReverseBobPrefixInformation_eq_sourceMarkerAverage
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : X) :
    exactConditionedReverseBobPrefixInformation
        G n S D remaining default =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseRightSide seed).card,
            ∑ outcome : ExactOutcome X Y A B n,
              repeatedConditionedOutcomeLaw G n S D outcome *
                exactReverseBobActualMarkedEntropyScore
                  G n S D remaining default
                  (exactReverseRightSide seed)
                  seed marker outcome) /
            ((exactReverseRightSide seed).card : ℝ)) := by
  classical
  unfold exactConditionedReverseBobPrefixInformation
  simp_rw [
    exactConditionedReverseBobPrefixEntropyIncrement_eq_markedOutcomeScore
      G n S D remaining positive]
  exact exactReverseBobSideWeightedPrefix_sum
    (exactRemainingCoordinate_card_pos D remaining)
    (fun side seed marker =>
      ∑ outcome : ExactOutcome X Y A B n,
        repeatedConditionedOutcomeLaw G n S D outcome *
          exactReverseBobActualMarkedEntropyScore
            G n S D remaining default side seed marker outcome)

theorem exactConditionedReverseBobPrefixInformation_eq_sourceMarkedOutcomeScore
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : X) :
    exactConditionedReverseBobPrefixInformation
        G n S D remaining default =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          ∑ outcome : ExactOutcome X Y A B n,
            repeatedConditionedOutcomeLaw G n S D outcome *
              exactReverseBobContextMarkedEntropyScore
                G n S D remaining default
                (exactReverseRightSide seed)
                (exactReverseBobContext seed)
                ((exactReverseBobContext seed).sideRank
                  ⟨seed.coordinate,
                    exactReverseRightSide_coordinate_mem seed⟩)
                outcome := by
  calc
    exactConditionedReverseBobPrefixInformation
        G n S D remaining default =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseRightSide seed).card,
            ∑ outcome : ExactOutcome X Y A B n,
              repeatedConditionedOutcomeLaw G n S D outcome *
                exactReverseBobActualMarkedEntropyScore
                  G n S D remaining default
                  (exactReverseRightSide seed)
                  seed marker outcome) /
            ((exactReverseRightSide seed).card : ℝ)) :=
      exactConditionedReverseBobPrefixInformation_eq_sourceMarkerAverage
        G n S D remaining positive default
    _ = _ := by
      simpa only [
        exactReverseBobActualMarkedEntropyScore_eq_context,
        exactReverseBobContextAt_actual] using
        (exactReverseBobUniformMarkedSeed_sum
          (exactRemainingCoordinate_card_pos D remaining)
          (fun side context marker =>
            ∑ outcome : ExactOutcome X Y A B n,
              repeatedConditionedOutcomeLaw G n S D outcome *
                exactReverseBobContextMarkedEntropyScore
                  G n S D remaining default side context marker outcome))

theorem exactReverseBobMarkedPriorMarginal_ne_zero_of_outcome
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : X)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n)
    (supported :
      repeatedConditionedOutcomeLaw G n S D outcome ≠ 0) :
    jointFirstMarginal
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩))
          (exactConditionedReverseBobNextPrior
            G n S D remaining
            (exactReverseRightSide seed)))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed outcome) ≠ 0 := by
  let side := exactReverseRightSide seed
  let marker : Fin side.card :=
    (exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
  let law := exactReverseBobConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseBobSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  have outcome_nonnegative :
      0 ≤ repeatedConditionedOutcomeLaw
        G n S D outcome :=
    conditionedEventDistribution_nonneg
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive outcome
  have outcome_positive :
      0 < repeatedConditionedOutcomeLaw
        G n S D outcome :=
    lt_of_le_of_ne outcome_nonnegative (Ne.symm supported)
  have seed_positive :
      0 < law.weight seed :=
    exactReverseBobConditionalSeedLaw_actual_pos
      (exactRemainingCoordinate_card_pos D remaining) seed
  have atom_positive :
      0 < reweightedSeedPosterior
        law G n S D (seed, outcome) := by
    rw [reweightedSeedPosterior_eq_product]
    exact mul_pos seed_positive outcome_positive
  have actual := reweightedSeedPrefixPriorMarginal_ne_zero_of_positive_atom
    law G n S D positive projection default marker
    (seed, outcome) atom_positive
  exact actual

theorem exactReverseBobActualMarkedEntropy_eq_source
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : X)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n)
    (supported :
      repeatedConditionedOutcomeLaw G n S D outcome ≠ 0) :
    exactReverseBobContextMarkedEntropyScore
        G n S D remaining default
        (exactReverseRightSide seed)
        (exactReverseBobContext seed)
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩)
        outcome =
      finiteRelativeEntropy
        (jointConditional
          (fun atom :
            ((SourceRemainingCoordinate D × Y) ×
              ExactHistoryFlag X Y A B D) × X =>
            exactBobInformationPosterior G n S D
              (atom.1.1, (atom.1.2, atom.2)))
          ((seed.coordinate, outcome.2.1 seed.coordinate.val),
            exactHistoryCode D (seed, outcome)))
        (G.conditionalXGivenY
          (outcome.2.1 seed.coordinate.val)) := by
  have history :
      exactReverseBobMaskedOutcomeContext
        G n S D (exactReverseRightSide seed) default
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩)
        (exactReverseBobContext seed) outcome =
      exactReverseBobMarkedHistoryContext
        G n S D default seed outcome := by
    simpa only [exactReverseBobContextAt_actual] using
      (exactReverseBobMaskedOutcomeContext_actual
        G n S D default seed outcome)
  have prior_supported :=
    exactReverseBobMarkedPriorMarginal_ne_zero_of_outcome
      G n S D remaining positive default seed outcome supported
  unfold exactReverseBobContextMarkedEntropyScore
  dsimp only
  rw [history]
  rw [exactConditionedReverseBobNextJoint_marked_conditional_eq_sourcePosterior
    G n S D remaining default seed outcome]
  rw [exactReverseBobMarkedPriorConditional_eq_game
    G n S D remaining default seed outcome prior_supported]

theorem exactReverseBobConditionalHistoryIdentification_proved
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (default : X) :
    ExactReverseBobConditionalHistoryIdentification
      G n S D remaining base default := by
  classical
  unfold ExactReverseBobConditionalHistoryIdentification
  rw [exactBobSourceConditionalInformation_eq_joint_atom_sum
    G n S D remaining positive base]
  rw [exactConditionedReverseBobPrefixInformation_eq_sourceMarkedOutcomeScore
    G n S D remaining positive default]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro seed _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases zero :
      repeatedConditionedOutcomeLaw
        G n S D outcome = 0
  · simp [exactPostselectedJointLaw, zero]
  · rw [exactReverseBobActualMarkedEntropy_eq_source
      G n S D remaining positive default seed outcome zero]
    unfold exactPostselectedJointLaw
    ring

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exact_source_equation_twenty_three_unconditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (defaultY : Y) (defaultX : X) :
    ExactSourceClassicalInformationBound G n S D base := by
  exact exact_source_equation_twenty_three_of_actual_conditioned_reindex
    G n S D remaining positive base defaultY defaultX
    (exactReverseAliceConditionalHistoryIdentification_proved
      G n S D remaining positive base defaultY)
    (exactReverseBobConditionalHistoryIdentification_proved
      G n S D remaining positive base defaultX)

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def ExactSourceSupportPreservingClassicalSampler
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (kappa gamma : ℝ) : Prop :=
  ∃ denominator : ℕ, 0 < denominator ∧
    ∃ numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ,
      (∀ index, (∑ history, numerator index history) = denominator) ∧
      (∀ index, finiteTotalVariation
        (exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index)
        (fun history =>
          (numerator index history : ℝ) / denominator) < gamma) ∧
      (∀ index history,
        0 < exactLocalConditionalFamily D base
            (exactLocallySampleableLaw G n S D)
            index history →
          0 < numerator index history) ∧
      ∃ nonempty : ∀ index,
        (rationalMarked denominator (numerator index)).Nonempty,
        finiteTotalVariation
            (exactLocallySampleableLaw G n S D)
            (exactLocallySampleableJARounded
              G n D denominator numerator) ≤ kappa + gamma ∧
        finiteTotalVariation
            (exactLocallySampleableLaw G n S D)
            (exactLocallySampleableJBRounded
              G n D denominator numerator) ≤ kappa + gamma ∧
        exactLocallySampleablePermutationMismatch
            G n D denominator numerator nonempty ≤
          4 * (kappa + gamma)

theorem exact_source_equation_twenty_seven_support_preserving
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    {kappa gamma : ℝ} (gamma_positive : 0 < gamma)
    (alice : finiteTotalVariation
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableJA G n S D base) ≤ kappa)
    (bob : finiteTotalVariation
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableJB G n S D base) ≤ kappa) :
    ExactSourceSupportPreservingClassicalSampler
      G n S D base kappa gamma := by
  obtain ⟨denominator, denominator_positive, numerator,
      normalized, approximation, preserves, nonempty, _, _⟩ :=
    exact_exists_support_preserving_local_shared_permutation
      G n S D positive base gamma_positive
  have rounded_alice :
      finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJARounded
            G n D denominator numerator) ≤ kappa + gamma := by
    calc
      finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJARounded
            G n D denominator numerator) ≤
        finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJA G n S D base) +
        finiteTotalVariation
          (exactLocallySampleableJA G n S D base)
          (exactLocallySampleableJARounded
            G n D denominator numerator) :=
          finiteTotalVariation_triangle _ _ _
      _ ≤ kappa + gamma :=
        add_le_add alice
          (exactLocallySampleableJA_rounded_totalVariation_le
            G n S D remaining base denominator numerator approximation)
  have rounded_bob :
      finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJBRounded
            G n D denominator numerator) ≤ kappa + gamma := by
    calc
      finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJBRounded
            G n D denominator numerator) ≤
        finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJB G n S D base) +
        finiteTotalVariation
          (exactLocallySampleableJB G n S D base)
          (exactLocallySampleableJBRounded
            G n D denominator numerator) :=
          finiteTotalVariation_triangle _ _ _
      _ ≤ kappa + gamma :=
        add_le_add bob
          (exactLocallySampleableJB_rounded_totalVariation_le
            G n S D remaining base denominator numerator approximation)
  refine ⟨denominator, denominator_positive, numerator,
    normalized, approximation, preserves, nonempty,
    rounded_alice, rounded_bob, ?_⟩
  calc
    exactLocallySampleablePermutationMismatch
        G n D denominator numerator nonempty ≤
      2 * finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) :=
        exactLocallySampleablePermutationMismatch_le_two_tv
          G n D denominator denominator_positive
          numerator normalized nonempty
    _ ≤ 2 *
        (finiteTotalVariation
          (exactLocallySampleableJARounded
            G n D denominator numerator)
          (exactLocallySampleableLaw G n S D) +
         finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJBRounded
            G n D denominator numerator)) := by
      gcongr
      exact finiteTotalVariation_triangle _ _ _
    _ = 2 *
        (finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJARounded
            G n D denominator numerator) +
         finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJBRounded
            G n D denominator numerator)) := by
      rw [finiteTotalVariation_comm
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableLaw G n S D)]
    _ ≤ 4 * (kappa + gamma) := by
      nlinarith

theorem
    exact_source_equation_twenty_seven_support_preserving_of_information
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (information : ExactSourceClassicalInformationBound
      G n S D base)
    {gamma : ℝ} (gamma_positive : 0 < gamma) :
    ExactSourceSupportPreservingClassicalSampler
      G n S D base (exactSourcePinskerRate G n S D) gamma := by
  exact exact_source_equation_twenty_seven_support_preserving
    G n S D remaining positive base gamma_positive
    (exact_source_alice_pinsker_of_classical_information
      G n S D remaining positive base information)
    (exact_source_bob_pinsker_of_classical_information
      G n S D remaining positive base information)

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem gameQuestionX_nonempty
    (G : Game X Y A B) : Nonempty X := by
  classical
  by_contra empty
  have zero : (∑ x : X, ∑ y : Y, G.questionWeight x y) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact (empty ⟨x⟩).elim
  linarith [G.weight_normalized]

theorem gameQuestionY_nonempty
    (G : Game X Y A B) : Nonempty Y := by
  classical
  by_contra empty
  have zero : (∑ x : X, ∑ y : Y, G.questionWeight x y) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro y _
    exact (empty ⟨y⟩).elim
  linarith [G.weight_normalized]

theorem exact_source_equation_twenty_three
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    ExactSourceClassicalInformationBound G n S D base := by
  classical
  exact exact_source_equation_twenty_three_unconditional
    G n S D remaining positive base
    (Classical.choice (gameQuestionY_nonempty G))
    (Classical.choice (gameQuestionX_nonempty G))

theorem
    exact_source_equation_twenty_seven_support_preserving_unconditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    {gamma : ℝ} (gamma_positive : 0 < gamma) :
    ExactSourceSupportPreservingClassicalSampler
      G n S D base (exactSourcePinskerRate G n S D) gamma := by
  exact
    exact_source_equation_twenty_seven_support_preserving_of_information
      G n S D remaining positive base
      (exact_source_equation_twenty_three
        G n S D remaining positive base)
      gamma_positive

end

noncomputable section

open Filter
open scoped Topology

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def ExactSourceOneGameRounding
    (G : Game X Y A B) : Prop :=
  ∃ K₀ : ℝ, 0 ≤ K₀ ∧
    ∀ (n : ℕ) (S : Strategy (G.repeat n))
      (D : Finset (Fin n)),
      0 < (Finset.univ \ D).card →
      0 < repeatedPostselectionMass G n S D →
      ∀ (α gamma : ℝ),
        0 < α → α ≤ 1 → 0 < gamma →
        uniformRemainingFailure
            (strategyEventLaw (G.repeat n) S)
            (repeatedCoordinateWin G n) D <
          (1 - entangledValue G) / 2 →
        ∃ rounded : Strategy G,
          roundedWinningLowerBound (1 - entangledValue G)
              K₀ α (martingaleRate G n S D)
              (exactSourcePinskerRate G n S D + gamma) ≤
            rounded.winProbability

theorem exact_totalSamplingLoss_mono
    {K₀ α₁ α₂ η₁ η₂ lam₁ lam₂ : ℝ}
    (constant_nonnegative : 0 ≤ K₀)
    (alpha_nonnegative : 0 ≤ α₁)
    (alpha_le : α₁ ≤ α₂)
    (eta_nonnegative : 0 ≤ η₁)
    (eta_le : η₁ ≤ η₂)
    (lam_le : lam₁ ≤ lam₂) :
    totalSamplingLoss K₀ α₁ η₁ lam₁ ≤
      totalSamplingLoss K₀ α₂ η₂ lam₂ := by
  have ceiling_nonnegative : 0 ≤ universalErrorCeiling K₀ := by
    unfold universalErrorCeiling
    positivity
  have alpha_root :
      α₁ ^ (1 / 12 : ℝ) ≤ α₂ ^ (1 / 12 : ℝ) :=
    Real.rpow_le_rpow alpha_nonnegative alpha_le (by norm_num)
  have eta_root :
      (32 * η₁) ^ (1 / 12 : ℝ) ≤
        (32 * η₂) ^ (1 / 12 : ℝ) := by
    apply Real.rpow_le_rpow
    · positivity
    · linarith
    · norm_num
  have eta_sqrt :
      Real.sqrt (8 * η₁) ≤ Real.sqrt (8 * η₂) := by
    apply Real.sqrt_le_sqrt
    linarith
  unfold totalSamplingLoss
  gcongr

theorem exact_standardQuantumParallelRepetition_of_source_rounding
    (G : Game X Y A B)
    (rounding : ExactSourceOneGameRounding G) :
    StandardQuantumParallelRepetition G := by
  intro gap
  by_contra no_exponential_bound
  have witness : HasSubexponentialWitness (repeatedEntangledValue G) :=
    (not_hasExponentialBound_iff (repeatedEntangledValue G)).mp
      no_exponential_bound
  obtain ⟨K₀, constant_nonnegative, construct⟩ := rounding
  let gapValue : ℝ := 1 - entangledValue G
  have gap_positive : 0 < gapValue := by
    dsimp [gapValue]
    linarith
  let failureTolerance : ℝ := min (gapValue / 2) (1 / 2)
  have failure_positive : 0 < failureTolerance := by
    dsimp [failureTolerance]
    exact lt_min (by positivity) (by norm_num)
  have failure_at_most_one : failureTolerance ≤ 1 := by
    have half := min_le_right (gapValue / 2) (1 / 2 : ℝ)
    dsimp [failureTolerance]
    linarith
  let rate : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have rate_positive (k : ℕ) : 0 < rate k := by
    dsimp [rate]
    positivity
  have rate_at_most_one (k : ℕ) : rate k ≤ 1 := by
    dsimp [rate]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).2
    have nonnegative : (0 : ℝ) ≤ (k : ℝ) := by positivity
    nlinarith
  have rate_tendsto : Tendsto rate atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have martingale_tendsto :
      Tendsto (fun k => rate k ^ 2 / 8) atTop (𝓝 0) := by
    simpa using (rate_tendsto.pow 2).div_const (8 : ℝ)
  have sampling_tendsto :
      Tendsto (fun k => rate k / 2 + rate k) atTop (𝓝 0) := by
    simpa using (rate_tendsto.div_const (2 : ℝ)).add rate_tendsto
  have eventually_small :
      ∀ᶠ k : ℕ in atTop,
        totalSamplingLoss K₀ (rate k)
            (rate k ^ 2 / 8) (rate k / 2 + rate k) <
          gapValue / 2 :=
    totalSamplingLoss_eventually_lt K₀
      rate_tendsto martingale_tendsto sampling_tendsto
      (by positivity)
  obtain ⟨k, loss_small⟩ := eventually_small.exists
  obtain ⟨n, _, S, D, _, postselection_positive,
      remaining_positive, failure_small, martingale_small,
      pinsker_small⟩ :=
    exact_arbitrarily_large_conditioning_of_subexponentialWitness
      G witness failure_positive failure_at_most_one
      (rate_positive k) 0
  have failure_gap :
      uniformRemainingFailure
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D < gapValue / 2 :=
    lt_of_lt_of_le failure_small
      (min_le_left (gapValue / 2) (1 / 2 : ℝ))
  obtain ⟨rounded, rounded_bound⟩ :=
    construct n S D remaining_positive postselection_positive
      (rate k) (rate k)
      (rate_positive k) (rate_at_most_one k)
      (rate_positive k) (by simpa [gapValue] using failure_gap)
  have martingale_nonnegative :=
    martingaleRate_nonneg G n S D
      remaining_positive postselection_positive
  have exact_loss_small :
      totalSamplingLoss K₀ (rate k)
          (martingaleRate G n S D)
          (exactSourcePinskerRate G n S D + rate k) <
        gapValue / 2 := by
    refine lt_of_le_of_lt ?_ loss_small
    apply exact_totalSamplingLoss_mono
      constant_nonnegative (rate_positive k).le (le_refl _)
      martingale_nonnegative martingale_small
    linarith
  exact source_equation_twenty_nine_contradiction G rounded
    K₀ (rate k) (martingaleRate G n S D)
    (exactSourcePinskerRate G n S D + rate k)
    rounded_bound (by simpa [gapValue] using exact_loss_small)

end

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def unitaryConjugatePOVM
    {C d : Type} [Fintype C] [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (P : POVM C d) : POVM C d where
  effect c :=
    (U : Matrix d d ℂ)ᴴ * P.effect c * (U : Matrix d d ℂ)
  positive c := by
    have positive :=
      (P.positive c).mul_mul_conjTranspose_same
        ((U : Matrix d d ℂ)ᴴ)
    simpa using positive
  complete := by
    classical
    have unitary :
        (U : Matrix d d ℂ)ᴴ * (U : Matrix d d ℂ) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        (Matrix.mem_unitaryGroup_iff').mp U.property
    calc
      (∑ c : C,
        (U : Matrix d d ℂ)ᴴ * P.effect c * (U : Matrix d d ℂ)) =
          (U : Matrix d d ℂ)ᴴ *
            (∑ c : C, P.effect c) *
            (U : Matrix d d ℂ) := by
              simp [Finset.mul_sum, Finset.sum_mul]
      _ = 1 := by rw [P.complete, Matrix.mul_one, unitary]

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

theorem residualIdentity_quadratic
    {s t : Type} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (M : Matrix s s ℂ)
    (z : EuclideanSpace ℂ s)
    (κ : EuclideanSpace ℂ t)
    (normalized : ‖κ‖ = 1) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
        (M ⊗ₖ (1 : Matrix t t ℂ)))
      (toLp 2 (fun q : s × t => z q.1 * κ q.2)) =
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := s) (𝕜 := ℂ) M) z := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  have residual_square :
      (∑ j : t, ‖κ j‖ ^ 2) = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, normalized]
    norm_num
  have residual_complex :
      (∑ j : t, κ j * star (κ j)) = 1 := by
    calc
      (∑ j : t, κ j * star (κ j)) =
          (↑(∑ j : t, ‖κ j‖ ^ 2) : ℂ) := by
            push_cast
            apply Finset.sum_congr rfl
            intro j _
            simpa [Complex.normSq_eq_norm_sq] using
              Complex.mul_conj (κ j)
      _ = 1 := by rw [residual_square]; norm_num
  congr 1
  change
    (∑ i : s × t,
      (∑ j : s × t,
        (M i.1 j.1 * (if i.2 = j.2 then 1 else 0)) *
          (z j.1 * κ j.2)) *
        star (z i.1 * κ i.2)) =
      ∑ i : s, (∑ j : s, M i j * z j) * star (z i)
  rw [Fintype.sum_prod_type]
  calc
    (∑ i : s, ∑ k : t,
      (∑ j : s × t,
        (M i j.1 * (if k = j.2 then 1 else 0)) *
          (z j.1 * κ j.2)) *
        star (z i * κ k)) =
      ∑ i : s, ∑ k : t,
        ((∑ j : s, M i j * z j) * κ k) *
          star (z i * κ k) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro k _
            congr 1
            rw [Fintype.sum_prod_type]
            simp [mul_ite, ite_mul, Finset.sum_mul, mul_assoc]
    _ = ∑ i : s,
      ((∑ j : s, M i j * z j) * star (z i)) *
        (∑ k : t, κ k * star (κ k)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          simp only [star_mul]
          ring
    _ = ∑ i : s, (∑ j : s, M i j * z j) * star (z i) := by
          rw [residual_complex]
          simp

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactSourceGlobalCatalystWinningEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    Matrix
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e))
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (exactSourceGlobalCatalystAlicePOVM
        G n S D e a₀ x).effect a ⊗ₖ
      (exactSourceGlobalCatalystBobPOVM
        G n S D e b₀ y).effect b
    else 0

def exactSourceGlobalCatalystBasisEquiv
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) :
    ((ExactGlobalHistoryLocalIndex G n S D ×
       ExactGlobalHistoryLocalIndex G n S D) ×
      (Fin e × Fin e)) ≃
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) := by
  classical
  let localEquiv :
      (ExactGlobalHistoryLocalIndex G n S D × Fin e) ≃
        Fin (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D) * e) :=
    (Equiv.prodCongr
      (Fintype.equivFin
        (ExactGlobalHistoryLocalIndex G n S D))
      (Equiv.refl (Fin e))).trans finProdFinEquiv
  exact
    (Equiv.prodProdProdComm
      (ExactGlobalHistoryLocalIndex G n S D)
      (ExactGlobalHistoryLocalIndex G n S D)
      (Fin e) (Fin e)).trans (Equiv.prodCongr localEquiv localEquiv)

@[simp] theorem exactSourceGlobalCatalystAlicePOVM_effect_global
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) (a₀ a : A) (x : X)
    (i j : ExactGlobalHistoryLocalIndex G n S D)
    (k l : Fin e) :
    (exactSourceGlobalCatalystAlicePOVM
      G n S D e a₀ x).effect a
      (finProdFinEquiv
        ((Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D)) i, k))
      (finProdFinEquiv
        ((Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D)) j, l)) =
      (exactSourceGlobalAlicePOVM
        G n S D a₀ x).effect a i j *
        (if k = l then 1 else 0) := by
  classical
  change
    (reindexedPOVM finProdFinEquiv
      (purificationAlicePOVM (k := Fin e)
        (reindexedPOVM
          (Fintype.equivFin
            (ExactGlobalHistoryLocalIndex G n S D))
          (exactSourceGlobalAlicePOVM G n S D a₀ x)))).effect a
      (finProdFinEquiv
        ((Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D)) i, k))
      (finProdFinEquiv
        ((Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D)) j, l)) = _
  exact reindexedCatalystPOVM_effect
    (exactSourceGlobalAlicePOVM G n S D a₀ x)
    e a i j k l

theorem exactSourceGlobalCatalystWinningEffect_compression
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (i j :
      (ExactGlobalHistoryLocalIndex G n S D ×
       ExactGlobalHistoryLocalIndex G n S D) ×
      (Fin e × Fin e)) :
    exactSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y
      (exactSourceGlobalCatalystBasisEquiv G n S D e i)
      (exactSourceGlobalCatalystBasisEquiv G n S D e j) =
      ((exactSourceGlobalWinningEffect G n S D a₀ b₀ x y) ⊗ₖ
        (1 : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ)) i j := by
  classical
  rcases i with ⟨⟨ia, ib⟩, ⟨ka, kb⟩⟩
  rcases j with ⟨⟨ja, jb⟩, ⟨la, lb⟩⟩
  by_cases alice_residual : ka = la
  · subst la
    by_cases bob_residual : kb = lb
    · subst lb
      simp only [exactSourceGlobalCatalystWinningEffect,
        exactSourceGlobalWinningEffect, Matrix.sum_apply,
        Matrix.kroneckerMap_apply,
        exactSourceGlobalCatalystBasisEquiv,
        Equiv.trans_apply, Equiv.prodCongr_apply,
        Equiv.prodProdProdComm_apply, Matrix.one_apply,
        ite_true, mul_one]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs with winning
      · simp [Matrix.kroneckerMap_apply,
                    exactSourceGlobalCatalystAlicePOVM_effect_global,
          exactSourceGlobalCatalystBobPOVM_effect]
      · rfl
    · simp [exactSourceGlobalCatalystWinningEffect,
        exactSourceGlobalWinningEffect,
        exactSourceGlobalCatalystBasisEquiv,
        Matrix.sum_apply, Matrix.kroneckerMap_apply,                         bob_residual]
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      split_ifs with winning
      · simp [Matrix.kroneckerMap_apply,
          exactSourceGlobalCatalystAlicePOVM_effect_global,
          exactSourceGlobalCatalystBobPOVM_effect,
          bob_residual]
      · rfl
  · simp [exactSourceGlobalCatalystWinningEffect,
      exactSourceGlobalWinningEffect,
      exactSourceGlobalCatalystBasisEquiv,
      Matrix.sum_apply, Matrix.kroneckerMap_apply,                   alice_residual]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs with winning
    · simp [Matrix.kroneckerMap_apply,
        exactSourceGlobalCatalystAlicePOVM_effect_global,
        exactSourceGlobalCatalystBobPOVM_effect,
        alice_residual]
    · rfl

theorem exactSourceGlobalCatalystWinningEffect_tensor_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (e : ℕ) (residual_positive : 0 < e)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (exactSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ x y))
      (tensorEmbezzlementTarget (n := e)
        (exactGlobalHistoryFinPsi G n S D r x y)) =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          ExactGlobalHistoryLocalIndex G n S D ×
          ExactGlobalHistoryLocalIndex G n S D)
        (𝕜 := ℂ)
        (exactSourceGlobalWinningEffect
          G n S D a₀ b₀ x y))
      (exactGlobalHistoryVector G n S D r
        (exactPsi G n S D r x y)) := by
  classical
  let source := exactGlobalHistoryVector G n S D r
    (exactPsi G n S D r x y)
  let residual := embezzlementState e
  let tensor : EuclideanSpace ℂ
      ((ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D) ×
       (Fin e × Fin e)) :=
    toLp 2 (fun q => source q.1 * residual q.2)
  let basis := exactSourceGlobalCatalystBasisEquiv G n S D e
  calc
    _ = quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          (ExactGlobalHistoryLocalIndex G n S D ×
            ExactGlobalHistoryLocalIndex G n S D) ×
          (Fin e × Fin e))
        (𝕜 := ℂ)
        ((exactSourceGlobalWinningEffect
          G n S D a₀ b₀ x y) ⊗ₖ
          (1 : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ)))
      tensor := by
        apply matrixQuadraticExpectation_injective
          basis basis.injective
        · intro i
          rcases i with ⟨⟨ia, ib⟩, ⟨ka, kb⟩⟩
          have alice_system :
              (finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D))
                  ia, ka)).divNat =
                (Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ia := by
            exact congrArg Prod.fst
              (Equiv.symm_apply_apply finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ia, ka))
          have alice_residual :
              (finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D))
                  ia, ka)).modNat = ka := by
            exact congrArg Prod.snd
              (Equiv.symm_apply_apply finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ia, ka))
          have bob_system :
              (finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D))
                  ib, kb)).divNat =
                (Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ib := by
            exact congrArg Prod.fst
              (Equiv.symm_apply_apply finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ib, kb))
          have bob_residual :
              (finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D))
                  ib, kb)).modNat = kb := by
            exact congrArg Prod.snd
              (Equiv.symm_apply_apply finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ib, kb))
          simp [basis, tensor, source, residual,
            exactSourceGlobalCatalystBasisEquiv,
            tensorEmbezzlementTarget,
            exactGlobalHistoryFinPsi,
            exactGlobalHistoryFinReindex,
            LinearIsometryEquiv.piLpCongrLeft_apply,
            Equiv.piCongrLeft'_apply,
            alice_system, alice_residual,
            bob_system, bob_residual]
        · intro j outside
          exact False.elim
            (outside (basis.symm j) (basis.apply_symm_apply j))
        · exact exactSourceGlobalCatalystWinningEffect_compression
            G n S D e a₀ b₀ x y
    _ = _ := residualIdentity_quadratic
      (exactSourceGlobalWinningEffect G n S D a₀ b₀ x y)
      source residual
      (embezzlementState_norm e residual_positive)

theorem exactPsi_eq_padded_normalizedPureVector_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y)
    (nonzero : exactUnnormalizedPsi G n S D r x y ≠ 0) :
    exactPsi G n S D r x y =
      exactPaddedVector G n S D r
        (normalizedPureVector
          (exactUnnormalizedPsi G n S D r x y)) := by
  classical
  let raw := exactUnnormalizedPsi G n S D r x y
  have padded_nonzero :
      exactPaddedVector G n S D r raw ≠ 0 := by
    intro zero
    apply nonzero
    apply norm_eq_zero.mp
    rw [← exactPaddedVector_norm G n S D r raw, zero]
    exact norm_zero
  unfold exactPsi normalizeOrDefault
  rw [if_neg padded_nonzero, NormedSpace.normalize,
    exactPaddedVector_norm]
  ext q
  rcases q with ⟨i, j⟩
  rcases i with i | (i | i) <;>
    rcases j with j | (j | j) <;>
    simp [exactPaddedVector, normalizedPureVector,
      smul_eq_mul]

theorem exactSourceGlobalCatalystWinningEffect_law_supported_verifier
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (e : ℕ) (residual_positive : 0 < e)
    (a₀ : A) (b₀ : B)
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    exactSourceConditionalWinningProbability G n S D t =
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            Fin (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D) * e) ×
            Fin (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D) * e))
          (𝕜 := ℂ)
          (exactSourceGlobalCatalystWinningEffect
            G n S D e a₀ b₀ t.2.1 t.2.2.1))
        (tensorEmbezzlementTarget (n := e)
          (exactGlobalHistoryFinPsi G n S D t.2.2.2
            t.2.1 t.2.2.1)) := by
  classical
  have coordinate :=
    exactLocallySampleableLaw_coordinate_eq_of_ne_zero
      G n S D t supported
  have accepted :=
    exactLocallySampleableLaw_accepted_of_ne_zero
      G n S D t supported
  have fiber :=
    exactLocallySampleableLaw_fiber_ne_zero_of_ne_zero
      G n S D t supported
  have raw_nonzero :=
    exactLocallySampleableLaw_psi_ne_zero_of_ne_zero
      G n S D t supported
  rw [exactSourceGlobalCatalystWinningEffect_tensor_quadratic
    G n S D t.2.2.2 e residual_positive a₀ b₀ t.2.1 t.2.2.1]
  rw [exactPsi_eq_padded_normalizedPureVector_of_ne_zero
    G n S D t.2.2.2 t.2.1 t.2.2.1 raw_nonzero]
  rw [exactSourceGlobalWinningEffect_quadratic
    G n S D t.2.2.2 a₀ b₀ t.2.1 t.2.2.1]
  have tuple :
      t = (t.2.2.2.seed.coordinate,
        t.2.1, t.2.2.1, t.2.2.2) := by
    rcases t with ⟨i, x, y, r⟩
    simpa using coordinate
  conv_lhs => rw [tuple]
  exact
    exactSourceConditionalWinningProbability_eq_normalized_verifier
      G n S D positive t.2.2.2 accepted a₀ b₀
      t.2.1 t.2.2.1 fiber

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

def unconditionalMatchedVerifierTensor
    {s t : Type*} [Fintype s] [Fintype t]
    (target : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    EuclideanSpace ℂ (s × t) :=
  toLp 2 (fun q : s × t => target q.1 * work q.2)

theorem unconditionalMatchedVerifierTensor_norm_sq
    {s t : Type*} [Fintype s] [Fintype t]
    (target : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    ‖unconditionalMatchedVerifierTensor target work‖ ^ 2 =
      ‖target‖ ^ 2 * ‖work‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  change
    (∑ i : s, ∑ j : t, ‖target i * work j‖ ^ 2) =
      ‖target‖ ^ 2 * ‖work‖ ^ 2
  simp_rw [norm_mul, mul_pow]
  rw [← Fintype.sum_mul_sum, ← EuclideanSpace.norm_sq_eq,
    ← EuclideanSpace.norm_sq_eq]

theorem unconditionalMatchedVerifierTensor_norm
    {s t : Type*} [Fintype s] [Fintype t]
    (target : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    ‖unconditionalMatchedVerifierTensor target work‖ =
      ‖target‖ * ‖work‖ := by
  have squared :=
    unconditionalMatchedVerifierTensor_norm_sq target work
  nlinarith [
    norm_nonneg (unconditionalMatchedVerifierTensor target work),
    norm_nonneg target, norm_nonneg work,
    mul_nonneg (norm_nonneg target) (norm_nonneg work)]

theorem unconditionalMatchedVerifierEffect_tensor_complement
    {s t : Type*} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (effect : Matrix s s ℂ) :
    (1 : Matrix (s × t) (s × t) ℂ) -
        (effect ⊗ₖ (1 : Matrix t t ℂ)) =
      (1 - effect) ⊗ₖ (1 : Matrix t t ℂ) := by
  classical
  ext ⟨i, k⟩ ⟨j, l⟩
  by_cases same_target : i = j
  · subst j
    by_cases same_work : k = l
    · subst l
      simp [Matrix.kroneckerMap_apply]
    · simp [Matrix.kroneckerMap_apply, same_work]
  · by_cases same_work : k = l
    · subst l
      simp [Matrix.kroneckerMap_apply, same_target]
    · simp [Matrix.kroneckerMap_apply, same_target, same_work]

theorem unconditionalMatchedVerifierEffect_tensor_posSemidef
    {s t : Type*} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (effect : Matrix s s ℂ)
    (positive : effect.PosSemidef) :
    (effect ⊗ₖ (1 : Matrix t t ℂ)).PosSemidef :=
  positive.kronecker Matrix.PosSemidef.one

theorem unconditionalMatchedVerifierEffect_tensor_complement_posSemidef
    {s t : Type*} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (effect : Matrix s s ℂ)
    (complement : (1 - effect).PosSemidef) :
    ((1 : Matrix (s × t) (s × t) ℂ) -
      (effect ⊗ₖ (1 : Matrix t t ℂ))).PosSemidef := by
  rw [unconditionalMatchedVerifierEffect_tensor_complement]
  exact complement.kronecker Matrix.PosSemidef.one

theorem unconditionalMatchedVerifierEffect_tensor_norm_le_one
    {s t : Type*} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (effect : Matrix s s ℂ)
    (positive : effect.PosSemidef)
    (complement : (1 - effect).PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
        (effect ⊗ₖ (1 : Matrix t t ℂ))‖ ≤ 1 := by
  exact matrixEffectCLM_norm_le_one
    (effect ⊗ₖ (1 : Matrix t t ℂ))
    (unconditionalMatchedVerifierEffect_tensor_posSemidef
      effect positive)
    (unconditionalMatchedVerifierEffect_tensor_complement_posSemidef
      effect complement)

theorem unconditionalMatchedVerifierEffect_tensor_quadratic
    {s t : Type*} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (effect : Matrix s s ℂ)
    (target : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
        (effect ⊗ₖ (1 : Matrix t t ℂ)))
      (unconditionalMatchedVerifierTensor target work) =
      ‖work‖ ^ 2 *
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := s) (𝕜 := ℂ) effect)
          target := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  have residual_complex :
      (∑ k : t, work k * star (work k)) =
        (↑(‖work‖ ^ 2) : ℂ) := by
    calc
      (∑ k : t, work k * star (work k)) =
          (↑(∑ k : t, ‖work k‖ ^ 2) : ℂ) := by
            push_cast
            apply Finset.sum_congr rfl
            intro k _
            simpa [Complex.normSq_eq_norm_sq] using
              Complex.mul_conj (work k)
      _ = (↑(‖work‖ ^ 2) : ℂ) := by
            rw [← EuclideanSpace.norm_sq_eq]
  change
    (∑ i : s × t,
      (∑ j : s × t,
        (effect i.1 j.1 * (if i.2 = j.2 then 1 else 0)) *
          (target j.1 * work j.2)) *
        star (target i.1 * work i.2)).re =
      ‖work‖ ^ 2 *
        (∑ i : s, (∑ j : s, effect i j * target j) *
          star (target i)).re
  rw [Fintype.sum_prod_type]
  have complex_factor :
      (∑ i : s, ∑ k : t,
        (∑ j : s × t,
          (effect i j.1 * (if k = j.2 then 1 else 0)) *
            (target j.1 * work j.2)) *
          star (target i * work k)) =
        (∑ i : s,
          (∑ j : s, effect i j * target j) * star (target i)) *
          (↑(‖work‖ ^ 2) : ℂ) := by
    calc
      (∑ i : s, ∑ k : t,
        (∑ j : s × t,
          (effect i j.1 * (if k = j.2 then 1 else 0)) *
            (target j.1 * work j.2)) *
          star (target i * work k)) =
        ∑ i : s, ∑ k : t,
          ((∑ j : s, effect i j * target j) * work k) *
            star (target i * work k) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro k _
              congr 1
              rw [Fintype.sum_prod_type]
              simp [mul_ite, ite_mul, Finset.sum_mul, mul_assoc]
      _ = ∑ i : s,
        ((∑ j : s, effect i j * target j) * star (target i)) *
          (∑ k : t, work k * star (work k)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            simp only [star_mul]
            ring
      _ = (∑ i : s,
          (∑ j : s, effect i j * target j) * star (target i)) *
          (↑(‖work‖ ^ 2) : ℂ) := by
            rw [residual_complex, Finset.sum_mul]
  rw [complex_factor, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

abbrev UnconditionalSelectedCopyLocalIndex
    (B d N m : ℕ) :=
  Σ _ : Fin B × Fin d, Fin (N * m)

def unconditionalSelectedCopyCleanedStage
    {d N B m : ℕ}
    (Q : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    EuclideanSpace ℂ
      (UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) :=
  dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
    Q w ξ ζ A C
    (dSVDensityRationalPublicBucketPhysicalCoherentMixedState
      (N := N) (B := B) w m ξ ζ)

def unconditionalSelectedCopyIdealStage
    {d N B m : ℕ}
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) :=
  dSVDensityRationalPublicBucketPhysicalCoherentTargetState
    (N := N) (B := B) w m ξ ζ

def unconditionalSelectedCopyRetainedWork
    {S N d L : ℕ} {τ : Type*} [Fintype τ]
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ τ) :
    EuclideanSpace ℂ
      ((Fin j.val →
        (DSVUniformDensityThresholdLocalIndex N d ×
         DSVUniformDensityThresholdLocalIndex N d)) × τ) :=
  unconditionalMatchedVerifierTensor
    (dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
      (N := N) width schedule ξ ζ j)
    rest

def unconditionalSelectedCopyCleanedMatchedBranch
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ]
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) (rest : EuclideanSpace ℂ τ) :
    EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex B d N m ×
          UnconditionalSelectedCopyLocalIndex B d N m) ×
        ((Fin j.val →
          (DSVUniformDensityThresholdLocalIndex N d ×
            DSVUniformDensityThresholdLocalIndex N d)) × τ)) :=
  unconditionalMatchedVerifierTensor
    (unconditionalSelectedCopyCleanedStage
      (N := N) (B := B) (m := m)
      Q (width (schedule j)) ξ ζ A C)
    (unconditionalSelectedCopyRetainedWork
      (N := N) width schedule ξ ζ j rest)

def unconditionalSelectedCopyIdealMatchedBranch
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ]
    (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ τ) :
    EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex B d N m ×
          UnconditionalSelectedCopyLocalIndex B d N m) ×
        ((Fin j.val →
          (DSVUniformDensityThresholdLocalIndex N d ×
            DSVUniformDensityThresholdLocalIndex N d)) × τ)) :=
  unconditionalMatchedVerifierTensor
    (unconditionalSelectedCopyIdealStage
      (N := N) (B := B) (m := m) (width (schedule j)) ξ ζ)
    (unconditionalSelectedCopyRetainedWork
      (N := N) width schedule ξ ζ j rest)

theorem unconditionalSelectedCopy_tensor_sub
    {s τ : Type*} [Fintype s] [Fintype τ]
    (x y : EuclideanSpace ℂ s) (work : EuclideanSpace ℂ τ) :
    unconditionalMatchedVerifierTensor x work -
        unconditionalMatchedVerifierTensor y work =
      unconditionalMatchedVerifierTensor (x - y) work := by
  ext ⟨i, j⟩
  change x i * work j - y i * work j =
    (x i - y i) * work j
  ring

theorem unconditionalSelectedCopyRetainedWork_norm_sq
    {S N d L : ℕ} {τ : Type*} [Fintype τ]
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ τ) :
    ‖unconditionalSelectedCopyRetainedWork
        (N := N) width schedule ξ ζ j rest‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ j.val * ‖rest‖ ^ 2 := by
  unfold unconditionalSelectedCopyRetainedWork
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_norm_sq]

theorem unconditionalSelectedCopyMatchedBranch_deviation_sq
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ]
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) (rest : EuclideanSpace ℂ τ)
    (rest_unit : ‖rest‖ = 1) :
    ‖unconditionalSelectedCopyCleanedMatchedBranch
          Q width schedule ξ ζ A C j rest -
        unconditionalSelectedCopyIdealMatchedBranch
          (B := B) (m := m) width schedule ξ ζ j rest‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousCommonStopGaugeStageError
          Q (width (schedule j)) m ξ ζ A C := by
  unfold unconditionalSelectedCopyCleanedMatchedBranch
    unconditionalSelectedCopyIdealMatchedBranch
  rw [unconditionalSelectedCopy_tensor_sub,
    unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopyRetainedWork_norm_sq,
    rest_unit]
  unfold dSVDensityRationalHeterogeneousCommonStopGaugeStageError
    unconditionalSelectedCopyCleanedStage
    unconditionalSelectedCopyIdealStage
  ring

theorem unconditionalSelectedCopy_weightedAffine
    {ι : Type*} [Fintype ι]
    (weight error asynchronous : ι → ℝ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i, weight i) = 1)
    (coefficient residual : ℝ)
    (pointwise : ∀ i, error i ≤ coefficient * asynchronous i + residual) :
    (∑ i, weight i * error i) ≤
      coefficient * (∑ i, weight i * asynchronous i) + residual := by
  classical
  calc
    (∑ i, weight i * error i) ≤
        ∑ i, weight i *
          (coefficient * asynchronous i + residual) := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left
              (pointwise i) (nonnegative i)
    _ = coefficient * (∑ i, weight i * asynchronous i) +
          (∑ i, weight i) * residual := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib,
              Finset.mul_sum, Finset.sum_mul]
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = coefficient * (∑ i, weight i * asynchronous i) + residual := by
          rw [normalized]
          ring

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalMatchedVerifierAggregate_dependent_continuity
    {J : Type*} [Fintype J]
    {H : J → Type*}
    [∀ j, NormedAddCommGroup (H j)]
    [∀ j, InnerProductSpace ℂ (H j)]
    (weight : J → ℝ)
    (nonnegative : ∀ j, 0 ≤ weight j)
    (effect : (j : J) → (H j →L[ℂ] H j))
    (contraction : ∀ j, ‖effect j‖ ≤ 1)
    (actual ideal : (j : J) → H j) :
    |(∑ j : J, weight j * quadraticExpectation (effect j) (actual j)) -
      (∑ j : J, weight j * quadraticExpectation (effect j) (ideal j))| ≤
      (Real.sqrt (∑ j : J, weight j * ‖actual j‖ ^ 2) +
        Real.sqrt (∑ j : J, weight j * ‖ideal j‖ ^ 2)) *
        Real.sqrt (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) := by
  classical
  have point (j : J) :
      |quadraticExpectation (effect j) (actual j) -
        quadraticExpectation (effect j) (ideal j)| ≤
        (‖actual j‖ + ‖ideal j‖) * ‖actual j - ideal j‖ :=
    quadraticExpectation_sub_le
      (effect j) (contraction j) (actual j) (ideal j)
  calc
    |(∑ j : J, weight j * quadraticExpectation (effect j) (actual j)) -
        (∑ j : J, weight j * quadraticExpectation (effect j) (ideal j))| =
      |∑ j : J, weight j *
        (quadraticExpectation (effect j) (actual j) -
          quadraticExpectation (effect j) (ideal j))| := by
            congr 1
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib]
    _ ≤ ∑ j : J, |weight j *
      (quadraticExpectation (effect j) (actual j) -
        quadraticExpectation (effect j) (ideal j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : J, weight j *
      |quadraticExpectation (effect j) (actual j) -
        quadraticExpectation (effect j) (ideal j)| := by
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_mul, abs_of_nonneg (nonnegative j)]
    _ ≤ ∑ j : J, weight j *
      ((‖actual j‖ + ‖ideal j‖) * ‖actual j - ideal j‖) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (point j) (nonnegative j)
    _ = (∑ j : J, weight j * ‖actual j‖ * ‖actual j - ideal j‖) +
        (∑ j : J, weight j * ‖ideal j‖ * ‖actual j - ideal j‖) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ ≤ Real.sqrt (∑ j : J, weight j * ‖actual j‖ ^ 2) *
          Real.sqrt (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) +
        Real.sqrt (∑ j : J, weight j * ‖ideal j‖ ^ 2) *
          Real.sqrt (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) := by
          exact add_le_add
            (weighted_real_cauchy weight
              (fun j => ‖actual j‖)
              (fun j => ‖actual j - ideal j‖) nonnegative)
            (weighted_real_cauchy weight
              (fun j => ‖ideal j‖)
              (fun j => ‖actual j - ideal j‖) nonnegative)
    _ = (Real.sqrt (∑ j : J, weight j * ‖actual j‖ ^ 2) +
        Real.sqrt (∑ j : J, weight j * ‖ideal j‖ ^ 2)) *
        Real.sqrt (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) := by
          ring

theorem unconditionalMatchedVerifierAggregate_dependent_le
    {J : Type*} [Fintype J]
    {H : J → Type*}
    [∀ j, NormedAddCommGroup (H j)]
    [∀ j, InnerProductSpace ℂ (H j)]
    (weight : J → ℝ)
    (nonnegative : ∀ j, 0 ≤ weight j)
    (effect : (j : J) → (H j →L[ℂ] H j))
    (contraction : ∀ j, ‖effect j‖ ≤ 1)
    (actual ideal : (j : J) → H j)
    (actual_mass : (∑ j : J, weight j * ‖actual j‖ ^ 2) ≤ 1)
    (ideal_mass : (∑ j : J, weight j * ‖ideal j‖ ^ 2) ≤ 1)
    (Δ : ℝ)
    (deviation :
      (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) ≤ Δ) :
    |(∑ j : J, weight j * quadraticExpectation (effect j) (actual j)) -
      (∑ j : J, weight j * quadraticExpectation (effect j) (ideal j))| ≤
      2 * Real.sqrt Δ := by
  have actual_nonnegative :
      0 ≤ ∑ j : J, weight j * ‖actual j‖ ^ 2 :=
    Finset.sum_nonneg
      (fun j _ => mul_nonneg (nonnegative j) (sq_nonneg _))
  have ideal_nonnegative :
      0 ≤ ∑ j : J, weight j * ‖ideal j‖ ^ 2 :=
    Finset.sum_nonneg
      (fun j _ => mul_nonneg (nonnegative j) (sq_nonneg _))
  have error_nonnegative :
      0 ≤ ∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2 :=
    Finset.sum_nonneg
      (fun j _ => mul_nonneg (nonnegative j) (sq_nonneg _))
  have actual_root :
      Real.sqrt (∑ j : J, weight j * ‖actual j‖ ^ 2) ≤ 1 := by
    nlinarith [
      Real.sq_sqrt actual_nonnegative,
      Real.sqrt_nonneg (∑ j : J, weight j * ‖actual j‖ ^ 2)]
  have ideal_root :
      Real.sqrt (∑ j : J, weight j * ‖ideal j‖ ^ 2) ≤ 1 := by
    nlinarith [
      Real.sq_sqrt ideal_nonnegative,
      Real.sqrt_nonneg (∑ j : J, weight j * ‖ideal j‖ ^ 2)]
  calc
    |(∑ j : J, weight j * quadraticExpectation (effect j) (actual j)) -
        (∑ j : J, weight j * quadraticExpectation (effect j) (ideal j))| ≤
      (Real.sqrt (∑ j : J, weight j * ‖actual j‖ ^ 2) +
        Real.sqrt (∑ j : J, weight j * ‖ideal j‖ ^ 2)) *
        Real.sqrt (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) :=
          unconditionalMatchedVerifierAggregate_dependent_continuity
            weight nonnegative effect contraction actual ideal
    _ ≤ 2 * Real.sqrt Δ := by
      apply mul_le_mul
      · linarith
      · exact Real.sqrt_le_sqrt deviation
      · exact Real.sqrt_nonneg _
      · norm_num

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

def unconditionalConjugatePureVector
    {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  toLp 2 (fun i : ι => star (z i))

@[simp] theorem unconditionalConjugatePureVector_apply
    {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℂ ι) (i : ι) :
    unconditionalConjugatePureVector z i = star (z i) := by
  rfl

theorem unconditionalConjugatePureVector_norm_sq
    {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    ‖unconditionalConjugatePureVector z‖ ^ 2 = ‖z‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq]

theorem unconditionalConjugatePureVector_norm
    {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    ‖unconditionalConjugatePureVector z‖ = ‖z‖ := by
  have squares := unconditionalConjugatePureVector_norm_sq z
  nlinarith [norm_nonneg (unconditionalConjugatePureVector z),
    norm_nonneg z]

def unconditionalConjugatePOVM
    {A ι : Type*} [Fintype A] [Fintype ι] [DecidableEq ι]
    (P : POVM A ι) : POVM A ι where
  effect a := (P.effect a).transpose
  positive a := (P.positive a).transpose
  complete := by
    classical
    rw [← Matrix.transpose_sum]
    rw [P.complete, Matrix.transpose_one]

theorem unconditionalConjugatePureVector_transpose_quadratic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (z : EuclideanSpace ℂ ι) :
    quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M.transpose)
        (unconditionalConjugatePureVector z) =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M) z := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  congr 1
  simp only [Matrix.transpose_apply,
    unconditionalConjugatePureVector_apply, star_star]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem unconditionalConjugatePOVM_jointEffect
    {A B ι κ : Type*} [Fintype A] [Fintype B]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : POVM A ι) (Q : POVM B κ) (a : A) (b : B) :
    (unconditionalConjugatePOVM P).effect a ⊗ₖ
        (unconditionalConjugatePOVM Q).effect b =
      (P.effect a ⊗ₖ Q.effect b).transpose := by
  exact Matrix.kroneckerMap_transpose (fun x y : ℂ => x * y)
    (P.effect a) (Q.effect b)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def unconditionalConjugateSourceGlobalCatalystWinningEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    Matrix
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e))
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystAlicePOVM
          G n S D e a₀ x)).effect a ⊗ₖ
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystBobPOVM
          G n S D e b₀ y)).effect b
    else 0

theorem
    unconditionalConjugateSourceGlobalCatalystWinningEffect_eq_transpose
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    unconditionalConjugateSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y =
      (exactSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y).transpose := by
  classical
  unfold unconditionalConjugateSourceGlobalCatalystWinningEffect
    exactSourceGlobalCatalystWinningEffect
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact unconditionalConjugatePOVM_jointEffect
      (exactSourceGlobalCatalystAlicePOVM G n S D e a₀ x)
      (exactSourceGlobalCatalystBobPOVM G n S D e b₀ y)
      a b
  · exact Matrix.transpose_zero.symm

theorem unconditionalConjugateSourceGlobalCatalystWinningEffect_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (z : EuclideanSpace ℂ
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e))) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (unconditionalConjugateSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ x y))
      (unconditionalConjugatePureVector z) =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (exactSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ x y)) z := by
  calc
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            Fin (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D) * e) ×
            Fin (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D) * e))
          (𝕜 := ℂ)
          (exactSourceGlobalCatalystWinningEffect
            G n S D e a₀ b₀ x y).transpose)
        (unconditionalConjugatePureVector z) := by
          exact congrArg
            (fun M =>
              quadraticExpectation
                (Matrix.toEuclideanCLM
                  (n :=
                    Fin (Fintype.card
                      (ExactGlobalHistoryLocalIndex G n S D) * e) ×
                    Fin (Fintype.card
                      (ExactGlobalHistoryLocalIndex G n S D) * e))
                  (𝕜 := ℂ) M)
                (unconditionalConjugatePureVector z))
            (unconditionalConjugateSourceGlobalCatalystWinningEffect_eq_transpose
              G n S D e a₀ b₀ x y)
    _ = _ := unconditionalConjugatePureVector_transpose_quadratic
      (exactSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y) z

theorem
    unconditionalConjugateSourceGlobalCatalystWinningEffect_law_supported
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (e : ℕ) (residual_positive : 0 < e)
    (a₀ : A) (b₀ : B)
    (u : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D u ≠ 0) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (unconditionalConjugateSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ u.2.1 u.2.2.1))
      (unconditionalConjugatePureVector
        (tensorEmbezzlementTarget (n := e)
          (exactGlobalHistoryFinPsi G n S D u.2.2.2
            u.2.1 u.2.2.1))) =
    exactSourceConditionalWinningProbability G n S D u := by
  rw [unconditionalConjugateSourceGlobalCatalystWinningEffect_quadratic]
  exact
    (exactSourceGlobalCatalystWinningEffect_law_supported_verifier
      G n S D positive e residual_positive a₀ b₀ u supported).symm

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem unconditionalPublicBucketPhysicalCoherentTarget_apply
    {d N B n : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin (N * n)) :
    dSVDensityRationalPublicBucketPhysicalCoherentTargetState
        (N := N) (B := B) w n ξ ζ
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      (ePRState B (φ, ψ) *
        (((‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
          dSVDensityRationalLocalSpectralPairBasisOverlap
            ξ ζ i j)) *
        ((Real.sqrt
            ((dSVDensityRationalPhysicalAcceptedRank
              w N ξ i).val : ℝ) : ℂ) *
          embezzlementState (N * n) (a, b)) := by
  rfl

theorem unconditionalCanonicalAcceptedCoefficient_sourceScale
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    Real.sqrt (w * (d : ℝ)) *
        (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) *
        Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) =
      dSVDensityRationalCanonicalAcceptedCoefficient w N ξ i := by
  have d_nonzero : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt dimension)
  have n_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt grid)
  have source_positive :
      0 < ‖sharedThresholdResourceRaw (d := Fin d)
        (fun _ : Fin N => (1 : ℝ))‖ := by
    have source_sq := dSVUniformDensityThresholdRaw_norm_sq N d
    have product_positive : (0 : ℝ) < (d : ℝ) * (N : ℝ) := by
      positivity
    nlinarith [norm_nonneg
      (sharedThresholdResourceRaw (d := Fin d)
        (fun _ : Fin N => (1 : ℝ)))]
  have left_nonnegative :
      0 ≤ Real.sqrt (w * (d : ℝ)) *
        (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) *
        Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) := by
    positivity
  have right_nonnegative :=
    dSVDensityRationalCanonicalAcceptedCoefficient_nonneg
      w N ξ i
  have same_square :
      (Real.sqrt (w * (d : ℝ)) *
        (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) *
        Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ)) ^ 2 =
        dSVDensityRationalCanonicalAcceptedCoefficient
          w N ξ i ^ 2 := by
    rw [mul_pow, mul_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ w * (d : ℝ)),
      inv_pow, dSVUniformDensityThresholdRaw_norm_sq,
      Real.sq_sqrt (by positivity :
        (0 : ℝ) ≤
          (dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val),
      dSVDensityRationalPhysicalAcceptedRank_targetCoefficient_sq
        width N ξ i]
    field_simp
  nlinarith

theorem unconditionalConjugateTranspose_eq_inverse
    {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (conjugateUnitary U : Matrix (Fin d) (Fin d) ℂ).transpose =
      ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) := by
  change U.val.conjTranspose.transpose.transpose =
    ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ)
  rw [Matrix.transpose_transpose]
  change star (U : Matrix (Fin d) (Fin d) ℂ) = _
  exact congrArg
    (fun V : Matrix.unitaryGroup (Fin d) ℂ =>
      (V : Matrix (Fin d) (Fin d) ℂ))
    (Unitary.star_eq_inv U)

theorem unconditionalConjugateBobBasisOverlapCancellation
    {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    (unitaryBasisOverlap U V : Matrix (Fin d) (Fin d) ℂ) *
        (conjugateUnitary V :
          Matrix (Fin d) (Fin d) ℂ).transpose =
      (conjugateUnitary U :
        Matrix (Fin d) (Fin d) ℂ).transpose := by
  rw [unconditionalConjugateTranspose_eq_inverse,
    unconditionalConjugateTranspose_eq_inverse]
  change
    (((U⁻¹ * V : Matrix.unitaryGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ)) *
      ((V⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) =
      ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ)
  change
    (((U⁻¹ * V) * V⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ) =
      ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ)
  simp

theorem unconditionalConjugateBobBasisOverlap_sum
    {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (i b : Fin d) :
    (∑ j : Fin d,
      unitaryBasisOverlap U V i j *
        star ((V : Matrix (Fin d) (Fin d) ℂ) b j)) =
      star ((U : Matrix (Fin d) (Fin d) ℂ) b i) := by
  have identity := congrArg
    (fun M : Matrix (Fin d) (Fin d) ℂ => M i b)
    (unconditionalConjugateBobBasisOverlapCancellation U V)
  simpa [Matrix.mul_apply, Matrix.transpose_apply,
    conjugateUnitary_apply] using identity

theorem unconditionalRationalMixedConjugateBobSpectral_sum
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i b : Fin d) :
    (∑ j : Fin d,
      dSVDensityRationalLocalSpectralPairBasisOverlap ξ ζ i j *
        star
          ((dSVUniformDensityThresholdLeftBobBasis ζ :
            Matrix (Fin d) (Fin d) ℂ) b j)) =
      star
        ((dSVUniformDensityThresholdLeftBobBasis ξ :
          Matrix (Fin d) (Fin d) ℂ) b i) := by
  exact unconditionalConjugateBobBasisOverlap_sum
    (dSVUniformDensityThresholdLeftBobBasis ξ)
    (dSVUniformDensityThresholdLeftBobBasis ζ) i b

theorem unconditionalConjugateCanonicalAcceptedTarget_apply
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d)
    (a b : Fin d) :
    star
        (dSVDensityRationalCanonicalAcceptedTarget w N ξ
          (a, b)) =
      ∑ i : Fin d,
        (dSVDensityRationalCanonicalAcceptedCoefficient
          w N ξ i : ℂ) *
        star
          ((dSVDensityRationalCanonicalAliceBasis ξ :
            Matrix (Fin d) (Fin d) ℂ) a i) *
        star
          ((dSVUniformDensityThresholdLeftBobBasis ξ :
            Matrix (Fin d) (Fin d) ℂ) b i) := by
  unfold dSVDensityRationalCanonicalAcceptedTarget
  rw [schmidtVector_apply]
  simp

theorem unconditionalMixedConjugateCanonicalAcceptedTarget_sum
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Fin d) :
    (∑ i : Fin d, ∑ j : Fin d,
      (Real.sqrt (w * (d : ℝ)) : ℂ) *
        ((‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
        (Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) : ℂ) *
        star
          ((dSVDensityRationalCanonicalAliceBasis ξ :
            Matrix (Fin d) (Fin d) ℂ) a i) *
        dSVDensityRationalLocalSpectralPairBasisOverlap
          ξ ζ i j *
        star
          ((dSVUniformDensityThresholdLeftBobBasis ζ :
            Matrix (Fin d) (Fin d) ℂ) b j)) =
      star
        (dSVDensityRationalCanonicalAcceptedTarget
          w N ξ (a, b)) := by
  classical
  calc
    _ =
        ∑ i : Fin d,
          ((Real.sqrt (w * (d : ℝ)) : ℂ) *
            ((‖sharedThresholdResourceRaw (d := Fin d)
              (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
            (Real.sqrt
              ((dSVDensityRationalPhysicalAcceptedRank
                w N ξ i).val : ℝ) : ℂ) *
            star
              ((dSVDensityRationalCanonicalAliceBasis ξ :
                Matrix (Fin d) (Fin d) ℂ) a i)) *
          (∑ j : Fin d,
            dSVDensityRationalLocalSpectralPairBasisOverlap
              ξ ζ i j *
            star
              ((dSVUniformDensityThresholdLeftBobBasis ζ :
                Matrix (Fin d) (Fin d) ℂ) b j)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ =
        ∑ i : Fin d,
          (dSVDensityRationalCanonicalAcceptedCoefficient
            w N ξ i : ℂ) *
          star
            ((dSVDensityRationalCanonicalAliceBasis ξ :
              Matrix (Fin d) (Fin d) ℂ) a i) *
          star
            ((dSVUniformDensityThresholdLeftBobBasis ξ :
              Matrix (Fin d) (Fin d) ℂ) b i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [unconditionalRationalMixedConjugateBobSpectral_sum]
          have coefficient := congrArg (fun x : ℝ => (x : ℂ))
            (unconditionalCanonicalAcceptedCoefficient_sourceScale
              width grid dimension ξ i)
          push_cast at coefficient
          rw [← coefficient]
          push_cast
          ring
    _ = _ :=
      (unconditionalConjugateCanonicalAcceptedTarget_apply
        w ξ a b).symm

def unconditionalMixedConjugateSigmaAtomLift
    {d m : ℕ} (B : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup
      (Σ _ : Fin B × Fin d, Fin m) ℂ := by
  classical
  let e : ((Fin B × Fin d) × Fin m) ≃
      (Σ _ : Fin B × Fin d, Fin m) :=
    (Equiv.sigmaEquivProd (Fin B × Fin d) (Fin m)).symm
  let M : Matrix ((Fin B × Fin d) × Fin m)
      ((Fin B × Fin d) × Fin m) ℂ :=
    ((1 : Matrix (Fin B) (Fin B) ℂ) ⊗ₖ
      (U : Matrix (Fin d) (Fin d) ℂ)) ⊗ₖ
      (1 : Matrix (Fin m) (Fin m) ℂ)
  have unitary : M ∈ Matrix.unitaryGroup
      ((Fin B × Fin d) × Fin m) ℂ :=
    Matrix.kronecker_mem_unitary
      (Matrix.kronecker_mem_unitary
        (Matrix.unitaryGroup (Fin B) ℂ).one_mem U.property)
      (Matrix.unitaryGroup (Fin m) ℂ).one_mem
  refine ⟨Matrix.reindex e e M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have compatible :
      star (Matrix.reindex e e M) =
        Matrix.reindex e e (star M) := by
    ext i j
    simp [Matrix.star_eq_conjTranspose,
      Matrix.reindex_apply, Matrix.conjTranspose_apply]
  rw [compatible]
  change
    (Matrix.reindexRingEquiv ℂ e) (star M) *
      (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp unitary]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

theorem unconditionalMixedConjugateSigmaAtomLift_apply
    {d m : ℕ} (B : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin m) :
    (unconditionalMixedConjugateSigmaAtomLift (m := m) B U :
      Matrix (Σ _ : Fin B × Fin d, Fin m)
        (Σ _ : Fin B × Fin d, Fin m) ℂ)
      ⟨(φ, i), a⟩ ⟨(ψ, j), b⟩ =
      if φ = ψ ∧ a = b then
        (U : Matrix (Fin d) (Fin d) ℂ) i j
      else 0 := by
  classical
  by_cases phase : φ = ψ <;>
    by_cases work : a = b <;>
      simp [unconditionalMixedConjugateSigmaAtomLift,
        Matrix.reindex_apply, Matrix.kroneckerMap_apply, phase, work]

def unconditionalMixedConjugateSigmaLocalAction
    {d m : ℕ} (B : ℕ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
        (Σ _ : Fin B × Fin d, Fin m))) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
        (Σ _ : Fin B × Fin d, Fin m)) :=
  toLp 2
    ((((unconditionalMixedConjugateSigmaAtomLift (m := m) B U :
          Matrix (Σ _ : Fin B × Fin d, Fin m)
            (Σ _ : Fin B × Fin d, Fin m) ℂ) ⊗ₖ
        (unconditionalMixedConjugateSigmaAtomLift (m := m) B V :
          Matrix (Σ _ : Fin B × Fin d, Fin m)
            (Σ _ : Fin B × Fin d, Fin m) ℂ)).mulVec
      (ofLp z)))

theorem unconditionalMixedConjugateSigmaLocalAction_apply
    {d m : ℕ} (B : ℕ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
        (Σ _ : Fin B × Fin d, Fin m)))
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin m) :
    unconditionalMixedConjugateSigmaLocalAction B U V z
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      ∑ k : Fin d, ∑ l : Fin d,
        (U : Matrix (Fin d) (Fin d) ℂ) i k *
        (V : Matrix (Fin d) (Fin d) ℂ) j l *
        z (⟨(φ, k), a⟩, ⟨(ψ, l), b⟩) := by
  classical
  simp [unconditionalMixedConjugateSigmaLocalAction,
    Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Fintype.sum_sigma,
    unconditionalMixedConjugateSigmaAtomLift_apply,
    mul_assoc, ite_and]

def unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
    {d N B : ℕ} (w : ℝ) (n : ℕ)
    (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin (N * n)) ×
       (Σ _ : Fin B × Fin d, Fin (N * n))) :=
  dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
    (unconditionalConjugatePureVector
      (dSVDensityRationalCanonicalAcceptedTarget w N ξ))
    (fun _ _ _ => embezzlementState (N * n))

theorem unconditionalMixedConjugateTargetCovariance
    {d N B n : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (ξ ζ : BipartiteUnitVector d) :
    Real.sqrt (w * (d : ℝ)) •
      unconditionalMixedConjugateSigmaLocalAction
        (m := N * n) B
        (conjugateUnitary
          (dSVDensityRationalCanonicalAliceBasis ξ))
        (conjugateUnitary
          (dSVUniformDensityThresholdLeftBobBasis ζ))
        (dSVDensityRationalPublicBucketPhysicalCoherentTargetState
          (N := N) (B := B) w n ξ ζ) =
    unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
        (B := B) w n ξ := by
  classical
  ext ⟨⟨⟨φ, i⟩, a⟩, ⟨⟨ψ, j⟩, b⟩⟩
  change
    (Real.sqrt (w * (d : ℝ)) : ℂ) *
      unconditionalMixedConjugateSigmaLocalAction B
        (conjugateUnitary
          (dSVDensityRationalCanonicalAliceBasis ξ))
        (conjugateUnitary
          (dSVUniformDensityThresholdLeftBobBasis ζ))
        (dSVDensityRationalPublicBucketPhysicalCoherentTargetState
          (N := N) (B := B) w n ξ ζ)
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      (ePRState B (φ, ψ) *
        star (dSVDensityRationalCanonicalAcceptedTarget
          w N ξ (i, j))) *
        embezzlementState (N * n) (a, b)
  rw [unconditionalMixedConjugateSigmaLocalAction_apply]
  simp_rw [conjugateUnitary_apply,
    unconditionalPublicBucketPhysicalCoherentTarget_apply]
  rw [← unconditionalMixedConjugateCanonicalAcceptedTarget_sum
    width grid dimension ξ ζ i j]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalSelectedCopy_coherentPhaseSigma_norm_sq
    {H : Type*} [Fintype H] {B m : ℕ}
    (phases : 0 < B)
    (history : EuclideanSpace ℂ (H × H))
    (work : H → H → EuclideanSpace ℂ (Fin m × Fin m)) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B history (fun _ i j => work i j)‖ ^ 2 =
      ‖dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
        history work‖ ^ 2 := by
  classical
  unfold dSVDensityRationalPublicBucketCoherentPhaseSigmaState
  rw [dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq,
    dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq]
  simp only [Fintype.sum_prod_type]
  simp_rw [
    dSVDensityRationalPublicBucketCoherentPhaseHistory_apply_norm_sq
      phases]
  have phase_ne : (B : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt phases)
  calc
    (∑ φ : Fin B, ∑ i : H, ∑ ψ : Fin B, ∑ j : H,
        (if φ = ψ then (B : ℝ)⁻¹ else 0) *
          ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2) =
        ∑ φ : Fin B, ∑ i : H, ∑ j : H,
          (B : ℝ)⁻¹ * ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro φ _
            apply Finset.sum_congr rfl
            intro i _
            simp
    _ = _ := by
      calc
        (∑ φ : Fin B, ∑ i : H, ∑ j : H,
            (B : ℝ)⁻¹ * ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2) =
          ∑ _φ : Fin B, (B : ℝ)⁻¹ *
            (∑ i : H, ∑ j : H,
              ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2) := by
              apply Finset.sum_congr rfl
              intro φ _
              simp_rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = _ := by
          rw [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          field_simp

theorem unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
    {H : Type*} [Fintype H] {B m : ℕ}
    (phases : 0 < B)
    (history : EuclideanSpace ℂ (H × H))
    (work : EuclideanSpace ℂ (Fin m × Fin m)) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B history (fun _ _ _ => work)‖ ^ 2 =
      ‖history‖ ^ 2 * ‖work‖ ^ 2 := by
  rw [unconditionalSelectedCopy_coherentPhaseSigma_norm_sq
    phases history (fun _ _ => work),
    dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq]
  calc
    (∑ i : H, ∑ j : H, ‖history (i, j)‖ ^ 2 * ‖work‖ ^ 2) =
        (∑ i : H, ∑ j : H, ‖history (i, j)‖ ^ 2) * ‖work‖ ^ 2 := by
          simp_rw [Finset.sum_mul]
    _ = _ := by
      congr 1
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]

theorem unconditionalSelectedCopy_conjugateAcceptedTarget_norm_sq
    {d N B m : ℕ} (phases : 0 < B)
    (grid : 0 < N) (harmonic : 0 < m)
    (w : ℝ) (ξ : BipartiteUnitVector d) :
    ‖unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
        (N := N) (B := B) w m ξ‖ ^ 2 =
      ‖dSVDensityRationalCanonicalAcceptedTarget w N ξ‖ ^ 2 := by
  unfold unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
  rw [unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
    phases]
  rw [unconditionalConjugatePureVector_norm_sq,
    embezzlementState_norm (N * m) (Nat.mul_pos grid harmonic)]
  ring

theorem unconditionalSelectedCopy_mixedConjugateLocalAction_norm
    {d B m : ℕ}
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
       (Σ _ : Fin B × Fin d, Fin m))) :
    ‖unconditionalMixedConjugateSigmaLocalAction B U V z‖ = ‖z‖ := by
  simpa [unconditionalMixedConjugateSigmaLocalAction] using
    dSVUniformDensityMixedProtocolLocalAction_norm
      (unconditionalMixedConjugateSigmaAtomLift (m := m) B U)
      (unconditionalMixedConjugateSigmaAtomLift (m := m) B V) z

theorem unconditionalSelectedCopyIdealStage_norm_sq
    {d N B m : ℕ} {w : ℝ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : 0 < w)
    (ξ ζ : BipartiteUnitVector d) :
    ‖unconditionalSelectedCopyIdealStage
        (N := N) (B := B) (m := m) w ξ ζ‖ ^ 2 =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ := by
  have covariance :=
    unconditionalMixedConjugateTargetCovariance
      (B := B) (n := m) width grid dimension ξ ζ
  have squared := congrArg (fun z => ‖z‖ ^ 2) covariance
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ w * (d : ℝ)),
    unconditionalSelectedCopy_mixedConjugateLocalAction_norm,
    unconditionalSelectedCopy_conjugateAcceptedTarget_norm_sq
      phases grid harmonic,
    dSVDensityRationalCanonicalAcceptedTarget_norm_sq width]
    at squared
  have dimension_real : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  have cancelled :
      (d : ℝ) *
          ‖unconditionalSelectedCopyIdealStage
            (N := N) (B := B) (m := m) w ξ ζ‖ ^ 2 =
        dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
    apply mul_left_cancel₀ (ne_of_gt width)
    simpa [unconditionalSelectedCopyIdealStage, mul_assoc] using squared
  rw [dSVDensityRationalPhysicalDiagonalBornSuccess_eq]
  apply (eq_div_iff (ne_of_gt dimension_real)).2
  simpa [mul_comm] using cancelled

theorem unconditionalSelectedCopyCleanedStage_norm_sq
    {d N B m : ℕ} {w : ℝ}
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : 0 < w)
    (ξ ζ : BipartiteUnitVector d)
    (Q : ℕ)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    ‖unconditionalSelectedCopyCleanedStage
        (N := N) (B := B) (m := m) Q w ξ ζ A C‖ ^ 2 =
      ‖dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ true true‖ ^ 2 := by
  unfold unconditionalSelectedCopyCleanedStage
    dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
  rw [dSVUniformDensityPhysicalAsyncSigmaContinuation_norm]
  unfold dSVDensityRationalPublicBucketPhysicalCoherentMixedState
  rw [unconditionalSelectedCopy_coherentPhaseSigma_norm_sq phases]
  exact
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState_norm_sq
      width grid harmonic ξ ζ

theorem unconditionalSelectedCopyCleanedMatchedBranch_norm_sq
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ]
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (Q : ℕ)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) (rest : EuclideanSpace ℂ τ)
    (rest_unit : ‖rest‖ = 1) :
    ‖unconditionalSelectedCopyCleanedMatchedBranch
        Q width schedule ξ ζ A C j rest‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ j.val := by
  unfold unconditionalSelectedCopyCleanedMatchedBranch
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopyCleanedStage_norm_sq
      phases grid harmonic (width_positive (schedule j)),
    unconditionalSelectedCopyRetainedWork_norm_sq,
    rest_unit]
  simp [dSVDensityRationalHeterogeneousPhysicalStageSuccess,
    dSVDensityRationalHeterogeneousPhysicalStageOutcome,
    j.isLt, mul_comm]

theorem unconditionalSelectedCopyIdealMatchedBranch_norm_sq
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ]
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ τ)
    (rest_unit : ‖rest‖ = 1) :
    ‖unconditionalSelectedCopyIdealMatchedBranch
        (N := N) (B := B) (m := m) width schedule ξ ζ j rest‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule j)) ξ := by
  unfold unconditionalSelectedCopyIdealMatchedBranch
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopyIdealStage_norm_sq
      phases grid dimension harmonic (width_positive (schedule j)),
    unconditionalSelectedCopyRetainedWork_norm_sq,
    rest_unit]
  ring

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def unconditionalMixedConjugateSelectedBranchUnitary
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup ((ι × ι) × τ) ℂ := by
  classical
  refine
    ⟨(((U : Matrix ι ι ℂ) ⊗ₖ
        (V : Matrix ι ι ℂ)) ⊗ₖ
        (1 : Matrix τ τ ℂ)), ?_⟩
  exact Matrix.kronecker_mem_unitary
    (Matrix.kronecker_mem_unitary U.property V.property)
    (Matrix.unitaryGroup τ ℂ).one_mem

def unconditionalMixedConjugateSelectedBranchLocalAction
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ ((ι × ι) × τ)) :
    EuclideanSpace ℂ ((ι × ι) × τ) :=
  toLp 2
    ((unconditionalMixedConjugateSelectedBranchUnitary
        (τ := τ) U V :
      Matrix ((ι × ι) × τ) ((ι × ι) × τ) ℂ).mulVec
      (ofLp z))

theorem unconditionalMixedConjugateSelectedBranch_tensorAction
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (stage : EuclideanSpace ℂ (ι × ι))
    (work : EuclideanSpace ℂ τ) :
    unconditionalMixedConjugateSelectedBranchLocalAction
        U V
        (unconditionalMatchedVerifierTensor stage work) =
      unconditionalMatchedVerifierTensor
        (toLp 2
          ((((U : Matrix ι ι ℂ) ⊗ₖ
              (V : Matrix ι ι ℂ)).mulVec
            (ofLp stage)))) work := by
  classical
  ext ⟨⟨a, b⟩, t⟩
  simp [unconditionalMixedConjugateSelectedBranchLocalAction,
    unconditionalMixedConjugateSelectedBranchUnitary,
    unconditionalMatchedVerifierTensor,
    Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Matrix.one_apply,
    Fintype.sum_prod_type, Finset.sum_mul, mul_assoc]

theorem unconditionalMixedConjugateSelectedBranch_tensor_smul
    {s τ : Type*} [Fintype s] [Fintype τ]
    (c : ℝ) (stage : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ τ) :
    c • unconditionalMatchedVerifierTensor stage work =
      unconditionalMatchedVerifierTensor
        (c • stage) work := by
  ext ⟨a, b⟩
  change (c : ℂ) * (stage a * work b) =
    ((c : ℂ) * stage a) * work b
  ring

theorem unconditionalMixedConjugateSelectedBranchCovariance
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (positive : 0 < width (schedule j))
    (rest : EuclideanSpace ℂ τ) :
    Real.sqrt (width (schedule j) * (d : ℝ)) •
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) B
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis ξ)))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) B
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis ζ)))
        (unconditionalSelectedCopyIdealMatchedBranch
          (N := N) (B := B) (m := m)
          width schedule ξ ζ j rest) =
      unconditionalMatchedVerifierTensor
        (unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
          (N := N) (B := B) (width (schedule j)) m ξ)
        (unconditionalSelectedCopyRetainedWork
          (N := N) width schedule ξ ζ j rest) := by
  classical
  unfold unconditionalSelectedCopyIdealMatchedBranch
    unconditionalSelectedCopyIdealStage
  rw [unconditionalMixedConjugateSelectedBranch_tensorAction,
    unconditionalMixedConjugateSelectedBranch_tensor_smul]
  congr 1
  exact unconditionalMixedConjugateTargetCovariance
    positive grid dimension ξ ζ

theorem unconditionalPhysicalAcceptedCoherentStage_eq_phaseSigma
    {d N B m : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin (N * m)) :
    dSVDensityRationalPublicBucketPhysicalCoherentMixedState
        (N := N) (B := B) w m ξ ζ
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      ePRState B (φ, ψ) *
        dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState
          w m ξ ζ (⟨i, a⟩, ⟨j, b⟩) := by
  simp [dSVDensityRationalPublicBucketPhysicalCoherentMixedState,
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState,
    dSVDensityRationalPublicBucketCoherentPhaseHistory,
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual,
    mul_assoc]

theorem unconditionalPhysicalAcceptedCoherentStage_apply
    {d N B m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : Fin B) (i j : Fin d)
    (k l : Fin N) (a b : Fin m) :
    dSVDensityRationalPublicBucketPhysicalCoherentMixedState
        (N := N) (B := B) w m ξ ζ
        (⟨(φ, i), finProdFinEquiv (k, a)⟩,
          ⟨(ψ, j), finProdFinEquiv (l, b)⟩) =
      ePRState B (φ, ψ) *
        dSVDensityRationalCanonicalPrefixSpectralOutcome
          w N ξ ζ (⟨k, i⟩, ⟨l, j⟩) *
        embezzlementState m (a, b) := by
  rw [unconditionalPhysicalAcceptedCoherentStage_eq_phaseSigma,
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState_apply
      width grid]
  ring

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

section DependentStoppingBlocks

variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι κ : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
variable [∀ r, Fintype (κ r)] [∀ r, DecidableEq (κ r)]

def actualStoppingBranchVector
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ s, κ s)))
    (r s : R) : EuclideanSpace ℂ (ι r × κ s) :=
  toLp 2 fun q => z (⟨r, q.1⟩, ⟨s, q.2⟩)

def actualStoppingBranchWinningEffect
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (r s : R) (x : X) (y : Y) :
    Matrix (ι r × κ s) (ι r × κ s) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (PA r x).effect a ⊗ₖ (PB s y).effect b
    else 0

omit [Fintype R] [DecidableEq R] in

theorem actualStoppingBranchWinningEffect_posSemidef
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (r s : R) (x : X) (y : Y) :
    (actualStoppingBranchWinningEffect
      G PA PB r s x y).PosSemidef := by
  classical
  apply Matrix.nonneg_iff_posSemidef.mp
  unfold actualStoppingBranchWinningEffect
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split
  · exact ((PA r x).positive a).kronecker
      ((PB s y).positive b) |>.nonneg
  · exact le_rfl

omit [Fintype R] [DecidableEq R] in

theorem actualStoppingBranchBorn_nonneg
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ s, κ s)))
    (r s : R) (x : X) (y : Y) :
    0 ≤ quadraticExpectation
      (Matrix.toEuclideanCLM (n := ι r × κ s) (𝕜 := ℂ)
        (actualStoppingBranchWinningEffect
          G PA PB r s x y))
      (actualStoppingBranchVector z r s) := by
  apply positive_quadraticExpectation_nonneg
  apply matrixEffectCLM_isPositive
  exact actualStoppingBranchWinningEffect_posSemidef
    G PA PB r s x y

def actualStoppingGlobalWinningEffect
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (x : X) (y : Y) :
    Matrix ((Σ r, ι r) × (Σ s, κ s))
      ((Σ r, ι r) × (Σ s, κ s)) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (dependentBlockPOVM
        (fun r => PA r x)).effect a ⊗ₖ
        (dependentBlockPOVM
          (fun s => PB s y)).effect b
    else 0

theorem actualStoppingGlobalWinningEffect_same
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (r s : R) (x : X) (y : Y)
    (i i' : ι r) (j j' : κ s) :
    actualStoppingGlobalWinningEffect G PA PB x y
        (⟨r, i⟩, ⟨s, j⟩) (⟨r, i'⟩, ⟨s, j'⟩) =
      actualStoppingBranchWinningEffect G PA PB r s x y
        (i, j) (i', j') := by
  classical
  unfold actualStoppingGlobalWinningEffect
    actualStoppingBranchWinningEffect
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · simp [dependentBlockPOVM_effect_same]
  · rfl

theorem actualStoppingGlobalWinningEffect_cross_eq_zero
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (r s r' s' : R) (x : X) (y : Y)
    (i : ι r) (j : κ s) (i' : ι r') (j' : κ s')
    (different : r ≠ r' ∨ s ≠ s') :
    actualStoppingGlobalWinningEffect G PA PB x y
        (⟨r, i⟩, ⟨s, j⟩) (⟨r', i'⟩, ⟨s', j'⟩) = 0 := by
  classical
  rcases different with left | right
  · unfold actualStoppingGlobalWinningEffect
    simp only [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs
    · simp [dependentBlockPOVM,
        Matrix.blockDiagonal'_apply, left]
    · rfl
  · unfold actualStoppingGlobalWinningEffect
    simp only [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs
    · simp [dependentBlockPOVM,
        Matrix.blockDiagonal'_apply, right]
    · rfl

theorem actualStoppingGlobalBorn_eq_sum
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ s, κ s)))
    (x : X) (y : Y) :
    quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := (Σ r, ι r) × (Σ s, κ s)) (𝕜 := ℂ)
          (actualStoppingGlobalWinningEffect G PA PB x y)) z =
      ∑ r : R, ∑ s : R,
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := ι r × κ s) (𝕜 := ℂ)
            (actualStoppingBranchWinningEffect
              G PA PB r s x y))
          (actualStoppingBranchVector z r s) := by
  classical
  have collapse (r s : R) (i : ι r) (j : κ s) :
      (∑ r' : R, ∑ i' : ι r', ∑ s' : R, ∑ j' : κ s',
        actualStoppingGlobalWinningEffect G PA PB x y
            (⟨r, i⟩, ⟨s, j⟩) (⟨r', i'⟩, ⟨s', j'⟩) *
          z (⟨r', i'⟩, ⟨s', j'⟩)) =
        ∑ i' : ι r, ∑ j' : κ s,
          actualStoppingBranchWinningEffect G PA PB r s x y
              (i, j) (i', j') * z (⟨r, i'⟩, ⟨s, j'⟩) := by
    rw [Finset.sum_eq_single r]
    · apply Finset.sum_congr rfl
      intro i' _
      rw [Finset.sum_eq_single s]
      · apply Finset.sum_congr rfl
        intro j' _
        rw [actualStoppingGlobalWinningEffect_same]
      · intro s' _ unequal
        apply Finset.sum_eq_zero
        intro j' _
        rw [actualStoppingGlobalWinningEffect_cross_eq_zero
          G PA PB r s r s' x y i j i' j'
            (Or.inr (Ne.symm unequal))]
        simp
      · simp
    · intro r' _ unequal
      apply Finset.sum_eq_zero
      intro i' _
      apply Finset.sum_eq_zero
      intro s' _
      apply Finset.sum_eq_zero
      intro j' _
      rw [actualStoppingGlobalWinningEffect_cross_eq_zero
        G PA PB r s r' s' x y i j i' j'
          (Or.inl (Ne.symm unequal))]
      simp
    · simp
  rw [matrixQuadraticExpectation_expand]
  simp_rw [matrixQuadraticExpectation_expand]
  simp only [Fintype.sum_prod_type, Fintype.sum_sigma,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [collapse]
  rfl

end DependentStoppingBlocks

end

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

theorem unitaryConjugatePOVM_jointEffect
    {A B d : Type} [Fintype A] [Fintype B]
    [Fintype d] [DecidableEq d]
    (U V : Matrix.unitaryGroup d ℂ)
    (P : POVM A d) (Q : POVM B d)
    (a : A) (b : B) :
    (unitaryConjugatePOVM U P).effect a ⊗ₖ
      (unitaryConjugatePOVM V Q).effect b =
      (((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ))ᴴ *
        (P.effect a ⊗ₖ Q.effect b) *
        ((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ))) := by
  change
    (((U : Matrix d d ℂ)ᴴ * P.effect a * (U : Matrix d d ℂ)) ⊗ₖ
      ((V : Matrix d d ℂ)ᴴ * Q.effect b * (V : Matrix d d ℂ))) =
      (((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ))ᴴ *
        (P.effect a ⊗ₖ Q.effect b) *
        ((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ)))
  rw [Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

section QuestionLocalStopping

variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]

def actualStoppingQuestionLocalAction
    (U V : Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ r, ι r))) :
    EuclideanSpace ℂ ((Σ r, ι r) × (Σ r, ι r)) :=
  toLp 2
    (((U : Matrix (Σ r, ι r) (Σ r, ι r) ℂ) ⊗ₖ
      (V : Matrix (Σ r, ι r) (Σ r, ι r) ℂ)).mulVec
      (ofLp z))

theorem actualStoppingQuestionLocalWinningEffect_quadratic
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (r : R) → Y → POVM B (ι r))
    (U : X → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (V : Y → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ r, ι r)))
    (normalized : ‖z‖ = 1)
    (x : X) (y : Y) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
        (pureVerifierEffect G z normalized
          (fun x => unitaryConjugatePOVM (U x)
            (dependentBlockPOVM (fun r => PA r x)))
          (fun y => unitaryConjugatePOVM (V y)
            (dependentBlockPOVM (fun r => PB r y)))
          x y)) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
          (actualStoppingGlobalWinningEffect
            G PA PB x y))
        (actualStoppingQuestionLocalAction
          (U x) (V y) z) := by
  classical
  change
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
        (∑ a : A, ∑ b : B,
          if G.predicate x y a b = true then
            (unitaryConjugatePOVM (U x)
              (dependentBlockPOVM
                (fun r => PA r x))).effect a ⊗ₖ
            (unitaryConjugatePOVM (V y)
              (dependentBlockPOVM
                (fun r => PB r y))).effect b
          else 0)) z =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
        (∑ a : A, ∑ b : B,
          if G.predicate x y a b = true then
            (dependentBlockPOVM
              (fun r => PA r x)).effect a ⊗ₖ
            (dependentBlockPOVM
              (fun r => PB r y)).effect b
          else 0))
      (actualStoppingQuestionLocalAction
        (U x) (V y) z)
  rw [sourceHistoryQuadraticExpectation_matrix_sum,
    sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [sourceHistoryQuadraticExpectation_matrix_sum,
    sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with accepted
  · rw [unitaryConjugatePOVM_jointEffect]
    exact (rectangular_matrix_quadratic_compression
      (((U x : Matrix (Σ r, ι r) (Σ r, ι r) ℂ) ⊗ₖ
        (V y : Matrix (Σ r, ι r) (Σ r, ι r) ℂ)))
      (((dependentBlockPOVM (fun r => PA r x)).effect a) ⊗ₖ
       ((dependentBlockPOVM (fun r => PB r y)).effect b))
      z).symm
  · simp [quadraticExpectation]

theorem actualStoppingQuestionLocalWinningProbability_eq_sum
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (r : R) → Y → POVM B (ι r))
    (U : X → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (V : Y → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ r, ι r)))
    (normalized : ‖z‖ = 1) :
    (pureVectorStrategy G z normalized
      (fun x => unitaryConjugatePOVM (U x)
        (dependentBlockPOVM (fun r => PA r x)))
      (fun y => unitaryConjugatePOVM (V y)
        (dependentBlockPOVM (fun r => PB r y)))).winProbability =
      ∑ x : X, ∑ y : Y, G.questionWeight x y *
        ∑ r : R, ∑ s : R,
          quadraticExpectation
            (Matrix.toEuclideanCLM (n := ι r × ι s) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G PA PB r s x y))
            (actualStoppingBranchVector
              (actualStoppingQuestionLocalAction
                (U x) (V y) z) r s) := by
  classical
  rw [pureVectorWinningProbability_eq]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  rw [actualStoppingQuestionLocalWinningEffect_quadratic]
  exact actualStoppingGlobalBorn_eq_sum
    G PA PB (actualStoppingQuestionLocalAction
      (U x) (V y) z) x y

theorem actualStoppingQuestionLocalWinningProbability_ge_matched
    {L : ℕ}
    {ι : Fin (L + 1) → Type}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (G : Game X Y A B)
    (PA : (r : Fin (L + 1)) → X → POVM A (ι r))
    (PB : (r : Fin (L + 1)) → Y → POVM B (ι r))
    (U : X → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (V : Y → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ r : Fin (L + 1), ι r) ×
       (Σ r : Fin (L + 1), ι r)))
    (normalized : ‖z‖ = 1) :
    (∑ x : X, ∑ y : Y, G.questionWeight x y *
      ∑ j : Fin L,
        quadraticExpectation
          (Matrix.toEuclideanCLM
            (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
            (actualStoppingBranchWinningEffect
              G PA PB j.succ j.succ x y))
          (actualStoppingBranchVector
            (actualStoppingQuestionLocalAction
              (U x) (V y) z) j.succ j.succ)) ≤
      (pureVectorStrategy G z normalized
        (fun x => unitaryConjugatePOVM (U x)
          (dependentBlockPOVM (fun r => PA r x)))
        (fun y => unitaryConjugatePOVM (V y)
          (dependentBlockPOVM (fun r => PB r y)))).winProbability := by
  classical
  rw [actualStoppingQuestionLocalWinningProbability_eq_sum]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  apply mul_le_mul_of_nonneg_left _ (G.weight_nonneg x y)
  let stopped := actualStoppingQuestionLocalAction
    (U x) (V y) z
  calc
    (∑ j : Fin L,
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
          (actualStoppingBranchWinningEffect
            G PA PB j.succ j.succ x y))
        (actualStoppingBranchVector stopped
          j.succ j.succ)) ≤
        ∑ r : Fin (L + 1),
          quadraticExpectation
            (Matrix.toEuclideanCLM (n := ι r × ι r) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G PA PB r r x y))
            (actualStoppingBranchVector stopped r r) := by
          rw [Fin.sum_univ_succ]
          have nonnegative := actualStoppingBranchBorn_nonneg
            G PA PB stopped (0 : Fin (L + 1)) 0 x y
          linarith
    _ ≤ ∑ r : Fin (L + 1), ∑ s : Fin (L + 1),
          quadraticExpectation
            (Matrix.toEuclideanCLM (n := ι r × ι s) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G PA PB r s x y))
            (actualStoppingBranchVector stopped r s) := by
          apply Finset.sum_le_sum
          intro r _
          exact Finset.single_le_sum
            (fun s _ => actualStoppingBranchBorn_nonneg
              G PA PB stopped r s x y)
            (Finset.mem_univ r)

theorem actualStoppingQuestionLocalFlaggedWinningProbability_ge_matched
    {L : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    {ι : Fin (L + 1) → Type}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (G : Game X Y A B)
    (weight : J → ℝ)
    (weight_nonnegative : ∀ j, 0 ≤ weight j)
    (weight_normalized : (∑ j : J, weight j) = 1)
    (PA : J → (r : Fin (L + 1)) → X → POVM A (ι r))
    (PB : J → (r : Fin (L + 1)) → Y → POVM B (ι r))
    (U : J → X → Matrix.unitaryGroup
      (Σ r : Fin (L + 1), ι r) ℂ)
    (V : J → Y → Matrix.unitaryGroup
      (Σ r : Fin (L + 1), ι r) ℂ)
    (z : J → EuclideanSpace ℂ
      ((Σ r : Fin (L + 1), ι r) ×
       (Σ r : Fin (L + 1), ι r)))
    (normalized : ∀ j, ‖z j‖ = 1) :
    (∑ q : J, weight q *
      (∑ x : X, ∑ y : Y, G.questionWeight x y *
        ∑ j : Fin L,
          quadraticExpectation
            (Matrix.toEuclideanCLM
              (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G (PA q) (PB q) j.succ j.succ x y))
            (actualStoppingBranchVector
              (actualStoppingQuestionLocalAction
                (U q x) (V q y) (z q)) j.succ j.succ))) ≤
      (pureFlaggedStrategy G weight weight_nonnegative
        weight_normalized z normalized
        (fun q x => unitaryConjugatePOVM (U q x)
          (dependentBlockPOVM (fun r => PA q r x)))
        (fun q y => unitaryConjugatePOVM (V q y)
          (dependentBlockPOVM (fun r => PB q r y)))).winProbability := by
  classical
  rw [pureFlaggedStrategy_winProbability]
  apply Finset.sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (weight_nonnegative q)
  exact actualStoppingQuestionLocalWinningProbability_ge_matched
    G (PA q) (PB q) (U q) (V q) (z q) (normalized q)

end QuestionLocalStopping

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

abbrev DSVDensityRationalPublicLogPhaseHistoryFamily
    (B N d L : ℕ) :=
  BipartiteUnitVector d →
    Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ

def dSVDensityRationalPublicLogPhaseStoppedState
    (B N d L m : ℕ)
    (S T : DSVDensityRationalPublicLogPhaseHistoryFamily
      B N d L)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicLogPhaseResidual
          B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicLogPhaseResidual
          B N d L m)) :=
  localUnitaryAction
    (dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
      B N d L m (S ξ))
    (dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
      B N d L m (T ζ))
    (dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
      B N d L m)

def dSVDensityRationalPublicMultiscaleOriginalSigmaTargetFirstEquiv
    (S B N d L m : ℕ) :
    (Σ _ :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ×
        DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L,
      Fin m) ≃
      Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) :=
  (dSVDensityRationalPublicBucketCoherentPhaseSigmaProductEquiv
    (H := DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L)
    (Fintype.card
      (DSVDensityRationalPublicMultiscalePhase S B)) m).trans
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m)

def dSVDensityRationalHeterogeneousOriginalAliceHistoryFamily
    (S B N d L : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S) :
    DSVDensityRationalPublicLogPhaseHistoryFamily
      (Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B))
      N d L :=
  fun ξ =>
    dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
      (Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B))
      (dSVDensityRationalHeterogeneousActualAliceUnitary
        N width schedule ξ)

def dSVDensityRationalHeterogeneousOriginalBobHistoryFamily
    (S B N d L : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S) :
    DSVDensityRationalPublicLogPhaseHistoryFamily
      (Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B))
      N d L :=
  fun ζ =>
    dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
      (Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B))
      (dSVDensityRationalHeterogeneousActualBobUnitary
        N width schedule ζ)

def dSVDensityRationalHeterogeneousOriginalStoppedState
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) :=
  dSVDensityRationalPublicLogPhaseStoppedState
    (Fintype.card
      (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m
    (dSVDensityRationalHeterogeneousOriginalAliceHistoryFamily
      S B N d L width schedule)
    (dSVDensityRationalHeterogeneousOriginalBobHistoryFamily
      S B N d L width schedule)
    ξ ζ

def dSVDensityRationalHeterogeneousOriginalSameStopStateEquiv
    (S B N d L m : ℕ) :
    EuclideanSpace ℂ
      ((Σ _ :
        DSVDensityRationalPublicMultiscalePhaseIndex S B ×
          DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L,
        Fin m) ×
       (Σ _ :
        DSVDensityRationalPublicMultiscalePhaseIndex S B ×
          DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L,
        Fin m)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (Fin (d *
          dSVDensityRationalPublicMultiscalePhaseResidual
            S B N d L m) ×
         Fin (d *
          dSVDensityRationalPublicMultiscalePhaseResidual
            S B N d L m)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr
      (dSVDensityRationalPublicMultiscaleOriginalSigmaTargetFirstEquiv
        S B N d L m)
      (dSVDensityRationalPublicMultiscaleOriginalSigmaTargetFirstEquiv
        S B N d L m))

def dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) :=
  dSVDensityRationalHeterogeneousOriginalSameStopStateEquiv
      S B N d L m
    (dSVDensityRationalHeterogeneousPureStoppedSigmaState
      width schedule ξ ζ
      (fun _ _ _ => embezzlementState m))

theorem
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_apply
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource
        S B N d L m width schedule ξ ζ
        (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((φ, a), i),
         dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((ψ, b), j)) =
      ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ (a, b) *
        embezzlementState m (i, j) := by
  simp [dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource,
    dSVDensityRationalHeterogeneousOriginalSameStopStateEquiv,
    dSVDensityRationalPublicMultiscaleOriginalSigmaTargetFirstEquiv,
    dSVDensityRationalPublicBucketCoherentPhaseSigmaProductEquiv,
    LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft',
    dSVDensityRationalHeterogeneousPureStoppedSigmaState,
    dSVDensityRationalPublicMultiscaleBucketCoherentSigmaState,
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual,
    dSVDensityRationalPublicBucketCoherentPhaseHistory]

theorem
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_eq_stopped
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource
        S B N d L m width schedule ξ ζ =
      dSVDensityRationalHeterogeneousOriginalStoppedState
        S B N d L m width schedule ξ ζ := by
  classical
  ext ⟨x, y⟩
  obtain ⟨⟨⟨φ, a⟩, i⟩, rfl⟩ :=
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m).surjective x
  obtain ⟨⟨⟨ψ, b⟩, j⟩, rfl⟩ :=
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m).surjective y
  obtain ⟨φ', rfl⟩ :=
    (Fintype.equivFin
      (DSVDensityRationalPublicMultiscalePhase S B)).surjective φ
  obtain ⟨ψ', rfl⟩ :=
    (Fintype.equivFin
      (DSVDensityRationalPublicMultiscalePhase S B)).surjective ψ
  rw [dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_apply]
  change _ =
    dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource
      S B N d L m width schedule ξ ζ
      (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m
        (((Fintype.equivFin
          (DSVDensityRationalPublicMultiscalePhase S B)) φ', a), i),
       dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m
        (((Fintype.equivFin
          (DSVDensityRationalPublicMultiscalePhase S B)) ψ', b), j))
  rw [dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource_apply]
  simp [ePRState]

theorem dSVDensityRationalHeterogeneousOriginalStoppedState_apply
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex N d L)
    (i j : Fin m) :
    dSVDensityRationalHeterogeneousOriginalStoppedState
        S B N d L m width schedule ξ ζ
        (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((φ, a), i),
         dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((ψ, b), j)) =
      ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ (a, b) *
        embezzlementState m (i, j) := by
  rw [←
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_eq_stopped]
  exact
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_apply
      S B N d L m width schedule ξ ζ φ ψ a b i j

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

def directDSVRemainingCopyEquiv
    {L : ℕ} {β : Type*} (j : Fin L) :
    ((Fin j.val → β) × (Fin (L - j.val) → β)) ≃ (Fin L → β) where
  toFun z i :=
    if before : i.val < j.val then z.1 ⟨i.val, before⟩
    else z.2 ⟨i.val - j.val, by omega⟩
  invFun z :=
    (fun i => z ⟨i.val, by omega⟩,
     fun i => z ⟨j.val + i.val, by omega⟩)
  left_inv z := by
    rcases z with ⟨before, after⟩
    apply Prod.ext
    · funext i
      simp
    · funext i
      simp
  right_inv z := by
    funext i
    dsimp
    split_ifs with before
    · rfl
    · apply congrArg z
      apply Fin.ext
      change j.val + (i.val - j.val) = i.val
      omega

def directDSVSelectedCopyLocalHistoryEquiv
    {L : ℕ} {β : Type*} (j : Fin L) :
    (β × ((Fin j.val → β) × (Fin (L - j.val) → β))) ≃
      (Fin (L + 1) → β) :=
  (Equiv.prodCongr (Equiv.refl β)
    (directDSVRemainingCopyEquiv (β := β) j)).trans
    (Fin.insertNthEquiv (fun _ : Fin (L + 1) => β) j.castSucc)

@[simp] theorem directDSVSelectedCopyLocalHistoryEquiv_hit
    {L : ℕ} {β : Type*} (j : Fin L)
    (selected : β) (before : Fin j.val → β)
    (after : Fin (L - j.val) → β) :
    directDSVSelectedCopyLocalHistoryEquiv j
        (selected, (before, after)) j.castSucc = selected := by
  simp [directDSVSelectedCopyLocalHistoryEquiv]

@[simp] theorem directDSVSelectedCopyLocalHistoryEquiv_before
    {L : ℕ} {β : Type*} (j : Fin L)
    (selected : β) (before : Fin j.val → β)
    (after : Fin (L - j.val) → β) (i : Fin j.val) :
    directDSVSelectedCopyLocalHistoryEquiv j
        (selected, (before, after))
        ⟨i.val, by omega⟩ = before i := by
  let k : Fin L := ⟨i.val, by omega⟩
  have earlier : k < j := by
    change i.val < j.val
    exact i.isLt
  have selected_index :
      j.castSucc.succAbove k =
        (⟨i.val, by omega⟩ : Fin (L + 1)) := by
    rw [Fin.succAbove_castSucc_of_lt j k earlier]
    rfl
  unfold directDSVSelectedCopyLocalHistoryEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply,
    Fin.insertNthEquiv_apply]
  rw [← selected_index, Fin.insertNth_apply_succAbove]
  change
    (if h : k.val < j.val
      then before ⟨k.val, h⟩
      else after ⟨k.val - j.val, by omega⟩) = before i
  simp only [k, i.isLt, ↓reduceDIte]

@[simp] theorem directDSVSelectedCopyLocalHistoryEquiv_after
    {L : ℕ} {β : Type*} (j : Fin L)
    (selected : β) (before : Fin j.val → β)
    (after : Fin (L - j.val) → β) (i : Fin (L - j.val)) :
    directDSVSelectedCopyLocalHistoryEquiv j
        (selected, (before, after))
        ⟨j.val + 1 + i.val, by omega⟩ = after i := by
  let k : Fin L := ⟨j.val + i.val, by omega⟩
  have later : j ≤ k := by
    change j.val ≤ j.val + i.val
    omega
  have selected_index :
      j.castSucc.succAbove k =
        (⟨j.val + 1 + i.val, by omega⟩ : Fin (L + 1)) := by
    rw [Fin.succAbove_castSucc_of_le j k later]
    apply Fin.ext
    change j.val + i.val + 1 = j.val + 1 + i.val
    omega
  unfold directDSVSelectedCopyLocalHistoryEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply,
    Fin.insertNthEquiv_apply]
  rw [← selected_index, Fin.insertNth_apply_succAbove]
  change
    (if h : k.val < j.val
      then before ⟨k.val, h⟩
      else after ⟨k.val - j.val, by omega⟩) = after i
  have not_before : ¬ j.val + i.val < j.val := by omega
  simp [k, not_before]

theorem directDSVRemainingCopyProductSplit
    {M : Type*} [CommMonoid M]
    {L : ℕ} (j : Fin L) (f : Fin L → M) :
    (∏ i : Fin L, f i) =
      (∏ i : Fin j.val, f ⟨i.val, by omega⟩) *
      (∏ i : Fin (L - j.val),
        f ⟨j.val + i.val, by omega⟩) := by
  classical
  have length : j.val + (L - j.val) = L := by omega
  calc
    (∏ i : Fin L, f i) =
        ∏ i : Fin (j.val + (L - j.val)), f (i.cast length) :=
      (Fin.prod_congr' f length).symm
    _ =
        (∏ i : Fin j.val, f ⟨i.val, by omega⟩) *
        (∏ i : Fin (L - j.val),
          f ⟨j.val + i.val, by omega⟩) := by
      rw [Fin.prod_univ_add]
      congr 1

theorem directDSVActualStoppingSelectedHistory_sourceProduct
    {S N d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (selectedA selectedB : DSVUniformDensityThresholdLocalIndex N d)
    (beforeA beforeB : Fin j.val →
      DSVUniformDensityThresholdLocalIndex N d)
    (afterA afterB : Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d) :
    dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ
        (⟨j.succ,
          directDSVSelectedCopyLocalHistoryEquiv j
            (selectedA, (beforeA, afterA))⟩,
         ⟨j.succ,
          directDSVSelectedCopyLocalHistoryEquiv j
            (selectedB, (beforeB, afterB))⟩) =
      dSVDensityRationalCompleteProjectiveOutcome
          (width (schedule j)) N ξ ζ true true
          (selectedA, selectedB) *
        dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
          (N := N) width schedule ξ ζ j
          (fun i => (beforeA i, beforeB i)) *
        dSVUniformDensityIndependentSharedState
          (L - j.val) N d (afterA, afterB) := by
  classical
  let a := directDSVSelectedCopyLocalHistoryEquiv j
    (selectedA, (beforeA, afterA))
  let b := directDSVSelectedCopyLocalHistoryEquiv j
    (selectedB, (beforeB, afterB))
  rw [dSVDensityRationalHeterogeneousActualCommonStopPhysicalState_eq_outcomeProduct]
  rw [Fin.prod_univ_succAbove _ j.castSucc]
  rw [directDSVRemainingCopyProductSplit j]
  rw [dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_apply]
  rw [dSVUniformDensityIndependentSharedState_apply]
  have hitA : a j.castSucc = selectedA :=
    directDSVSelectedCopyLocalHistoryEquiv_hit j
      selectedA beforeA afterA
  have hitB : b j.castSucc = selectedB :=
    directDSVSelectedCopyLocalHistoryEquiv_hit j
      selectedB beforeB afterB
  have selected :
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j j.castSucc
          (a j.castSucc, b j.castSucc) =
        dSVDensityRationalCompleteProjectiveOutcome
          (width (schedule j)) N ξ ζ true true
          (selectedA, selectedB) := by
    rw [dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_hit,
      hitA, hitB]
  rw [selected]
  simp only [mul_assoc]
  apply congrArg (fun t : ℂ =>
    dSVDensityRationalCompleteProjectiveOutcome
      (width (schedule j)) N ξ ζ true true
      (selectedA, selectedB) * t)
  apply congrArg₂ (fun x y : ℂ => x * y)
  · apply Finset.prod_congr rfl
    intro i _
    let k : Fin L := ⟨i.val, by omega⟩
    have earlier : k < j := by
      change i.val < j.val
      exact i.isLt
    have index : j.castSucc.succAbove k =
        (⟨i.val, by omega⟩ : Fin (L + 1)) := by
      rw [Fin.succAbove_castSucc_of_lt j k earlier]
      rfl
    change
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          (j.castSucc.succAbove k)
          (a (j.castSucc.succAbove k),
           b (j.castSucc.succAbove k)) = _
    rw [index]
    change
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          (⟨i.val, by omega⟩ : Fin (L + 1))
          (a ⟨i.val, by omega⟩,
           b ⟨i.val, by omega⟩) = _
    change
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          (⟨i.val, by omega⟩ : Fin (L + 1))
          (directDSVSelectedCopyLocalHistoryEquiv j
             (selectedA, (beforeA, afterA)) ⟨i.val, by omega⟩,
           directDSVSelectedCopyLocalHistoryEquiv j
             (selectedB, (beforeB, afterB)) ⟨i.val, by omega⟩) = _
    rw [directDSVSelectedCopyLocalHistoryEquiv_before,
      directDSVSelectedCopyLocalHistoryEquiv_before]
  · apply Finset.prod_congr rfl
    intro i _
    let k : Fin L := ⟨j.val + i.val, by omega⟩
    have later : j ≤ k := by
      change j.val ≤ j.val + i.val
      omega
    have index : j.castSucc.succAbove k =
        (⟨j.val + 1 + i.val, by omega⟩ : Fin (L + 1)) := by
      rw [Fin.succAbove_castSucc_of_le j k later]
      apply Fin.ext
      change j.val + i.val + 1 = j.val + 1 + i.val
      omega
    change
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          (j.castSucc.succAbove k)
          (a (j.castSucc.succAbove k),
           b (j.castSucc.succAbove k)) = _
    rw [index]
    change
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          (⟨j.val + 1 + i.val, by omega⟩ : Fin (L + 1))
          (directDSVSelectedCopyLocalHistoryEquiv j
             (selectedA, (beforeA, afterA))
               ⟨j.val + 1 + i.val, by omega⟩,
           directDSVSelectedCopyLocalHistoryEquiv j
             (selectedB, (beforeB, afterB))
               ⟨j.val + 1 + i.val, by omega⟩) = _
    rw [directDSVSelectedCopyLocalHistoryEquiv_after,
      directDSVSelectedCopyLocalHistoryEquiv_after]
    have is_after :
        j.val <
          (⟨j.val + 1 + i.val, by omega⟩ : Fin (L + 1)).val := by
      change j.val < j.val + 1 + i.val
      omega
    rw [dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_after
      width schedule ξ ζ j
      (⟨j.val + 1 + i.val, by omega⟩ : Fin (L + 1)) is_after]

abbrev UnconditionalSourcePhysicalStoppingPhaseFiber
    (S B N d L m : ℕ) :=
  Σ _ : DSVDensityRationalPublicMultiscalePhaseIndex S B ×
    DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d, Fin m

def unconditionalSourcePhysicalStoppingPhaseHarmonicIndexEquiv
    (S B N d L m : ℕ) :
    ((DSVDensityRationalPublicMultiscalePhaseIndex S B ×
        DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) ×
      Fin m) ≃
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber S B N d L m)
    where
  toFun q := ⟨q.1.2.1, ⟨(q.1.1, q.1.2.2), q.2⟩⟩
  invFun q := ((q.2.1.1, ⟨q.1, q.2.1.2⟩), q.2.2)
  left_inv := by
    intro q
    rcases q with ⟨⟨phase, ⟨flag, history⟩⟩, work⟩
    rfl
  right_inv := by
    intro q
    rcases q with ⟨flag, ⟨⟨phase, history⟩, work⟩⟩
    rfl

def unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
    (S B N d L m : ℕ) :
    Fin (d *
      dSVDensityRationalPublicMultiscalePhaseResidual
        S B N d L m) ≃
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber S B N d L m) :=
  (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m).symm.trans
    (unconditionalSourcePhysicalStoppingPhaseHarmonicIndexEquiv
      S B N d L m)

def unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
    (S B N d L m : ℕ) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ
      ((Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m) ×
       (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr
      (unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
        S B N d L m)
      (unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
        S B N d L m))

theorem unconditionalSourcePhysicalStoppingTargetFirst_branch_apply
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (r s : Fin (L + 1))
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d)
    (i k : Fin m) :
    actualStoppingBranchVector
      (unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m
        (dSVDensityRationalHeterogeneousOriginalStoppedState
          S B N d L m width schedule ξ ζ)) r s
      (⟨(φ, a), i⟩, ⟨(ψ, b), k⟩) =
        ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ
          (⟨r, a⟩, ⟨s, b⟩) *
        embezzlementState m (i, k) := by
  change
    dSVDensityRationalHeterogeneousOriginalStoppedState
      S B N d L m width schedule ξ ζ
      (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m ((φ, ⟨r, a⟩), i),
       dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m ((ψ, ⟨s, b⟩), k)) = _
  exact dSVDensityRationalHeterogeneousOriginalStoppedState_apply
    S B N d L m width schedule ξ ζ φ ψ ⟨r, a⟩ ⟨s, b⟩ i k

theorem unconditionalSourcePhysicalStoppingBranch_sigmaContinuation
    {R κ : Type} [Fintype R] [DecidableEq R]
    [Fintype κ] [DecidableEq κ]
    (U V : R → Matrix.unitaryGroup κ ℂ)
    (z : EuclideanSpace ℂ ((Σ _ : R, κ) × (Σ _ : R, κ)))
    (r s : R) :
    actualStoppingBranchVector
      (dSVUniformDensityPhysicalAsyncSigmaContinuation U V z)
      r s =
      toLp 2
        ((((U r : Matrix κ κ ℂ) ⊗ₖ (V s : Matrix κ κ ℂ)).mulVec
          (ofLp (actualStoppingBranchVector z r s)))) := by
  classical
  ext ⟨i, j⟩
  simp [actualStoppingBranchVector,
    dSVUniformDensityPhysicalAsyncSigmaContinuation,
    coherentSharedRandomControlledUnitary,
    Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Matrix.blockDiagonal'_apply,
    Fintype.sum_prod_type, Fintype.sum_sigma]

def unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup κ ℂ := by
  classical
  let M : Matrix ι ι ℂ := U.val
  refine ⟨Matrix.reindex e e M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have compatible :
      star (Matrix.reindex e e M) = Matrix.reindex e e (star M) := by
    ext i j
    simp [Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
      Matrix.conjTranspose_apply]
  rw [compatible]
  change
    (Matrix.reindexRingEquiv ℂ e) (star M) *
      (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp U.property]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

def unconditionalSelectedMultiscalePhaseIndexEquiv
    {S B : ℕ} (scale : Fin (S + 1)) :
    (Fin B × Fin (Fintype.card (Fin S → Fin B))) ≃
      DSVDensityRationalPublicMultiscalePhaseIndex (S + 1) B :=
  ((Equiv.prodCongr (Equiv.refl (Fin B))
      (Fintype.equivFin (Fin S → Fin B)).symm).trans
    (Fin.insertNthEquiv
      (fun _ : Fin (S + 1) => Fin B) scale)).trans
      (Fintype.equivFin (Fin (S + 1) → Fin B))

theorem unconditionalSelectedMultiscalePhase_card
    (S B : ℕ) :
    Fintype.card
        (DSVDensityRationalPublicMultiscalePhase (S + 1) B) =
      B * Fintype.card (Fin S → Fin B) := by
  simp [DSVDensityRationalPublicMultiscalePhase,
    pow_succ, Nat.mul_comm]

theorem unconditionalSelectedMultiscalePhase_EPR_apply
    {S B : ℕ} (scale : Fin (S + 1))
    (p q : Fin B)
    (r t : Fin (Fintype.card (Fin S → Fin B))) :
    ePRState
        (Fintype.card
          (DSVDensityRationalPublicMultiscalePhase (S + 1) B))
        (unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (p, r),
         unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (q, t)) =
      ePRState B (p, q) *
        ePRState (Fintype.card (Fin S → Fin B)) (r, t) := by
  classical
  by_cases selected : p = q
  · subst q
    by_cases residual : r = t
    · subst t
      simp only [ePRState, ↓reduceIte]
      rw [unconditionalSelectedMultiscalePhase_card,
        Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg B), mul_inv]
      exact Complex.ofReal_mul _ _
    · have different :
          unconditionalSelectedMultiscalePhaseIndexEquiv
              scale (p, r) ≠
            unconditionalSelectedMultiscalePhaseIndexEquiv
              scale (p, t) := by
          intro equal
          exact residual
            (congrArg Prod.snd
              ((unconditionalSelectedMultiscalePhaseIndexEquiv
                scale).injective equal))
      simp [ePRState, different, residual]
  · have different :
        unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (p, r) ≠
          unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (q, t) := by
        intro equal
        exact selected
          (congrArg Prod.fst
            ((unconditionalSelectedMultiscalePhaseIndexEquiv
              scale).injective equal))
    simp [ePRState, different, selected]

def unconditionalActualMultiscalePhaseIndexEquiv
    {S B : ℕ} (scale : Fin S) :
    (Fin B × Fin (Fintype.card (Fin (S - 1) → Fin B))) ≃
      DSVDensityRationalPublicMultiscalePhaseIndex S B := by
  cases S with
  | zero => exact Fin.elim0 scale
  | succ S =>
      exact unconditionalSelectedMultiscalePhaseIndexEquiv
        (S := S) scale

theorem unconditionalActualMultiscalePhase_EPR_apply
    {S B : ℕ} (scale : Fin S)
    (p q : Fin B)
    (r t : Fin (Fintype.card (Fin (S - 1) → Fin B))) :
    ePRState
        (Fintype.card
          (DSVDensityRationalPublicMultiscalePhase S B))
        (unconditionalActualMultiscalePhaseIndexEquiv
            scale (p, r),
         unconditionalActualMultiscalePhaseIndexEquiv
            scale (q, t)) =
      ePRState B (p, q) *
        ePRState (Fintype.card (Fin (S - 1) → Fin B))
          (r, t) := by
  cases S with
  | zero => exact Fin.elim0 scale
  | succ S =>
      exact unconditionalSelectedMultiscalePhase_EPR_apply
        scale p q r t

def unconditionalSourcePhysicalCleanedReindexedUnitary
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ)
    (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup κ ℂ := by
  classical
  let M : Matrix ι ι ℂ := U.val
  refine ⟨Matrix.reindex e e M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have compatible :
      star (Matrix.reindex e e M) =
        Matrix.reindex e e (star M) := by
    ext i j
    simp [Matrix.star_eq_conjTranspose,
      Matrix.reindex_apply, Matrix.conjTranspose_apply]
  rw [compatible]
  change
    (Matrix.reindexRingEquiv ℂ e) (star M) *
      (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp U.property]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

def unconditionalSourcePhysicalCleanedTargetFirstUnitary
    (S B N d L m : ℕ)
    (U : Matrix.unitaryGroup
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) ℂ) :
    Matrix.unitaryGroup
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m) ℂ :=
  unconditionalSourcePhysicalCleanedReindexedUnitary
    (unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
      S B N d L m) U

def unconditionalSourcePhysicalCleanedStoppingFixedSource
    (S B N d L m : ℕ) :
    EuclideanSpace ℂ
      ((Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m) ×
       (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m)) :=
  unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
    S B N d L m
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
      S B N d L m)

theorem unconditionalSourcePhysicalCleanedStoppingFixedSource_norm
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m) :
    ‖unconditionalSourcePhysicalCleanedStoppingFixedSource
      S B N d L m‖ = 1 := by
  unfold unconditionalSourcePhysicalCleanedStoppingFixedSource
  rw [LinearIsometryEquiv.norm_map]
  exact
    dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource_norm
      phases grid dimension harmonic

theorem
    unconditionalSourcePhysicalCleanedStoppingLocalAction_reindex
    {S B N d L m : ℕ}
    (U V : Matrix.unitaryGroup
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) ℂ)
    (z : EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m))) :
    actualStoppingQuestionLocalAction
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m U)
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m V)
      (unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m z) =
      unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m (localUnitaryAction U V z) := by
  classical
  let e := unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
    S B N d L m
  ext ⟨a, b⟩
  change
    (∑ q :
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m) ×
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m),
      (U : Matrix _ _ ℂ) (e.symm a) (e.symm q.1) *
        (V : Matrix _ _ ℂ) (e.symm b) (e.symm q.2) *
        z (e.symm q.1, e.symm q.2)) =
      ∑ q :
        Fin (d *
          dSVDensityRationalPublicMultiscalePhaseResidual
            S B N d L m) ×
        Fin (d *
          dSVDensityRationalPublicMultiscalePhaseResidual
            S B N d L m),
        (U : Matrix _ _ ℂ) (e.symm a) q.1 *
          (V : Matrix _ _ ℂ) (e.symm b) q.2 * z q
  simpa using
    (Equiv.sum_comp (Equiv.prodCongr e e)
      (fun q :
        (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m) ×
        (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m) =>
        (U : Matrix _ _ ℂ) (e.symm a) (e.symm q.1) *
          (V : Matrix _ _ ℂ) (e.symm b) (e.symm q.2) *
          z (e.symm q.1, e.symm q.2))).symm

theorem
    unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    actualStoppingQuestionLocalAction
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
          S B N d L m width schedule ξ))
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
          S B N d L m width schedule ζ))
      (unconditionalSourcePhysicalCleanedStoppingFixedSource
        S B N d L m) =
      unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m
        (dSVDensityRationalHeterogeneousOriginalStoppedState
          S B N d L m width schedule ξ ζ) := by
  unfold unconditionalSourcePhysicalCleanedStoppingFixedSource
  rw [unconditionalSourcePhysicalCleanedStoppingLocalAction_reindex]
  rfl

theorem
    unconditionalSourcePhysicalCleanedStoppingFixedSource_branch_apply
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (r s : Fin (L + 1))
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d)
    (i k : Fin m) :
    actualStoppingBranchVector
      (actualStoppingQuestionLocalAction
        (unconditionalSourcePhysicalCleanedTargetFirstUnitary
          S B N d L m
          (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
            S B N d L m width schedule ξ))
        (unconditionalSourcePhysicalCleanedTargetFirstUnitary
          S B N d L m
          (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
            S B N d L m width schedule ζ))
        (unconditionalSourcePhysicalCleanedStoppingFixedSource
          S B N d L m)) r s
      (⟨(φ, a), i⟩, ⟨(ψ, b), k⟩) =
        ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ (⟨r, a⟩, ⟨s, b⟩) *
        embezzlementState m (i, k) := by
  rw [unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction]
  exact
    unconditionalSourcePhysicalStoppingTargetFirst_branch_apply
      width schedule ξ ζ r s φ ψ a b i k

def unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
    {L : ℕ} (j : Fin L) (β : Type*) :
    (Fin (L + 1) → β) ≃
      β × ((Fin j.val → β) × (Fin (L - j.val) → β)) where
  toFun f :=
    (f j.castSucc,
      (fun i => f ⟨i.val, by omega⟩,
       fun i => f ⟨j.val + 1 + i.val, by omega⟩))
  invFun q i :=
    if before : i.val < j.val then
      q.2.1 ⟨i.val, before⟩
    else if hit : i.val = j.val then q.1
    else q.2.2 ⟨i.val - (j.val + 1), by omega⟩
  left_inv := by
    intro f
    funext i
    dsimp
    split <;> rename_i before
    · apply congrArg f
      apply Fin.ext
      rfl
    · split <;> rename_i hit
      · apply congrArg f
        apply Fin.ext
        exact hit.symm
      · apply congrArg f
        apply Fin.ext
        simp only
        omega
  right_inv := by
    intro q
    rcases q with ⟨selected, before, later⟩
    apply Prod.ext
    · simp
    · apply Prod.ext
      · funext i
        simp
      · funext i
        have not_before : ¬ j.val + 1 + i.val < j.val := by omega
        have not_hit : ¬ j.val + 1 + i.val = j.val := by omega
        simp [not_before, not_hit]

@[simp] theorem unconditionalSourcePhysicalCleanedSelectedHistoryEquiv_hit
    {L : ℕ} (j : Fin L) (β : Type*) (f : Fin (L + 1) → β) :
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
      j β f).1 = f j.castSucc := by
  rfl

def unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
    {P R : Type*} {B N d L m : ℕ}
    (phaseSplit : P ≃ Fin B × R) (j : Fin L) :
    (Σ _ : P × (Fin (L + 1) →
        DSVUniformDensityThresholdLocalIndex N d), Fin m) ≃
      UnconditionalSelectedCopyLocalIndex B d N m ×
        ((Fin j.val →
          DSVUniformDensityThresholdLocalIndex N d) ×
         ((Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d) × R)) where
  toFun q :=
    let phase := phaseSplit q.1.1
    let history :=
      unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
        (DSVUniformDensityThresholdLocalIndex N d) q.1.2
    (⟨(phase.1, history.1.2),
       finProdFinEquiv (history.1.1, q.2)⟩,
      (history.2.1, (history.2.2, phase.2)))
  invFun q :=
    let work := finProdFinEquiv.symm q.1.2
    ⟨(phaseSplit.symm (q.1.1.1, q.2.2.2),
      (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
        (DSVUniformDensityThresholdLocalIndex N d)).symm
        (⟨work.1, q.1.1.2⟩, (q.2.1, q.2.2.1))),
      work.2⟩
  left_inv := by
    rintro ⟨⟨phase, history⟩, work⟩
    simp only [Equiv.symm_apply_apply]
    change
      (⟨(phaseSplit.symm
          ((phaseSplit phase).1, (phaseSplit phase).2),
        (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
          (DSVUniformDensityThresholdLocalIndex N d)).symm
          ((unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
            (DSVUniformDensityThresholdLocalIndex N d) history).1,
           ((unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
             (DSVUniformDensityThresholdLocalIndex N d) history).2.1,
            (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
              (DSVUniformDensityThresholdLocalIndex N d) history).2.2))),
        work⟩ :
        Σ _ : P × (Fin (L + 1) →
          DSVUniformDensityThresholdLocalIndex N d), Fin m) =
          ⟨(phase, history), work⟩
    simp
    exact
      (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
        (DSVUniformDensityThresholdLocalIndex N d)).symm_apply_apply
          history
  right_inv := by
    rintro ⟨⟨⟨phase, spectral⟩, packed⟩,
      ⟨before, ⟨later, remainder⟩⟩⟩
    simp
    exact finProdFinEquiv.apply_symm_apply packed

def unconditionalSourcePhysicalCleanedFullBilateralRegroup
    {R : Type*} {B N d L m : ℕ} (j : Fin L) :
    ((UnconditionalSelectedCopyLocalIndex B d N m ×
       ((Fin j.val → DSVUniformDensityThresholdLocalIndex N d) ×
        ((Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d) × R))) ×
     (UnconditionalSelectedCopyLocalIndex B d N m ×
       ((Fin j.val → DSVUniformDensityThresholdLocalIndex N d) ×
        ((Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d) × R)))) ≃
    ((UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) ×
      ((Fin j.val →
        (DSVUniformDensityThresholdLocalIndex N d ×
         DSVUniformDensityThresholdLocalIndex N d)) ×
       (((Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d) ×
         (Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d)) ×
        (R × R)))) where
  toFun q :=
    ((q.1.1, q.2.1),
      ((fun i => (q.1.2.1 i, q.2.2.1 i)),
       ((q.1.2.2.1, q.2.2.2.1),
        (q.1.2.2.2, q.2.2.2.2))))
  invFun q :=
    ((q.1.1,
       ((fun i => (q.2.1 i).1),
        (q.2.2.1.1, q.2.2.2.1))),
     (q.1.2,
       ((fun i => (q.2.1 i).2),
        (q.2.2.1.2, q.2.2.2.2))))
  left_inv := by
    rintro ⟨⟨selectedA, beforeA, laterA, phaseA⟩,
      ⟨selectedB, beforeB, laterB, phaseB⟩⟩
    simp
  right_inv := by
    rintro ⟨⟨selectedA, selectedB⟩,
      ⟨before, ⟨⟨laterA, laterB⟩, ⟨phaseA, phaseB⟩⟩⟩⟩
    simp

def unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
    {P R : Type*} [Fintype P] [Fintype R]
    {B N d L m : ℕ}
    (phaseSplit : P ≃ Fin B × R) (j : Fin L) :
    EuclideanSpace ℂ
      ((Σ _ : P × (Fin (L + 1) →
          DSVUniformDensityThresholdLocalIndex N d), Fin m) ×
       (Σ _ : P × (Fin (L + 1) →
          DSVUniformDensityThresholdLocalIndex N d), Fin m)) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex B d N m ×
        UnconditionalSelectedCopyLocalIndex B d N m) ×
       ((Fin j.val →
         (DSVUniformDensityThresholdLocalIndex N d ×
          DSVUniformDensityThresholdLocalIndex N d)) ×
        (((Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d) ×
          (Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d)) ×
         (R × R)))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.prodCongr
      (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
        phaseSplit j)
      (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
        phaseSplit j)).trans
      (unconditionalSourcePhysicalCleanedFullBilateralRegroup
        (R := R) (B := B) (N := N) (d := d) (m := m) j))

def unconditionalSourcePhysicalCleanedSelectedStageUnitary
    {B N d m : ℕ}
    (Q : ℕ) (w : ℝ) (ξ : BipartiteUnitVector d)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  dSVDensityRationalPublicBucketCoherentPhaseLocalUnitary
    (dSVDensityRationalPhysicalAcceptedRank w N ξ)
    (dSVDensityRationalPublicLogRankBucket Q)
    A

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

abbrev UnconditionalActualCleanedSelectedRetainedIndex
    {N d L : ℕ} (j : Fin L) (R : Type) :=
  (Fin j.val → DSVUniformDensityThresholdLocalIndex N d) ×
    ((Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d) × R)

def unconditionalActualCleanedSelectedTensorUnitary
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) :
    Matrix.unitaryGroup (ι × κ) ℂ :=
  ⟨(U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ),
    Matrix.kronecker_mem_unitary U.property V.property⟩

def unconditionalActualCleanedSelectedStageBucketUnitary
    {B N d m : ℕ} (Q : ℕ) (w : ℝ)
    (ξ : BipartiteUnitVector d)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  unconditionalSourcePhysicalCleanedSelectedStageUnitary Q w ξ A

def unconditionalActualCleanedSelectedStagePhysicalIndexEquiv
    (B N d m : ℕ) :
    (Σ _ : Fin B,
      DSVUniformDensityThresholdLocalIndex N d × Fin m) ≃
      UnconditionalSelectedCopyLocalIndex B d N m where
  toFun q :=
    ⟨(q.1, q.2.1.2), finProdFinEquiv (q.2.1.1, q.2.2)⟩
  invFun q :=
    let work := finProdFinEquiv.symm q.2
    ⟨q.1.1, (⟨work.1, q.1.2⟩, work.2)⟩
  left_inv := by
    rintro ⟨phase, ⟨⟨threshold, spectral⟩, harmonic⟩⟩
    simp
  right_inv := by
    rintro ⟨⟨phase, spectral⟩, work⟩
    simp
    exact finProdFinEquiv.apply_symm_apply work

def unconditionalActualCleanedSelectedStageSpectralUnitary
    {B N d m : ℕ}
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
    (unconditionalActualCleanedSelectedStagePhysicalIndexEquiv
      B N d m)
    (coherentSharedRandomControlledUnitary
      (fun _ : Fin B =>
        unconditionalActualCleanedSelectedTensorUnitary
          spectral (1 : Matrix.unitaryGroup (Fin m) ℂ)))

def unconditionalActualCleanedSelectedFullStageUnitary
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    Matrix.unitaryGroup
      (UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m) ℂ := by
  let retained :=
    UnconditionalActualCleanedSelectedRetainedIndex
      (N := N) (d := d) j R
  let selected := UnconditionalSelectedCopyLocalIndex B d N m
  let regroup :
      UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m ≃ (Σ _ : retained, selected) :=
    (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      phaseSplit j).trans
      ((Equiv.prodComm selected retained).trans
        (Equiv.sigmaEquivProd retained selected).symm)
  exact
    unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      regroup.symm
      (coherentSharedRandomControlledUnitary
        (fun _ : retained =>
          unconditionalActualCleanedSelectedStageBucketUnitary
            Q (width (schedule j)) ξ A *
          unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m) spectral))

def unconditionalActualCleanedSelectedFiniteStageDecoder
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Fin (L + 1) → Matrix.unitaryGroup
      (UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m) ℂ :=
  Fin.cases 1 (fun j =>
    unconditionalActualCleanedSelectedFullStageUnitary
      phaseSplit Q width schedule ξ spectral A j)

@[simp] theorem
    unconditionalActualCleanedSelectedFiniteStageDecoder_succ
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    unconditionalActualCleanedSelectedFiniteStageDecoder
        phaseSplit Q width schedule ξ spectral A j.succ =
      unconditionalActualCleanedSelectedFullStageUnitary
        phaseSplit Q width schedule ξ spectral A j := by
  simp [unconditionalActualCleanedSelectedFiniteStageDecoder]

theorem unconditionalActualCleanedSelectedMatchedStoppingBranch
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    actualStoppingBranchVector
      (dSVUniformDensityPhysicalAsyncSigmaContinuation
        (unconditionalActualCleanedSelectedFiniteStageDecoder
          phaseSplit Q width schedule ξ
          (dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ) A)
        (unconditionalActualCleanedSelectedFiniteStageDecoder
          phaseSplit Q width schedule ζ
          ((dSVUniformDensityBobHistoryCopyBasis (N := N) ζ)⁻¹) C)
        (actualStoppingQuestionLocalAction
          (unconditionalSourcePhysicalCleanedTargetFirstUnitary
            S B N d L m
            (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
              S B N d L m width schedule ξ))
          (unconditionalSourcePhysicalCleanedTargetFirstUnitary
            S B N d L m
            (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
              S B N d L m width schedule ζ))
          (unconditionalSourcePhysicalCleanedStoppingFixedSource
            S B N d L m))) j.succ j.succ =
      toLp 2
        ((((unconditionalActualCleanedSelectedFullStageUnitary
              phaseSplit Q width schedule ξ
              (dSVUniformDensityAliceHistorySpectralCopy
                (N := N) ξ) A j :
            Matrix (UnconditionalSourcePhysicalStoppingPhaseFiber
              S B N d L m)
              (UnconditionalSourcePhysicalStoppingPhaseFiber
                S B N d L m) ℂ) ⊗ₖ
          (unconditionalActualCleanedSelectedFullStageUnitary
              phaseSplit Q width schedule ζ
              ((dSVUniformDensityBobHistoryCopyBasis
                (N := N) ζ)⁻¹) C j :
            Matrix (UnconditionalSourcePhysicalStoppingPhaseFiber
              S B N d L m)
              (UnconditionalSourcePhysicalStoppingPhaseFiber
                S B N d L m) ℂ)).mulVec
            (ofLp
              (actualStoppingBranchVector
                (unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
                  S B N d L m
                  (dSVDensityRationalHeterogeneousOriginalStoppedState
                    S B N d L m width schedule ξ ζ))
                j.succ j.succ)))) := by
  rw [unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction,
    unconditionalSourcePhysicalStoppingBranch_sigmaContinuation,
    unconditionalActualCleanedSelectedFiniteStageDecoder_succ,
    unconditionalActualCleanedSelectedFiniteStageDecoder_succ]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

abbrev UnconditionalSourceFlagControlledRetainedIndex
    {N d L : ℕ} (j : Fin L) (R : Type) :=
  (Fin j.val → DSVUniformDensityThresholdLocalIndex N d) ×
    ((Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d) × R)

def unconditionalSourceFlagControlledTensorUnitary
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) :
    Matrix.unitaryGroup (ι × κ) ℂ :=
  ⟨(U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ),
    Matrix.kronecker_mem_unitary U.property V.property⟩

def unconditionalSourceFlagControlledStagePhysicalIndexEquiv
    (B N d m : ℕ) :
    (Σ _ : Fin B,
      DSVUniformDensityThresholdLocalIndex N d × Fin m) ≃
      UnconditionalSelectedCopyLocalIndex B d N m where
  toFun q :=
    ⟨(q.1, q.2.1.2), finProdFinEquiv (q.2.1.1, q.2.2)⟩
  invFun q :=
    let work := finProdFinEquiv.symm q.2
    ⟨q.1.1, (⟨work.1, q.1.2⟩, work.2)⟩
  left_inv := by
    rintro ⟨phase, ⟨⟨threshold, spectral⟩, harmonic⟩⟩
    simp
  right_inv := by
    rintro ⟨⟨phase, spectral⟩, work⟩
    simp
    exact finProdFinEquiv.apply_symm_apply work

def unconditionalSourceFlagControlledStageSpectralUnitary
    {B N d m : ℕ}
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
    (unconditionalSourceFlagControlledStagePhysicalIndexEquiv
      B N d m)
    (coherentSharedRandomControlledUnitary
      (fun _ : Fin B =>
        unconditionalSourceFlagControlledTensorUnitary
          spectral (1 : Matrix.unitaryGroup (Fin m) ℂ)))

def unconditionalSourceFlagControlledStageBucketUnitary
    {B N d m : ℕ} (Q : ℕ) (w : ℝ)
    (ξ : BipartiteUnitVector d)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun q : Fin B × Fin d =>
      A q.1 (dSVDensityRationalPublicLogRankBucket Q q.1
        (dSVDensityRationalPhysicalAcceptedRank w N ξ q.2)))

def unconditionalSourceFlagControlledFullStageUnitary
    {S B N d L m : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    Matrix.unitaryGroup
      (UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m) ℂ := by
  let retained :=
    UnconditionalSourceFlagControlledRetainedIndex
      (N := N) (d := d) j R
  let selected := UnconditionalSelectedCopyLocalIndex B d N m
  let regroup :
      UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m ≃ (Σ _ : retained, selected) :=
    (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      phaseSplit j).trans
      ((Equiv.prodComm selected retained).trans
        (Equiv.sigmaEquivProd retained selected).symm)
  exact
    unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      regroup.symm
      (coherentSharedRandomControlledUnitary
        (fun _ : retained =>
          unconditionalSourceFlagControlledStageBucketUnitary
            Q (width (schedule j)) ξ A *
          unconditionalSourceFlagControlledStageSpectralUnitary
            (B := B) (m := m) spectral))

def unconditionalSourceFlagControlledFiniteStageDecoder
    {S B N d L m : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Fin (L + 1) → Matrix.unitaryGroup
      (UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m) ℂ :=
  Fin.cases 1 (fun j =>
    unconditionalSourceFlagControlledFullStageUnitary
      phaseSplit Q width schedule ξ spectral A j)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def unconditionalActualPhysicalMixedAcceptedRawStage
    {B N d m : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) :=
  toLp 2 fun q =>
    ePRState B (q.1.1.1, q.2.1.1) *
      dSVDensityRationalPhysicalAcceptedOutcome w N ξ ζ
        (⟨(finProdFinEquiv.symm q.1.2).1, q.1.1.2⟩,
         ⟨(finProdFinEquiv.symm q.2.2).1, q.2.1.2⟩) *
      embezzlementState m
        ((finProdFinEquiv.symm q.1.2).2,
         (finProdFinEquiv.symm q.2.2).2)

theorem unconditionalActualPhysicalMixedAcceptedSpectralGauge_apply
    {B N d m : ℕ}
    (U : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (φ ψ : Fin B) (i j : Fin d)
    (k l : Fin N) (a b : Fin m) :
    (unconditionalActualCleanedSelectedStageSpectralUnitary
        (B := B) (m := m) U :
        Matrix (UnconditionalSelectedCopyLocalIndex B d N m)
          (UnconditionalSelectedCopyLocalIndex B d N m) ℂ)
      ⟨(φ, i), finProdFinEquiv (k, a)⟩
      ⟨(ψ, j), finProdFinEquiv (l, b)⟩ =
        if φ = ψ then
          (U : Matrix
              (DSVUniformDensityThresholdLocalIndex N d)
              (DSVUniformDensityThresholdLocalIndex N d) ℂ)
            ⟨k, i⟩ ⟨l, j⟩ *
            (if a = b then (1 : ℂ) else 0)
        else 0 := by
  classical
  have threshold_a : (finProdFinEquiv (k, a)).divNat = k := by
    change (finProdFinEquiv.symm (finProdFinEquiv (k, a))).1 = k
    rw [Equiv.symm_apply_apply]
  have harmonic_a : (finProdFinEquiv (k, a)).modNat = a := by
    change (finProdFinEquiv.symm (finProdFinEquiv (k, a))).2 = a
    rw [Equiv.symm_apply_apply]
  have threshold_b : (finProdFinEquiv (l, b)).divNat = l := by
    change (finProdFinEquiv.symm (finProdFinEquiv (l, b))).1 = l
    rw [Equiv.symm_apply_apply]
  have harmonic_b : (finProdFinEquiv (l, b)).modNat = b := by
    change (finProdFinEquiv.symm (finProdFinEquiv (l, b))).2 = b
    rw [Equiv.symm_apply_apply]
  simp [unconditionalActualCleanedSelectedStageSpectralUnitary,
    unconditionalSourceFixedPureStoppedSigmaReindexedUnitary,
    unconditionalActualCleanedSelectedStagePhysicalIndexEquiv,
    coherentSharedRandomControlledUnitary,
    unconditionalActualCleanedSelectedTensorUnitary,
    Matrix.blockDiagonal'_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, threshold_a, harmonic_a,
    threshold_b, harmonic_b]

theorem
    unconditionalActualPhysicalMixedAcceptedSpectralGauge_sum
    {N d : ℕ}
    (f : DSVUniformDensityThresholdLocalIndex N d →
      DSVUniformDensityThresholdLocalIndex N d → ℂ) :
    (∑ i : Fin d, ∑ k : Fin N,
      ∑ j : Fin d, ∑ l : Fin N,
        f ⟨k, i⟩ ⟨l, j⟩) =
      ∑ x : DSVUniformDensityThresholdLocalIndex N d,
        ∑ y : DSVUniformDensityThresholdLocalIndex N d,
          f x y := by
  classical
  simp only [Fintype.sum_sigma]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem unconditionalActualPhysicalMixedAcceptedSpectralGauge_stage
    {B N d m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d) :
    toLp 2
      ((((unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m)
            (dSVUniformDensityAliceHistorySpectralCopy
              (N := N) ξ) :
            Matrix (UnconditionalSelectedCopyLocalIndex B d N m)
              (UnconditionalSelectedCopyLocalIndex B d N m) ℂ) ⊗ₖ
          (unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m)
            ((dSVUniformDensityBobHistoryCopyBasis
              (N := N) ζ)⁻¹) :
            Matrix (UnconditionalSelectedCopyLocalIndex B d N m)
              (UnconditionalSelectedCopyLocalIndex B d N m) ℂ)).mulVec
        (ofLp (unconditionalActualPhysicalMixedAcceptedRawStage
          (B := B) (m := m) w ξ ζ)))) =
      dSVDensityRationalPublicBucketPhysicalCoherentMixedState
        (N := N) (B := B) w m ξ ζ := by
  classical
  ext ⟨⟨⟨φ, i⟩, packedA⟩, ⟨⟨ψ, j⟩, packedB⟩⟩
  obtain ⟨⟨k, a⟩, rfl⟩ := finProdFinEquiv.surjective packedA
  obtain ⟨⟨l, b⟩, rfl⟩ := finProdFinEquiv.surjective packedB
  have reindex_packed (f : Fin (N * m) → ℂ) :
      (∑ packed : Fin (N * m), f packed) =
        ∑ packed : Fin N × Fin m, f (finProdFinEquiv packed) :=
    (Equiv.sum_comp finProdFinEquiv f).symm
  rw [unconditionalPhysicalAcceptedCoherentStage_apply
    width grid ξ ζ φ ψ i j k l a b]
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Fintype.sum_sigma]
  simp_rw [reindex_packed]
  simp only [Fintype.sum_prod_type]
  simp_rw [unconditionalActualPhysicalMixedAcceptedSpectralGauge_apply]
  simp only [
    unconditionalActualPhysicalMixedAcceptedRawStage,
    Equiv.symm_apply_apply, ite_mul, mul_ite, zero_mul, mul_zero,
    mul_one]
  simp [dSVDensityRationalCanonicalPrefixSpectralOutcome, ePRState,
    Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm]
  let alice : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ
  let bob : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityBobHistoryCopyBasis (N := N) ζ
  let summand :
      DSVUniformDensityThresholdLocalIndex N d →
        DSVUniformDensityThresholdLocalIndex N d → ℂ :=
    fun x y =>
      (↑(Real.sqrt (B : ℝ)) : ℂ)⁻¹ *
        (embezzlementState m (a, b) *
          (dSVDensityRationalPhysicalAcceptedOutcome
            w N ξ ζ (x, y) *
            (alice ⟨k, i⟩ x * (starRingEnd ℂ) (bob y ⟨l, j⟩))))
  by_cases phases : φ = ψ
  · simp only [if_pos phases]
    exact unconditionalActualPhysicalMixedAcceptedSpectralGauge_sum
      summand
  · simp only [if_neg phases]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

abbrev UnconditionalActualCanonicalRetainedPhaseIndex (S B : ℕ) :=
  Fin (Fintype.card (Fin (S - 1) → Fin B))

def unconditionalActualCanonicalRetainedPhaseTail
    {S B N d L : ℕ} (j : Fin L) :
    EuclideanSpace ℂ
      (((Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d) ×
        (Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d)) ×
       (UnconditionalActualCanonicalRetainedPhaseIndex S B ×
        UnconditionalActualCanonicalRetainedPhaseIndex S B)) :=
  toLp 2 fun q =>
    dSVUniformDensityIndependentSharedState (L - j.val) N d q.1 *
      ePRState
        (Fintype.card (Fin (S - 1) → Fin B)) q.2

def unconditionalActualCanonicalFixedSourceMatchedBranch
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    EuclideanSpace ℂ
      (UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m ×
       UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m) :=
  actualStoppingBranchVector
    (actualStoppingQuestionLocalAction
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
          S B N d L m width schedule ξ))
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
          S B N d L m width schedule ζ))
      (unconditionalSourcePhysicalCleanedStoppingFixedSource
        S B N d L m)) j.succ j.succ

def unconditionalActualCanonicalRawSelectedPhysicalStage
    {B N d m : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) :=
  toLp 2 fun q =>
    ePRState B (q.1.1.1, q.2.1.1) *
      dSVDensityRationalPhysicalAcceptedOutcome w N ξ ζ
        (⟨(finProdFinEquiv.symm q.1.2).1, q.1.1.2⟩,
         ⟨(finProdFinEquiv.symm q.2.2).1, q.2.1.2⟩) *
      embezzlementState m
        ((finProdFinEquiv.symm q.1.2).2,
         (finProdFinEquiv.symm q.2.2).2)

theorem unconditionalActualCanonicalCleanedHistorySymm_eq_direct
    {L : ℕ} (j : Fin L) (β : Type*)
    (selected : β) (before : Fin j.val → β)
    (later : Fin (L - j.val) → β) :
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
      j β).symm (selected, (before, later)) =
      directDSVSelectedCopyLocalHistoryEquiv
        j (selected, (before, later)) := by
  apply (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
    j β).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact
      (directDSVSelectedCopyLocalHistoryEquiv_hit
        j selected before later).symm
  · apply Prod.ext
    · funext i
      exact
        (directDSVSelectedCopyLocalHistoryEquiv_before
          j selected before later i).symm
    · funext i
      exact
        (directDSVSelectedCopyLocalHistoryEquiv_after
          j selected before later i).symm

theorem unconditionalActualCanonicalFullSource_eq_rawSelectedStage
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualMultiscalePhaseIndexEquiv
          (schedule j)).symm j
        (unconditionalActualCanonicalFixedSourceMatchedBranch
          (B := B) (m := m) width schedule ξ ζ j) =
      unconditionalMatchedVerifierTensor
        (unconditionalActualCanonicalRawSelectedPhysicalStage
          (B := B) (m := m) (width (schedule j)) ξ ζ)
        (unconditionalSelectedCopyRetainedWork
          (N := N) width schedule ξ ζ j
          (unconditionalActualCanonicalRetainedPhaseTail
            (S := S) (B := B) j)) := by
  classical
  ext ⟨⟨⟨⟨p, i⟩, packedA⟩, ⟨⟨q, k⟩, packedB⟩⟩,
    ⟨before, ⟨⟨afterA, afterB⟩, ⟨tailA, tailB⟩⟩⟩⟩
  let a := finProdFinEquiv.symm packedA
  let b := finProdFinEquiv.symm packedB
  let historyA :=
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
      (DSVUniformDensityThresholdLocalIndex N d)).symm
      (⟨a.1, i⟩,
       ((fun t => (before t).1), afterA))
  let historyB :=
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
      (DSVUniformDensityThresholdLocalIndex N d)).symm
      (⟨b.1, k⟩,
       ((fun t => (before t).2), afterB))
  change
    unconditionalActualCanonicalFixedSourceMatchedBranch
        width schedule ξ ζ j
        (⟨(unconditionalActualMultiscalePhaseIndexEquiv
              (schedule j) (p, tailA), historyA), a.2⟩,
         ⟨(unconditionalActualMultiscalePhaseIndexEquiv
              (schedule j) (q, tailB), historyB), b.2⟩) =
      unconditionalActualCanonicalRawSelectedPhysicalStage
        (width (schedule j)) ξ ζ
        (⟨(p, i), packedA⟩, ⟨(q, k), packedB⟩) *
      unconditionalSelectedCopyRetainedWork
        width schedule ξ ζ j
        (unconditionalActualCanonicalRetainedPhaseTail j)
        (before, ((afterA, afterB), (tailA, tailB)))
  unfold unconditionalActualCanonicalFixedSourceMatchedBranch
  rw [unconditionalSourcePhysicalCleanedStoppingFixedSource_branch_apply
    width schedule ξ ζ j.succ j.succ]
  rw [unconditionalActualMultiscalePhase_EPR_apply
    (schedule j) p q tailA tailB]
  change
    (ePRState B (p, q) *
       ePRState (Fintype.card (Fin (S - 1) → Fin B))
         (tailA, tailB)) *
       dSVDensityRationalHeterogeneousActualPhysicalState
         N width schedule ξ ζ
         (⟨j.succ, historyA⟩, ⟨j.succ, historyB⟩) *
       embezzlementState m (a.2, b.2) =
      (ePRState B (p, q) *
        dSVDensityRationalPhysicalAcceptedOutcome
          (width (schedule j)) N ξ ζ (⟨a.1, i⟩, ⟨b.1, k⟩) *
        embezzlementState m (a.2, b.2)) *
        (dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
          (N := N) width schedule ξ ζ j before *
          (dSVUniformDensityIndependentSharedState
             (L - j.val) N d (afterA, afterB) *
           ePRState (Fintype.card (Fin (S - 1) → Fin B))
             (tailA, tailB)))
  rw [show historyA =
    directDSVSelectedCopyLocalHistoryEquiv j
      (⟨a.1, i⟩, ((fun t => (before t).1), afterA)) from
        unconditionalActualCanonicalCleanedHistorySymm_eq_direct
          j _ _ _ _,
    show historyB =
    directDSVSelectedCopyLocalHistoryEquiv j
      (⟨b.1, k⟩, ((fun t => (before t).2), afterB)) from
        unconditionalActualCanonicalCleanedHistorySymm_eq_direct
          j _ _ _ _]
  rw [directDSVActualStoppingSelectedHistory_sourceProduct]
  unfold dSVDensityRationalPhysicalAcceptedOutcome
  ring

theorem unconditionalActualCanonicalRawSelectedPhysicalStage_eq
    {B N d m : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) :
    unconditionalActualCanonicalRawSelectedPhysicalStage
        (B := B) (N := N) (m := m) w ξ ζ =
      unconditionalActualPhysicalMixedAcceptedRawStage
        (B := B) (N := N) (m := m) w ξ ζ := by
  rfl

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

def directDSVActualReindexedRetainedPOVM
    {C s t ι : Type*}
    [Fintype C] [Fintype s] [Fintype t] [Fintype ι]
    [DecidableEq s] [DecidableEq t] [DecidableEq ι]
    (e : ι ≃ s × t)
    (P : POVM C s) : POVM C ι :=
  reindexedPOVM e.symm (purificationAlicePOVM (k := t) P)

@[simp] theorem directDSVActualReindexedRetainedPOVM_effect
    {C s t ι : Type*}
    [Fintype C] [Fintype s] [Fintype t] [Fintype ι]
    [DecidableEq s] [DecidableEq t] [DecidableEq ι]
    (e : ι ≃ s × t)
    (P : POVM C s) (a : C) (i j : ι) :
    (directDSVActualReindexedRetainedPOVM e P).effect a i j =
      P.effect a (e i).1 (e j).1 *
        if (e i).2 = (e j).2 then 1 else 0 := by
  change
    (P.effect a ⊗ₖ (1 : Matrix t t ℂ)) (e i) (e j) = _
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply]

def directDSVActualBilateralRetainedIndexEquiv
    {s t u v ι κ : Type*}
    (eA : ι ≃ s × t) (eB : κ ≃ u × v) :
    (ι × κ) ≃ ((s × u) × (t × v)) :=
  (Equiv.prodCongr eA eB).trans
    (Equiv.prodProdProdComm s t u v)

def directDSVActualLocalPOVMWinningEffect
    {X Y A B s t : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    (G : Game X Y A B)
    (PA : POVM A s) (PB : POVM B t)
    (x : X) (y : Y) : Matrix (s × t) (s × t) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      PA.effect a ⊗ₖ PB.effect b
    else 0

theorem directDSVActualReindexedRetainedPOVMWinningEffect
    {X Y A B s t u v ι κ : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [Fintype u] [Fintype v]
    [Fintype ι] [Fintype κ]
    [DecidableEq s] [DecidableEq t] [DecidableEq u] [DecidableEq v]
    [DecidableEq ι] [DecidableEq κ]
    (G : Game X Y A B)
    (eA : ι ≃ s × t) (eB : κ ≃ u × v)
    (PA : POVM A s) (PB : POVM B u)
    (x : X) (y : Y) :
    directDSVActualLocalPOVMWinningEffect G
        (directDSVActualReindexedRetainedPOVM eA PA)
        (directDSVActualReindexedRetainedPOVM eB PB)
        x y =
      Matrix.reindex
        (directDSVActualBilateralRetainedIndexEquiv eA eB).symm
        (directDSVActualBilateralRetainedIndexEquiv eA eB).symm
        (directDSVActualLocalPOVMWinningEffect G PA PB x y ⊗ₖ
          (1 : Matrix (t × v) (t × v) ℂ)) := by
  classical
  ext ⟨i, k⟩ ⟨j, l⟩
  by_cases alice_work : (eA i).2 = (eA j).2 <;>
    by_cases bob_work : (eB k).2 = (eB l).2 <;>
      simp [directDSVActualLocalPOVMWinningEffect,
        directDSVActualReindexedRetainedPOVM,
        reindexedPOVM, purificationAlicePOVM,
        directDSVActualBilateralRetainedIndexEquiv,
        Matrix.reindex_apply, Matrix.sum_apply, Matrix.ite_apply,
        Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply,
        Equiv.prodProdProdComm_apply, alice_work, bob_work]

theorem directDSVActualReindexedWinningEffect_quadratic
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (winning : Matrix κ κ ℂ)
    (z : EuclideanSpace ℂ ι) :
    quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
          (Matrix.reindex e.symm e.symm winning)) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ) winning)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e z) := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  change
    (∑ i : ι, (∑ j : ι, winning (e i) (e j) * z j) *
      star (z i)).re =
    (∑ i : κ,
      (∑ j : κ, winning i j * z (e.symm j)) *
        star (z (e.symm i))).re
  congr 1
  calc
    (∑ i : ι, (∑ j : ι, winning (e i) (e j) * z j) *
      star (z i)) =
        ∑ i : ι,
          (∑ j : κ, winning (e i) j * z (e.symm j)) *
            star (z i) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          simpa only [Equiv.symm_apply_apply] using
            (Equiv.sum_comp e
              (fun j : κ => winning (e i) j * z (e.symm j)))
    _ = ∑ i : κ,
          (∑ j : κ, winning i j * z (e.symm j)) *
            star (z (e.symm i)) := by
          simpa only [Equiv.symm_apply_apply] using
            (Equiv.sum_comp e
              (fun i : κ =>
                (∑ j : κ, winning i j * z (e.symm j)) *
                  star (z (e.symm i))))

theorem directDSVActualReindexedRetainedPOVMWinningEffect_tensor_quadratic
    {X Y A B s t u v ι κ : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [Fintype u] [Fintype v]
    [Fintype ι] [Fintype κ]
    [DecidableEq s] [DecidableEq t] [DecidableEq u] [DecidableEq v]
    [DecidableEq ι] [DecidableEq κ]
    (G : Game X Y A B)
    (eA : ι ≃ s × t) (eB : κ ≃ u × v)
    (PA : POVM A s) (PB : POVM B u)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (target : EuclideanSpace ℂ (s × u))
    (work : EuclideanSpace ℂ (t × v))
    (selected :
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (directDSVActualBilateralRetainedIndexEquiv eA eB) z =
          unconditionalMatchedVerifierTensor target work) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM eA PA)
          (directDSVActualReindexedRetainedPOVM eB PB)
          x y)) z =
      ‖work‖ ^ 2 *
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := s × u) (𝕜 := ℂ)
            (directDSVActualLocalPOVMWinningEffect G PA PB x y))
          target := by
  rw [directDSVActualReindexedRetainedPOVMWinningEffect,
    directDSVActualReindexedWinningEffect_quadratic,
    selected, unconditionalMatchedVerifierEffect_tensor_quadratic]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem unconditionalSelectedBranchLocalAction_mul
    {s t : Type*} [Fintype s] [DecidableEq s]
    [Fintype t] [DecidableEq t]
    (U₁ U₂ V₁ V₂ : Matrix.unitaryGroup s ℂ)
    (z : EuclideanSpace ℂ ((s × s) × t)) :
    unconditionalMixedConjugateSelectedBranchLocalAction
      (U₁ * U₂) (V₁ * V₂) z =
    unconditionalMixedConjugateSelectedBranchLocalAction U₁ V₁
      (unconditionalMixedConjugateSelectedBranchLocalAction
        U₂ V₂ z) := by
  classical
  simp [unconditionalMixedConjugateSelectedBranchLocalAction,
    unconditionalMixedConjugateSelectedBranchUnitary,
    Matrix.mulVec_mulVec, Matrix.mul_kronecker_mul]
  apply congrArg
    (fun (W : Matrix ((s × s) × t) ((s × s) × t) ℂ) =>
      W.mulVec (ofLp z))
  simpa using
    (Matrix.mul_kronecker_mul
      ((U₁ : Matrix s s ℂ) ⊗ₖ (V₁ : Matrix s s ℂ))
      ((U₂ : Matrix s s ℂ) ⊗ₖ (V₂ : Matrix s s ℂ))
      (1 : Matrix t t ℂ) (1 : Matrix t t ℂ))

def unconditionalSelectedRetainedBilateralRegroup
    (ι τ : Type) :
    ((ι × τ) × (ι × τ)) ≃ ((ι × ι) × (τ × τ)) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv := by rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl
  right_inv := by rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl

theorem unconditionalRegroupedSelectedRetainedReindexAction
    {κ ι τ δ : Type}
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    [Fintype δ] [DecidableEq δ]
    (e : κ ≃ ι × τ)
    (workEquiv : τ × τ ≃ δ)
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ (κ × κ)) :
    let regroup :=
      (unconditionalSelectedRetainedBilateralRegroup ι τ).trans
        (Equiv.prodCongr (Equiv.refl (ι × ι)) workEquiv)
    let sigma :=
      (Equiv.prodComm ι τ).trans (Equiv.sigmaEquivProd τ ι).symm
    let localEquiv := e.trans sigma
    let A := unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      localEquiv.symm (coherentSharedRandomControlledUnitary
        (fun _ : τ => U))
    let B := unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      localEquiv.symm (coherentSharedRandomControlledUnitary
        (fun _ : τ => V))
    let state := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      ((Equiv.prodCongr e e).trans regroup)
    state
      (toLp 2
        ((((A : Matrix κ κ ℂ) ⊗ₖ
          (B : Matrix κ κ ℂ)).mulVec (ofLp z)))) =
      unconditionalMixedConjugateSelectedBranchLocalAction U V
        (state z) := by
  classical
  dsimp
  ext ⟨⟨i, j⟩, c⟩
  have reindex (f : κ × κ → ℂ) :
      (∑ p : κ × κ, f p) =
        ∑ p : (ι × τ) × (ι × τ),
          f (e.symm p.1, e.symm p.2) := by
    simpa using
      (Equiv.sum_comp (Equiv.prodCongr e e)
        (fun p : (ι × τ) × (ι × τ) =>
          f (e.symm p.1, e.symm p.2)))
  change
    (∑ p : κ × κ,
      (unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
          (((Equiv.sigmaEquivProd τ ι).trans
            (Equiv.prodComm τ ι)).trans e.symm)
          (coherentSharedRandomControlledUnitary
            (fun _ : τ => U)) : Matrix κ κ ℂ)
          (e.symm (i, (workEquiv.symm c).1)) p.1 *
        (unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
          (((Equiv.sigmaEquivProd τ ι).trans
            (Equiv.prodComm τ ι)).trans e.symm)
          (coherentSharedRandomControlledUnitary
            (fun _ : τ => V)) : Matrix κ κ ℂ)
          (e.symm (j, (workEquiv.symm c).2)) p.2 * z p) = _
  rw [reindex]
  simp [unconditionalSourceFixedPureStoppedSigmaReindexedUnitary,
    coherentSharedRandomControlledUnitary,
    unconditionalSelectedRetainedBilateralRegroup,
    unconditionalMixedConjugateSelectedBranchLocalAction,
    unconditionalMixedConjugateSelectedBranchUnitary,
    Matrix.mulVec, dotProduct,
    Matrix.blockDiagonal'_apply, Matrix.one_apply,
    Matrix.kroneckerMap_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft', Fintype.sum_prod_type, mul_assoc]

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def unconditionalActualFixedSourceRetainedHistoryPairEquiv
    {N d L : ℕ} {R : Type} (j : Fin L) :
    (UnconditionalActualCleanedSelectedRetainedIndex
      (N := N) (d := d) j R ×
     UnconditionalActualCleanedSelectedRetainedIndex
      (N := N) (d := d) j R) ≃
    ((Fin j.val →
        (DSVUniformDensityThresholdLocalIndex N d ×
         DSVUniformDensityThresholdLocalIndex N d)) ×
      (((Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d) ×
        (Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d)) ×
       (R × R))) where
  toFun p :=
    ((fun i => (p.1.1 i, p.2.1 i)),
      ((p.1.2.1, p.2.2.1), (p.1.2.2, p.2.2.2)))
  invFun p :=
    ((fun i => (p.1 i).1, (p.2.1.1, p.2.2.1)),
      (fun i => (p.1 i).2, (p.2.1.2, p.2.2.2)))
  left_inv := by
    rintro ⟨⟨beforeA, afterA, phaseA⟩,
      ⟨beforeB, afterB, phaseB⟩⟩
    simp
  right_inv := by
    rintro ⟨before, ⟨⟨afterA, afterB⟩, ⟨phaseA, phaseB⟩⟩⟩
    simp

theorem unconditionalActualFixedSourceFullBilateralRegroup_eq
    {B N d L m : ℕ} {R : Type} (j : Fin L) :
    unconditionalSourcePhysicalCleanedFullBilateralRegroup
        (R := R) (B := B) (N := N) (d := d) (m := m) j =
      (unconditionalSelectedRetainedBilateralRegroup
        (UnconditionalSelectedCopyLocalIndex B d N m)
        (UnconditionalActualCleanedSelectedRetainedIndex
          (N := N) (d := d) j R)).trans
        (Equiv.prodCongr
          (Equiv.refl
            (UnconditionalSelectedCopyLocalIndex B d N m ×
             UnconditionalSelectedCopyLocalIndex B d N m))
          (unconditionalActualFixedSourceRetainedHistoryPairEquiv
            (N := N) (d := d) (R := R) j)) := by
  apply Equiv.ext
  rintro ⟨⟨selectedA, beforeA, afterA, phaseA⟩,
    ⟨selectedB, beforeB, afterB, phaseB⟩⟩
  rfl

theorem unconditionalActualFixedSourceFullPhysicalBilateralStageTransport
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (spectralA spectralB : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L)
    (z : EuclideanSpace ℂ
      (UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m ×
       UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m)) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        phaseSplit j
      (toLp 2
        (((unconditionalActualCleanedSelectedFullStageUnitary
              phaseSplit Q width schedule ξ spectralA A j :
              Matrix (UnconditionalSourcePhysicalStoppingPhaseFiber
                S B N d L m)
                (UnconditionalSourcePhysicalStoppingPhaseFiber
                  S B N d L m) ℂ) ⊗ₖ
            (unconditionalActualCleanedSelectedFullStageUnitary
              phaseSplit Q width schedule ζ spectralB C j :
              Matrix (UnconditionalSourcePhysicalStoppingPhaseFiber
                S B N d L m)
                (UnconditionalSourcePhysicalStoppingPhaseFiber
                  S B N d L m) ℂ)).mulVec
          (ofLp z))) =
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalActualCleanedSelectedStageBucketUnitary
            Q (width (schedule j)) ξ A *
          unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m) spectralA)
        (unconditionalActualCleanedSelectedStageBucketUnitary
            Q (width (schedule j)) ζ C *
          unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m) spectralB)
        (unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
          phaseSplit j z) := by
  classical
  let e :
      UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m ≃
        UnconditionalSelectedCopyLocalIndex B d N m ×
          UnconditionalActualCleanedSelectedRetainedIndex
            (N := N) (d := d) j R :=
    unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      (N := N) (d := d) (m := m) phaseSplit j
  let work :=
    unconditionalActualFixedSourceRetainedHistoryPairEquiv
      (N := N) (d := d) (R := R) j
  let UA :=
    unconditionalActualCleanedSelectedStageBucketUnitary
      Q (width (schedule j)) ξ A *
      unconditionalActualCleanedSelectedStageSpectralUnitary
        (B := B) (m := m) spectralA
  let UB :=
    unconditionalActualCleanedSelectedStageBucketUnitary
      Q (width (schedule j)) ζ C *
      unconditionalActualCleanedSelectedStageSpectralUnitary
        (B := B) (m := m) spectralB
  have transport :=
    unconditionalRegroupedSelectedRetainedReindexAction
      e work UA UB z
  simpa only [unconditionalActualCleanedSelectedFullStageUnitary,
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry,
    unconditionalActualFixedSourceFullBilateralRegroup_eq,
    e, work, UA, UB] using transport

theorem unconditionalActualFixedSourceDecodedMatchedBranch
    {S B N d L m : ℕ}
    (Q : ℕ) (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L)
    (positive : 0 < width (schedule j)) (grid : 0 < N) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualMultiscalePhaseIndexEquiv
          (schedule j)).symm j
      (actualStoppingBranchVector
        (dSVUniformDensityPhysicalAsyncSigmaContinuation
          (unconditionalActualCleanedSelectedFiniteStageDecoder
            (unconditionalActualMultiscalePhaseIndexEquiv
              (schedule j)).symm
            Q width schedule ξ
            (dSVUniformDensityAliceHistorySpectralCopy
              (N := N) ξ) A)
          (unconditionalActualCleanedSelectedFiniteStageDecoder
            (unconditionalActualMultiscalePhaseIndexEquiv
              (schedule j)).symm
            Q width schedule ζ
            ((dSVUniformDensityBobHistoryCopyBasis
              (N := N) ζ)⁻¹) C)
          (actualStoppingQuestionLocalAction
            (unconditionalSourcePhysicalCleanedTargetFirstUnitary
              S B N d L m
              (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
                S B N d L m width schedule ξ))
            (unconditionalSourcePhysicalCleanedTargetFirstUnitary
              S B N d L m
              (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
                S B N d L m width schedule ζ))
            (unconditionalSourcePhysicalCleanedStoppingFixedSource
              S B N d L m))) j.succ j.succ) =
      unconditionalSelectedCopyCleanedMatchedBranch
        (N := N) (B := B) (m := m)
        Q width schedule ξ ζ A C j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := S) (B := B) (N := N) (d := d) (L := L) j) := by
  let phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × UnconditionalActualCanonicalRetainedPhaseIndex S B :=
    (unconditionalActualMultiscalePhaseIndexEquiv
      (B := B) (schedule j)).symm
  have sameSource :
      actualStoppingBranchVector
          (unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
            S B N d L m
            (dSVDensityRationalHeterogeneousOriginalStoppedState
              S B N d L m width schedule ξ ζ)) j.succ j.succ =
        unconditionalActualCanonicalFixedSourceMatchedBranch
          (B := B) (m := m) width schedule ξ ζ j := by
    unfold unconditionalActualCanonicalFixedSourceMatchedBranch
    rw [unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction]
  change
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        phaseSplit j
      (actualStoppingBranchVector
        (dSVUniformDensityPhysicalAsyncSigmaContinuation
          (unconditionalActualCleanedSelectedFiniteStageDecoder
            phaseSplit Q width schedule ξ
            (dSVUniformDensityAliceHistorySpectralCopy
              (N := N) ξ) A)
          (unconditionalActualCleanedSelectedFiniteStageDecoder
            phaseSplit Q width schedule ζ
            ((dSVUniformDensityBobHistoryCopyBasis
              (N := N) ζ)⁻¹) C)
          (actualStoppingQuestionLocalAction
            (unconditionalSourcePhysicalCleanedTargetFirstUnitary
              S B N d L m
              (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
                S B N d L m width schedule ξ))
            (unconditionalSourcePhysicalCleanedTargetFirstUnitary
              S B N d L m
              (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
                S B N d L m width schedule ζ))
            (unconditionalSourcePhysicalCleanedStoppingFixedSource
              S B N d L m))) j.succ j.succ) = _
  rw [unconditionalActualCleanedSelectedMatchedStoppingBranch
    phaseSplit Q width schedule ξ ζ A C j]
  rw [unconditionalActualFixedSourceFullPhysicalBilateralStageTransport]
  rw [sameSource,
    unconditionalActualCanonicalFullSource_eq_rawSelectedStage]
  rw [unconditionalSelectedBranchLocalAction_mul,
    unconditionalMixedConjugateSelectedBranch_tensorAction,
    unconditionalActualCanonicalRawSelectedPhysicalStage_eq,
    unconditionalActualPhysicalMixedAcceptedSpectralGauge_stage
      positive grid ξ ζ,
    unconditionalMixedConjugateSelectedBranch_tensorAction]
  congr 1

end

end QuantumParallelRepetition
