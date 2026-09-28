/-
Copyright (c) 2026 the openai/ten-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/openai/ten-proofs (commit 94bc0feb, 2026-08-01) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: QuantumParallelRepetition.lean
-/
module
public import Mathlib
public import MIPRE.Background.Repetition.TenProofs.QuantumParallelRepetition.Part02

@[expose] public section

-- Part 3 of 8 of upstream's single module `QuantumParallelRepetition.lean`: its lines
-- 17934-26827, cut between top-level `noncomputable section` blocks by
-- scripts/vendor-repetition.py (the Palomar registry caps a Lean file at 10,000 lines).
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset


noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

attribute [local instance] Classical.propDecidable

def dSVDensityRationalHeterogeneousActualAcceptSet
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun j : Fin L =>
    accepted j (history j.castSucc)

def dSVDensityRationalHeterogeneousActualFirstAccepted
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) : Fin (L + 1) := by
  classical
  let hits := dSVDensityRationalHeterogeneousActualAcceptSet
    accepted history
  exact if nonempty : hits.Nonempty then
    (hits.min' nonempty).succ
  else 0

theorem dSVDensityRationalHeterogeneousActualFirstAccepted_prefix_iff
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) (j : Fin L) :
    dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted history = j.succ ↔
      accepted j (history j.castSucc) ∧
        ∀ i : Fin L, i < j →
          ¬ accepted i (history i.castSucc) := by
  classical
  unfold dSVDensityRationalHeterogeneousActualFirstAccepted
  simpa [dSVDensityRationalHeterogeneousActualAcceptSet] using
    dSVUniformDensityFirstAcceptFinitePrefix
      (dSVDensityRationalHeterogeneousActualAcceptSet
        accepted history) j

theorem dSVDensityRationalHeterogeneousActualFirstAccepted_zero_iff
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) :
    dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted history = 0 ↔
      ∀ i : Fin L, ¬ accepted i (history i.castSucc) := by
  classical
  unfold dSVDensityRationalHeterogeneousActualFirstAccepted
  let hits := dSVDensityRationalHeterogeneousActualAcceptSet
    accepted history
  change (if h : hits.Nonempty then (hits.min' h).succ else 0) = 0 ↔ _
  by_cases nonempty : hits.Nonempty
  · rw [dif_pos nonempty]
    constructor
    · intro impossible
      exact (Fin.succ_ne_zero _ impossible).elim
    · intro none
      obtain ⟨j, member⟩ := nonempty
      have hit : accepted j (history j.castSucc) := by
        simpa [hits,
          dSVDensityRationalHeterogeneousActualAcceptSet]
          using member
      exact (none j hit).elim
  · rw [dif_neg nonempty]
    simp only [true_iff]
    intro j hit
    apply nonempty
    refine ⟨j, ?_⟩
    simpa [hits,
      dSVDensityRationalHeterogeneousActualAcceptSet] using hit

def dSVDensityRationalHeterogeneousActualFirstAcceptEquiv
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop) :
    Equiv.Perm (Σ _ : Fin (L + 1), Fin (L + 1) → β) where
  toFun q :=
    ⟨(Equiv.swap (0 : Fin (L + 1))
      (dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted q.2)) q.1, q.2⟩
  invFun q :=
    ⟨(Equiv.swap (0 : Fin (L + 1))
      (dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted q.2)) q.1, q.2⟩
  left_inv := by
    rintro ⟨flag, history⟩
    simp
  right_inv := by
    rintro ⟨flag, history⟩
    simp

def dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop) :
    Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ :=
  permutationUnitary
    (dSVDensityRationalHeterogeneousActualFirstAcceptEquiv
      accepted)

theorem dSVDensityRationalHeterogeneousActualFirstAcceptUnitary_mulVec
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (v : (Σ _ : Fin (L + 1), Fin (L + 1) → β) → ℂ)
    (flag : Fin (L + 1)) (history : Fin (L + 1) → β) :
    ((dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
        accepted :
      Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
        (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)).mulVec
        v ⟨flag, history⟩ =
      v ⟨(Equiv.swap (0 : Fin (L + 1))
        (dSVDensityRationalHeterogeneousActualFirstAccepted
          accepted history)) flag, history⟩ := by
  rw [dSVDensityRationalHeterogeneousActualFirstAcceptUnitary,
    permutationUnitary_val, Matrix.permMatrix_mulVec]
  rfl

theorem
    dSVDensityRationalHeterogeneousActualFirstAcceptUnitary_zeroFlag
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (v : (Fin (L + 1) → β) → ℂ)
    (flag : Fin (L + 1)) (history : Fin (L + 1) → β) :
    ((dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
        accepted :
      Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
        (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)).mulVec
        (fun q => if q.1 = 0 then v q.2 else 0)
        ⟨flag, history⟩ =
      if flag =
        dSVDensityRationalHeterogeneousActualFirstAccepted
          accepted history
      then v history else 0 := by
  rw [dSVDensityRationalHeterogeneousActualFirstAcceptUnitary_mulVec]
  let selected :=
    dSVDensityRationalHeterogeneousActualFirstAccepted
      accepted history
  change
    (if (Equiv.swap (0 : Fin (L + 1)) selected) flag = 0
    then v history else 0) =
    if flag = selected then v history else 0
  congr 1
  apply propext
  constructor
  · intro zero
    have injective :=
      (Equiv.swap (0 : Fin (L + 1)) selected).injective
    apply injective
    simpa using zero
  · intro same
    subst flag
    simp

def dSVDensityRationalHeterogeneousActualCopyAccepted
    {S N d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (j : Fin L)
    (atom : DSVUniformDensityThresholdLocalIndex N d) : Prop :=
  dSVDensityRationalCompletePhysicalStoppingCopyAccepted
    (width (schedule j)) ξ atom

def dSVDensityRationalHeterogeneousActualCopyCondition
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (flag : Fin (L + 1)) (i : Fin (L + 1)) (atom : β) : Prop :=
  if active : i.val < L then
    if flag = 0 then
      ¬ accepted ⟨i.val, active⟩ atom
    else if i.val + 1 < flag.val then
      ¬ accepted ⟨i.val, active⟩ atom
    else if i.val + 1 = flag.val then
      accepted ⟨i.val, active⟩ atom
    else True
  else True

theorem
    dSVDensityRationalHeterogeneousActualFirstAccepted_allFlags_iff
    {β : Type*} {L : ℕ}
    (accepted : Fin L → β → Prop)
    (history : Fin (L + 1) → β) (flag : Fin (L + 1)) :
    dSVDensityRationalHeterogeneousActualFirstAccepted
        accepted history = flag ↔
      ∀ i : Fin (L + 1),
        dSVDensityRationalHeterogeneousActualCopyCondition
          accepted flag i (history i) := by
  induction flag using Fin.cases with
  | zero =>
      rw [dSVDensityRationalHeterogeneousActualFirstAccepted_zero_iff]
      constructor
      · intro failed i
        by_cases active : i.val < L
        · have actual := failed (⟨i.val, active⟩ : Fin L)
          simpa [dSVDensityRationalHeterogeneousActualCopyCondition,
            active] using actual
        · simp [dSVDensityRationalHeterogeneousActualCopyCondition,
            active]
      · intro all i
        have actual := all i.castSucc
        simpa [dSVDensityRationalHeterogeneousActualCopyCondition,
          i.isLt] using actual
  | succ j =>
      rw [dSVDensityRationalHeterogeneousActualFirstAccepted_prefix_iff]
      constructor
      · rintro ⟨hit, earlier⟩ i
        by_cases active : i.val < L
        · by_cases before : i.val < j.val
          · have failure := earlier
              (⟨i.val, active⟩ : Fin L) (by exact before)
            simpa [dSVDensityRationalHeterogeneousActualCopyCondition,
              active, Fin.succ_ne_zero, before] using failure
          · by_cases equal : i.val = j.val
            · have same : i = j.castSucc := Fin.ext equal
              subst i
              simpa [dSVDensityRationalHeterogeneousActualCopyCondition,
                j.isLt, Fin.succ_ne_zero] using hit
            · simp [dSVDensityRationalHeterogeneousActualCopyCondition,
                active, Fin.succ_ne_zero, before, equal]
        · simp [dSVDensityRationalHeterogeneousActualCopyCondition,
            active]
      · intro all
        constructor
        · have actual := all j.castSucc
          simpa [dSVDensityRationalHeterogeneousActualCopyCondition,
            j.isLt, Fin.succ_ne_zero] using actual
        · intro i before
          have actual := all i.castSucc
          simpa [dSVDensityRationalHeterogeneousActualCopyCondition,
            i.isLt, Fin.succ_ne_zero, before] using actual

theorem
    dSVDensityRationalHeterogeneousActualFirstAccepted_sourceProduct
    {β : Type*} [Fintype β] {L : ℕ}
    (accepted : Fin L → β → Prop)
    (flag : Fin (L + 1))
    (A D : Fin (L + 1) → β → ℂ) :
    (∑ history : Fin (L + 1) → β,
      (∏ i : Fin (L + 1), A i (history i)) *
        (if flag =
          dSVDensityRationalHeterogeneousActualFirstAccepted
            accepted history
        then ∏ i : Fin (L + 1), D i (history i)
        else 0)) =
      ∏ i : Fin (L + 1),
        ∑ atom : β, A i atom *
          (if dSVDensityRationalHeterogeneousActualCopyCondition
              accepted flag i atom
          then D i atom else 0) := by
  classical
  have single (history : Fin (L + 1) → β) :
      (∏ i : Fin (L + 1), A i (history i)) *
          (if flag =
            dSVDensityRationalHeterogeneousActualFirstAccepted
              accepted history
          then ∏ i : Fin (L + 1), D i (history i)
          else 0) =
        ∏ i : Fin (L + 1),
          (A i (history i) *
            (if dSVDensityRationalHeterogeneousActualCopyCondition
                accepted flag i (history i)
            then D i (history i) else 0)) := by
    by_cases selected :
        dSVDensityRationalHeterogeneousActualFirstAccepted
          accepted history = flag
    · have all :=
        (dSVDensityRationalHeterogeneousActualFirstAccepted_allFlags_iff
          accepted history flag).mp selected
      rw [if_pos selected.symm, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [if_pos (all i)]
    · have absent : ¬ ∀ i : Fin (L + 1),
          dSVDensityRationalHeterogeneousActualCopyCondition
            accepted flag i (history i) := by
        intro all
        exact selected
          ((dSVDensityRationalHeterogeneousActualFirstAccepted_allFlags_iff
            accepted history flag).mpr all)
      push Not at absent
      obtain ⟨i, rejected⟩ := absent
      have zero :
          (∏ k : Fin (L + 1),
            A k (history k) *
              (if dSVDensityRationalHeterogeneousActualCopyCondition
                  accepted flag k (history k)
              then D k (history k) else 0)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [rejected]
      rw [if_neg (Ne.symm selected), mul_zero, zero]
  calc
    _ = ∑ history : Fin (L + 1) → β,
      ∏ i : Fin (L + 1),
        (A i (history i) *
          (if dSVDensityRationalHeterogeneousActualCopyCondition
              accepted flag i (history i)
          then D i (history i) else 0)) := by
        apply Finset.sum_congr rfl
        intro history _
        exact single history
    _ = _ :=
      (Fintype.prod_sum fun i : Fin (L + 1) => fun atom : β =>
        A i atom *
          (if dSVDensityRationalHeterogeneousActualCopyCondition
              accepted flag i atom
          then D i atom else 0)).symm

def dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (U : Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ :=
  (dSVDensityRationalFirstAcceptActualTensorBasis
      (L := L) U)⁻¹ *
    dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
      accepted *
    dSVDensityRationalFirstAcceptActualTensorBasis
      (L := L) U

def dSVDensityRationalHeterogeneousActualAliceUnitary
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ :=
  dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
    (dSVDensityRationalHeterogeneousActualCopyAccepted
      width schedule ξ)
    (dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ)

def dSVDensityRationalHeterogeneousActualBobUnitary
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ζ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ :=
  dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
    (dSVDensityRationalHeterogeneousActualCopyAccepted
      width schedule ζ)
    ((dSVUniformDensityBobHistoryCopyBasis (N := N) ζ)⁻¹)

def dSVDensityRationalHeterogeneousActualPhysicalState
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ×
       DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) :=
  toLp 2
    ((((dSVDensityRationalHeterogeneousActualAliceUnitary
          N width schedule ξ :
          Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ) ⊗ₖ
        (dSVDensityRationalHeterogeneousActualBobUnitary
          N width schedule ζ :
          Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ)).mulVec
      (ofLp
        (dSVUniformDensityThresholdWholeHistorySharedState
          N d L))))

theorem dSVDensityRationalHeterogeneousActualPhysicalState_norm
    {S N d L : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    ‖dSVDensityRationalHeterogeneousActualPhysicalState
      N width schedule ξ ζ‖ = 1 := by
  unfold dSVDensityRationalHeterogeneousActualPhysicalState
  rw [dSVUniformDensityMixedProtocolLocalAction_norm]
  exact dSVUniformDensityThresholdWholeHistorySharedState_norm
    grid dimension L

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder

def dSVDensityRationalHeterogeneousPhysicalStageOutcome
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (k : ℕ) (alice bob : Bool) : ℝ :=
  if active : k < L then
    ‖dSVDensityRationalCompleteProjectiveOutcome
      (width (schedule ⟨k, active⟩)) N ξ ζ alice bob‖ ^ 2
  else if alice = false ∧ bob = false then 1 else 0

def dSVDensityRationalHeterogeneousPhysicalStageContinue
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageOutcome
    N width schedule ξ ζ k false false

def dSVDensityRationalHeterogeneousPhysicalStageSuccess
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageOutcome
    N width schedule ξ ζ k true true

def dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageOutcome
      N width schedule ξ ζ k true false +
    dSVDensityRationalHeterogeneousPhysicalStageOutcome
      N width schedule ξ ζ k false true

theorem dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (k : ℕ) (alice bob : Bool) :
    0 ≤ dSVDensityRationalHeterogeneousPhysicalStageOutcome
      N width schedule ξ ζ k alice bob := by
  unfold dSVDensityRationalHeterogeneousPhysicalStageOutcome
  split_ifs <;> positivity

theorem dSVDensityRationalHeterogeneousPhysicalStage_partition
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) :
    dSVDensityRationalHeterogeneousPhysicalStageContinue
        N width schedule ξ ζ k +
      dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ k +
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k = 1 := by
  by_cases active : k < L
  · simpa [
      dSVDensityRationalHeterogeneousPhysicalStageContinue,
      dSVDensityRationalHeterogeneousPhysicalStageSuccess,
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous,
      dSVDensityRationalHeterogeneousPhysicalStageOutcome,
      active,
      dSVDensityRationalActualMixedContinueMass,
      dSVDensityRationalActualMixedSuccessMass,
      dSVDensityRationalActualMixedAsynchronousMass] using
        (dSVDensityRationalActualMixed_mass_partition
          grid dimension (width (schedule ⟨k, active⟩)) ξ ζ)
  · simp [
      dSVDensityRationalHeterogeneousPhysicalStageContinue,
      dSVDensityRationalHeterogeneousPhysicalStageSuccess,
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous,
      dSVDensityRationalHeterogeneousPhysicalStageOutcome,
      active]

theorem
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_hazard
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k.val =
      dSVDensityRationalPhysicalProjectorCrossHazard
        N (width (schedule k)) ξ ζ := by
  simpa [
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous,
    dSVDensityRationalHeterogeneousPhysicalStageOutcome,
    k.isLt,
    dSVDensityRationalActualMixedAsynchronousMass] using
      (dSVDensityRationalActualMixedAsynchronousMass_eq_crossHazard
        (width (schedule k)) N ξ ζ)

def dSVDensityRationalHeterogeneousPhysicalSurvival
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVHeterogeneousRealPrefix
    (dSVDensityRationalHeterogeneousPhysicalStageContinue
      N width schedule ξ ζ) k

theorem dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) :
    0 ≤ dSVDensityRationalHeterogeneousPhysicalSurvival
      N width schedule ξ ζ k := by
  unfold dSVDensityRationalHeterogeneousPhysicalSurvival
  apply dSVHeterogeneousRealPrefix_nonneg
  intro j
  exact dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
    N width schedule ξ ζ j false false

def dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ k ∈ Finset.range L,
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k *
      dSVDensityRationalHeterogeneousPhysicalStageSuccess
        N width schedule ξ ζ k

def dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ k ∈ Finset.range L,
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k *
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k

def dSVDensityRationalHeterogeneousPhysicalTerminalMass
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalSurvival
    N width schedule ξ ζ L

theorem
    dSVDensityRationalHeterogeneousPhysicalStopped_mass_partition
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
        N width schedule ξ ζ +
      dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule ξ ζ +
      dSVDensityRationalHeterogeneousPhysicalTerminalMass
          N width schedule ξ ζ = 1 := by
  let continuation :=
    dSVDensityRationalHeterogeneousPhysicalStageContinue
      N width schedule ξ ζ
  let success :=
    dSVDensityRationalHeterogeneousPhysicalStageSuccess
      N width schedule ξ ζ
  let asynchronous :=
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
      N width schedule ξ ζ
  have stage (k : ℕ) :
      success k + asynchronous k = 1 - continuation k := by
    dsimp [continuation, success, asynchronous]
    linarith [
      dSVDensityRationalHeterogeneousPhysicalStage_partition
        grid dimension width schedule ξ ζ k]
  have escape :=
    dSVHeterogeneousRealStopping_escape_identity
      continuation L
  change
    (∑ k ∈ Finset.range L,
      dSVHeterogeneousRealPrefix continuation k * success k) +
      (∑ k ∈ Finset.range L,
        dSVHeterogeneousRealPrefix continuation k *
          asynchronous k) +
      dSVHeterogeneousRealPrefix continuation L = 1
  have combined :
      (∑ k ∈ Finset.range L,
        dSVHeterogeneousRealPrefix continuation k * success k) +
      (∑ k ∈ Finset.range L,
        dSVHeterogeneousRealPrefix continuation k *
          asynchronous k) =
      ∑ k ∈ Finset.range L,
        dSVHeterogeneousRealPrefix continuation k *
          (1 - continuation k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← mul_add, stage k]
  rw [combined, escape]
  ring

theorem
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_eq_hazard
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
        N width schedule ξ ζ =
      ∑ k : Fin L,
        dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k.val *
          dSVDensityRationalPhysicalProjectorCrossHazard
            N (width (schedule k)) ξ ζ := by
  classical
  unfold
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
  calc
    (∑ k ∈ Finset.range L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k) =
      ∑ k : Fin L,
        dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k.val *
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k.val := by
          simpa using
            (Fin.sum_univ_eq_sum_range
              (fun k : ℕ =>
                dSVDensityRationalHeterogeneousPhysicalSurvival
                    N width schedule ξ ζ k *
                  dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
                    N width schedule ξ ζ k) L).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [
        dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_hazard
          N width schedule ξ ζ k]

theorem
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_nonneg
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    0 ≤
      dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
        N width schedule ξ ζ := by
  unfold
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg
    (dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
      N width schedule ξ ζ k)
  exact add_nonneg
    (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
      N width schedule ξ ζ k true false)
    (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
      N width schedule ξ ζ k false true)

theorem dSVDensityRationalHeterogeneousPhysicalTerminalMass_nonneg
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    0 ≤ dSVDensityRationalHeterogeneousPhysicalTerminalMass
      N width schedule ξ ζ :=
  dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
    N width schedule ξ ζ L

def dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) : ℝ :=
  dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
      N width schedule ξ ζ k /
    (dSVDensityRationalHeterogeneousPhysicalStageSuccess
        N width schedule ξ ζ k +
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k)

theorem
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_escape_mul_ratio
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : ℕ) :
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k =
      (dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ k +
        dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k) *
        dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
          N width schedule ξ ζ k := by
  let p := dSVDensityRationalHeterogeneousPhysicalStageSuccess
    N width schedule ξ ζ k
  let h := dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
    N width schedule ξ ζ k
  have p_nonnegative : 0 ≤ p :=
    dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
      N width schedule ξ ζ k true true
  have h_nonnegative : 0 ≤ h := add_nonneg
    (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
      N width schedule ξ ζ k true false)
    (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
      N width schedule ξ ζ k false true)
  change h = (p + h) * (h / (p + h))
  by_cases vanished : p + h = 0
  · have h_zero : h = 0 := by linarith
    simp [h_zero]
  · field_simp

theorem
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_eq_ratioLedger
    {d S L : ℕ} (N : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
        N width schedule ξ ζ =
      ∑ k ∈ Finset.range L,
        dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k *
          (dSVDensityRationalHeterogeneousPhysicalStageSuccess
              N width schedule ξ ζ k +
            dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
              N width schedule ξ ζ k) *
          dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
            N width schedule ξ ζ k := by
  unfold
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
  apply Finset.sum_congr rfl
  intro k _
  calc
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k *
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        ((dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k) *
          dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
            N width schedule ξ ζ k) :=
      congrArg
        (fun x : ℝ =>
          dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k * x)
        (dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_escape_mul_ratio
          N width schedule ξ ζ k)
    _ = _ := by ring

theorem
    dSVDensityRationalHeterogeneousPhysicalStageDiagonalSuccess_lower
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d) (k : Fin L) :
    1 / (2 * (width (schedule k) + 1) * (d : ℝ)) ≤
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ := by
  have width_positive : 0 < width (schedule k) :=
    lt_of_lt_of_le (by norm_num) (large (schedule k))
  have mass := dSVDensityRationalLargeWidthDiagonalMass_half
    width_positive grid (fine (schedule k)) ξ
  have dimension_real : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  calc
    1 / (2 * (width (schedule k) + 1) * (d : ℝ)) =
      (1 / (2 * (width (schedule k) + 1))) / (d : ℝ) := by
        rw [div_div]
    _ ≤ dSVDensityRationalLeftProjectiveDiagonalMass
        (width (schedule k)) N ξ / (d : ℝ) :=
      (div_le_div_iff_of_pos_right dimension_real).mpr mass
    _ = dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ := by
      rw [dSVDensityRationalPhysicalDiagonalBornSuccess_eq]

theorem
    dSVDensityRationalHeterogeneousPhysicalStage_escape_ge_diagonal
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ ≤
      dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ k.val +
        dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k.val := by
  simpa [
    dSVDensityRationalHeterogeneousPhysicalStageSuccess,
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous,
    dSVDensityRationalHeterogeneousPhysicalStageOutcome,
    k.isLt,
    dSVDensityRationalActualMixedSuccessMass,
    dSVDensityRationalActualMixedAsynchronousMass]
    using dSVDensityRationalActualMixed_escape_ge_diagonal
      grid dimension (width (schedule k)) ξ ζ

theorem
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_relative_diagonal_le
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k.val /
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ ≤
      8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (width (schedule k) + 1) * ((d : ℝ) / N) := by
  rw [
    dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_eq_hazard
      N width schedule ξ ζ k]
  exact dSVDensityRationalLargeWidthPhysicalRelativeHazard_le
    dimension (large (schedule k)) grid (fine (schedule k)) ξ ζ

theorem
    dSVDensityRationalHeterogeneousPhysicalStageHazardRatio_le_relative_diagonal
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
        N width schedule ξ ζ k.val ≤
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k.val /
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule k)) ξ := by
  have width_positive : 0 < width (schedule k) :=
    lt_of_lt_of_le (by norm_num) (large (schedule k))
  have self_positive :=
    dSVDensityRationalLargeWidthPhysicalDiagonalBornSuccess_pos
      dimension width_positive grid (fine (schedule k)) ξ
  have self_lower :=
    dSVDensityRationalHeterogeneousPhysicalStage_escape_ge_diagonal
      grid dimension width schedule ξ ζ k
  have asynchronous_nonnegative :
      0 ≤ dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k.val := by
    exact add_nonneg
      (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
        N width schedule ξ ζ k.val true false)
      (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
        N width schedule ξ ζ k.val false true)
  unfold dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
  exact div_le_div_of_nonneg_left
    asynchronous_nonnegative self_positive self_lower

theorem
    dSVDensityRationalHeterogeneousPhysicalStageHazardRatio_le_targetDistance
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W : ℝ} (upper : ∀ s, width s ≤ W)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
        N width schedule ξ ζ k.val ≤
      8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (W + 1) * ((d : ℝ) / N) := by
  calc
    _ ≤ dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
          N width schedule ξ ζ k.val /
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule k)) ξ :=
      dSVDensityRationalHeterogeneousPhysicalStageHazardRatio_le_relative_diagonal
        grid dimension width large fine schedule ξ ζ k
    _ ≤ 8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (width (schedule k) + 1) * ((d : ℝ) / N) :=
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous_relative_diagonal_le
        grid dimension width large fine schedule ξ ζ k
    _ ≤ 8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (W + 1) * ((d : ℝ) / N) := by
      have scale := upper (schedule k)
      have grid_cost : 0 ≤ (d : ℝ) / N := by positivity
      nlinarith [mul_nonneg grid_cost (sub_nonneg.mpr scale)]

theorem dSVDensityRationalHeterogeneousPhysicalStoppedEscape_budget
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    (∑ k ∈ Finset.range L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        (dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k)) ≤ 1 := by
  let continuation :=
    dSVDensityRationalHeterogeneousPhysicalStageContinue
      N width schedule ξ ζ
  let escape : ℕ → ℝ := fun k =>
    dSVDensityRationalHeterogeneousPhysicalStageSuccess
        N width schedule ξ ζ k +
      dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
        N width schedule ξ ζ k
  have continuation_nonnegative : ∀ k, 0 ≤ continuation k := by
    intro k
    exact
      dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
        N width schedule ξ ζ k false false
  have stage : ∀ k, continuation k + escape k ≤ 1 := by
    intro k
    have actual :=
      dSVDensityRationalHeterogeneousPhysicalStage_partition
        grid dimension width schedule ξ ζ k
    dsimp [continuation, escape]
    linarith
  simpa [continuation, escape,
    dSVDensityRationalHeterogeneousPhysicalSurvival]
    using dSVHeterogeneousRealStopping_escape_budget
      continuation escape continuation_nonnegative stage L

theorem
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_le_targetDistance
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W : ℝ} (upper : ∀ s, width s ≤ W) (W_nonnegative : 0 ≤ W)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
        N width schedule ξ ζ ≤
      8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
        2 * (W + 1) * ((d : ℝ) / N) := by
  let bound : ℝ :=
    8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
      2 * (W + 1) * ((d : ℝ) / N)
  have bound_nonnegative : 0 ≤ bound := by
    dsimp [bound]
    positivity
  have escape_budget :=
    dSVDensityRationalHeterogeneousPhysicalStoppedEscape_budget
      grid dimension width schedule ξ ζ
  rw [
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_eq_ratioLedger]
  change
    (∑ k ∈ Finset.range L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        (dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k) *
        dSVDensityRationalHeterogeneousPhysicalStageHazardRatio
          N width schedule ξ ζ k) ≤ bound
  calc
    _ ≤ ∑ k ∈ Finset.range L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        (dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k) * bound := by
      apply Finset.sum_le_sum
      intro k member
      have active : k < L := Finset.mem_range.mp member
      let stage : Fin L := ⟨k, active⟩
      have ratio :=
        dSVDensityRationalHeterogeneousPhysicalStageHazardRatio_le_targetDistance
          grid dimension width large fine upper schedule ξ ζ stage
      have survival_nonnegative :=
        dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
          N width schedule ξ ζ k
      have success_nonnegative :=
        dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
          N width schedule ξ ζ k true true
      have asynchronous_nonnegative :
          0 ≤
            dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
              N width schedule ξ ζ k := by
        exact add_nonneg
          (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
            N width schedule ξ ζ k true false)
          (dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
            N width schedule ξ ζ k false true)
      have coefficient_nonnegative :
          0 ≤
            dSVDensityRationalHeterogeneousPhysicalSurvival
                N width schedule ξ ζ k *
              (dSVDensityRationalHeterogeneousPhysicalStageSuccess
                  N width schedule ξ ζ k +
                dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
                  N width schedule ξ ζ k) :=
        mul_nonneg survival_nonnegative
          (add_nonneg success_nonnegative asynchronous_nonnegative)
      apply mul_le_mul_of_nonneg_left _ coefficient_nonnegative
      simpa [stage, bound] using ratio
    _ =
      (∑ k ∈ Finset.range L,
        dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k *
          (dSVDensityRationalHeterogeneousPhysicalStageSuccess
              N width schedule ξ ζ k +
            dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
              N width schedule ξ ζ k)) * bound := by
      rw [Finset.sum_mul]
    _ ≤ bound := by
      nlinarith [mul_nonneg bound_nonnegative
        (sub_nonneg.mpr escape_budget)]

def dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
    (d : ℕ) (W : ℝ) : ℝ :=
  1 / (2 * (W + 1) * (d : ℝ))

theorem
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate_pos
    {d : ℕ} (dimension : 0 < d)
    {W : ℝ} (W_nonnegative : 0 ≤ W) :
    0 < dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
      d W := by
  unfold dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
  positivity

theorem
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate_le_half
    {d : ℕ} (dimension : 0 < d)
    {W : ℝ} (W_nonnegative : 0 ≤ W) :
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
      d W ≤ (1 / 2 : ℝ) := by
  have real_dimension : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  have dimension_one : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt dimension))
  have denominator : 0 < 2 * (W + 1) * (d : ℝ) := by
    positivity
  unfold dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
  apply (div_le_div_iff₀ denominator (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith [mul_nonneg W_nonnegative real_dimension.le]

theorem
    dSVDensityRationalHeterogeneousPhysicalStageDiagonalSuccess_ge_uniform
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W : ℝ} (W_nonnegative : 0 ≤ W)
    (upper : ∀ s, width s ≤ W)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
        d W ≤
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ := by
  have real_dimension : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  have width_positive : 0 < width (schedule k) :=
    lt_of_lt_of_le (by norm_num) (large (schedule k))
  have wide_positive : 0 < 2 * (W + 1) * (d : ℝ) := by
    positivity
  have stage_positive :
      0 < 2 * (width (schedule k) + 1) * (d : ℝ) := by
    positivity
  have width_bound := upper (schedule k)
  calc
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
        d W = 1 / (2 * (W + 1) * (d : ℝ)) := rfl
    _ ≤ 1 / (2 * (width (schedule k) + 1) * (d : ℝ)) := by
      apply (div_le_div_iff₀ wide_positive stage_positive).mpr
      nlinarith [mul_nonneg real_dimension.le
        (sub_nonneg.mpr width_bound)]
    _ ≤ dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule k)) ξ :=
      dSVDensityRationalHeterogeneousPhysicalStageDiagonalSuccess_lower
        grid dimension width large fine schedule ξ k

theorem
    dSVDensityRationalHeterogeneousPhysicalStageContinue_le_uniform
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W : ℝ} (W_nonnegative : 0 ≤ W)
    (upper : ∀ s, width s ≤ W)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (k : Fin L) :
    dSVDensityRationalHeterogeneousPhysicalStageContinue
        N width schedule ξ ζ k.val ≤
      1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W := by
  have floor :=
    dSVDensityRationalHeterogeneousPhysicalStageDiagonalSuccess_ge_uniform
      grid dimension width large fine W_nonnegative upper schedule ξ k
  have escape :=
    dSVDensityRationalHeterogeneousPhysicalStage_escape_ge_diagonal
      grid dimension width schedule ξ ζ k
  have partition :=
    dSVDensityRationalHeterogeneousPhysicalStage_partition
      grid dimension width schedule ξ ζ k.val
  linarith

theorem
    dSVDensityRationalHeterogeneousPhysicalTerminalMass_le_pow
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W : ℝ} (W_nonnegative : 0 ≤ W)
    (upper : ∀ s, width s ≤ W)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalTerminalMass
        N width schedule ξ ζ ≤
      (1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W) ^ L := by
  let continuation :=
    dSVDensityRationalHeterogeneousPhysicalStageContinue
      N width schedule ξ ζ
  let c : ℝ :=
    1 - dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
      d W
  have rate_bounded :=
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate_le_half
      dimension W_nonnegative
  have c_nonnegative : 0 ≤ c := by
    dsimp [c]
    linarith
  have continuation_nonnegative : ∀ k, 0 ≤ continuation k := by
    intro k
    exact
      dSVDensityRationalHeterogeneousPhysicalStageOutcome_nonneg
        N width schedule ξ ζ k false false
  have prefix_bound : ∀ k : ℕ, k ≤ L →
      dSVHeterogeneousRealPrefix continuation k ≤ c ^ k := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [dSVHeterogeneousRealPrefix]
    | succ k induction =>
        intro within
        have active : k < L := by omega
        have previous := induction (by omega : k ≤ L)
        let stage : Fin L := ⟨k, active⟩
        have next :=
          dSVDensityRationalHeterogeneousPhysicalStageContinue_le_uniform
            grid dimension width large fine W_nonnegative upper
            schedule ξ ζ stage
        change continuation k ≤ c at next
        rw [dSVHeterogeneousRealPrefix_succ, pow_succ]
        exact mul_le_mul previous next
          (continuation_nonnegative k) (pow_nonneg c_nonnegative k)
  change dSVHeterogeneousRealPrefix continuation L ≤ c ^ L
  exact prefix_bound L (le_refl L)

theorem
    dSVDensityRationalHeterogeneousPhysical_exists_positive_horizon
    {d : ℕ} (dimension : 0 < d)
    {W ε : ℝ} (W_nonnegative : 0 ≤ W) (precision : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧
      (1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W) ^ L ≤ ε ^ 2 := by
  have rate :=
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate_pos
      dimension W_nonnegative
  have bounded :=
    dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate_le_half
      dimension W_nonnegative
  have continuation : 0 ≤
      1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W := by
    linarith
  have square : 0 < ε ^ 2 := sq_pos_of_pos precision
  obtain ⟨k, tail⟩ := exists_pow_lt_of_lt_one square
    (show
      1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W < 1 by linarith)
  refine ⟨k + 1, by omega, ?_⟩
  calc
    (1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W) ^ (k + 1) ≤
      (1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W) ^ k := by
      rw [pow_succ]
      nlinarith [pow_nonneg continuation k]
    _ ≤ ε ^ 2 := tail.le

theorem
    dSVDensityRationalHeterogeneousPhysicalTerminalMass_le_horizon
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (large : ∀ s, 1 ≤ width s)
    (fine : ∀ s : Fin S,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)))
    {W ε : ℝ} (W_nonnegative : 0 ≤ W)
    (upper : ∀ s, width s ≤ W)
    (tail :
      (1 -
        dSVDensityRationalHeterogeneousPhysicalUniformEscapeRate
          d W) ^ L ≤ ε ^ 2)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousPhysicalTerminalMass
        N width schedule ξ ζ ≤ ε ^ 2 :=
  (dSVDensityRationalHeterogeneousPhysicalTerminalMass_le_pow
    grid dimension width large fine W_nonnegative upper
    schedule ξ ζ).trans tail

end

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

def fairPartitionWeight (α : Type*) [Fintype α] : ℝ :=
  ((2 : ℝ) ^ Fintype.card α)⁻¹

def reversePartitionWeight (s : Finset α) : ℝ :=
  fairPartitionWeight α *
    (2 * (s.card : ℝ) / (Fintype.card α : ℝ))

def forwardMarkedPartitionWeight (α : Type*) [Fintype α] : ℝ :=
  2 * fairPartitionWeight α / (Fintype.card α : ℝ)

def reverseMarkedPartitionWeight (s : Finset α) (i : α) : ℝ :=
  if i ∈ s then reversePartitionWeight s / (s.card : ℝ) else 0

omit [DecidableEq α] in
theorem fairPartitionWeight_pos : 0 < fairPartitionWeight α := by
  unfold fairPartitionWeight
  positivity

omit [DecidableEq α] in
theorem fairPartitionWeight_nonneg : 0 ≤ fairPartitionWeight α :=
  fairPartitionWeight_pos.le

omit [DecidableEq α] in

theorem fairPartitionWeight_sum :
    (∑ _s : Finset α, fairPartitionWeight α) = 1 := by
  simp [fairPartitionWeight, Fintype.card_finset]

omit [DecidableEq α] in

theorem reversePartitionWeight_nonneg (s : Finset α) :
    0 ≤ reversePartitionWeight s := by
  unfold reversePartitionWeight
  exact mul_nonneg fairPartitionWeight_nonneg
    (div_nonneg
      (mul_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le s.card))
      (by exact_mod_cast Nat.zero_le (Fintype.card α)))

omit [DecidableEq α] in

@[simp] theorem reversePartitionWeight_empty :
    reversePartitionWeight (α := α) ∅ = 0 := by
  simp [reversePartitionWeight]

omit [DecidableEq α] in

theorem reversePartitionWeight_pos_iff
    (hα : 0 < Fintype.card α) (s : Finset α) :
    0 < reversePartitionWeight s ↔ s.Nonempty := by
  constructor
  · intro hs
    apply Finset.card_pos.mp
    by_contra hcard
    have hzero : s.card = 0 := Nat.eq_zero_of_not_pos hcard
    simp [reversePartitionWeight, hzero] at hs
  · intro hs
    unfold reversePartitionWeight
    have hcard : 0 < s.card := Finset.card_pos.mpr hs
    exact mul_pos fairPartitionWeight_pos
      (div_pos
        (mul_pos (by norm_num) (by exact_mod_cast hcard))
        (by exact_mod_cast hα))

theorem reverseMarkedPartitionWeight_eq_forward
    {s : Finset α} {i : α} (hi : i ∈ s) :
    reverseMarkedPartitionWeight s i =
      forwardMarkedPartitionWeight α := by
  have hs : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr ⟨i, hi⟩))
  simp only [reverseMarkedPartitionWeight, if_pos hi,
    reversePartitionWeight, forwardMarkedPartitionWeight]
  field_simp

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def rightSpectralBornWeight
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (i : dB) : ℝ :=
  bornTracePairing ρ.matrix F
    (positiveMatrixSpectralAtom G hG i)

theorem rightSpectralBornWeight_nonneg
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (i : dB) :
    0 ≤ rightSpectralBornWeight ρ F G hG i := by
  exact trace_mul_posSemidef_nonneg ρ.positive
    (hF.kronecker (positiveMatrixSpectralAtom_posSemidef G hG i))

theorem rightSpectralBornWeight_sum
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef) :
    (∑ i : dB, rightSpectralBornWeight ρ F G hG i) =
      bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) := by
  unfold rightSpectralBornWeight
  calc
    (∑ i : dB,
      bornTracePairing ρ.matrix F
        (positiveMatrixSpectralAtom G hG i)) =
      bornTracePairing ρ.matrix F
        (∑ i : dB, positiveMatrixSpectralAtom G hG i) := by
          simp [map_sum]
    _ = bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) := by
      rw [positiveMatrixSpectralAtom_sum]

theorem rightSpectralBornWeight_moment
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef) :
    (∑ i : dB,
      rightSpectralBornWeight ρ F G hG i *
        hG.isHermitian.eigenvalues i) =
      bornTracePairing ρ.matrix F G := by
  have hspectral : G =
      ∑ i : dB,
        hG.isHermitian.eigenvalues i •
          positiveMatrixSpectralAtom G hG i := by
    calc
      G = cfc (fun z : ℝ => z) G :=
        (cfc_id' ℝ G hG.isHermitian).symm
      _ = _ := positiveMatrix_cfc_spectral_sum G hG (fun z : ℝ => z)
  have h := congrArg (bornTracePairing ρ.matrix F) hspectral
  simp only [map_sum, map_smul, smul_eq_mul] at h
  calc
    (∑ i : dB,
      rightSpectralBornWeight ρ F G hG i *
        hG.isHermitian.eigenvalues i) =
      ∑ i : dB,
        hG.isHermitian.eigenvalues i *
          bornTracePairing ρ.matrix F
            (positiveMatrixSpectralAtom G hG i) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold rightSpectralBornWeight
        ring
    _ = bornTracePairing ρ.matrix F G := h.symm

theorem rightSpectralBornWeight_entropy
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef) :
    bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) =
      ∑ i : dB,
        rightSpectralBornWeight ρ F G hG i *
          (hG.isHermitian.eigenvalues i *
            Real.log (hG.isHermitian.eigenvalues i)) := by
  have hspectral := positiveMatrix_cfc_spectral_sum G hG
    (fun z : ℝ => z * Real.log z)
  have h := congrArg (bornTracePairing ρ.matrix F) hspectral
  simp only [map_sum, map_smul, smul_eq_mul] at h
  calc
    bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) =
      ∑ i : dB,
        (hG.isHermitian.eigenvalues i *
          Real.log (hG.isHermitian.eigenvalues i)) *
          bornTracePairing ρ.matrix F
            (positiveMatrixSpectralAtom G hG i) := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      unfold rightSpectralBornWeight
      ring

theorem rightSpectralBornWeight_negEntropy
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef) :
    -bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) =
      ∑ i : dB,
        rightSpectralBornWeight ρ F G hG i *
          Real.negMulLog (hG.isHermitian.eigenvalues i) := by
  rw [rightSpectralBornWeight_entropy ρ F G hG,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [Real.negMulLog]

theorem bornTracePairing_le_one_one
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (hFcomplement : (1 - F).PosSemidef) :
    bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) ≤ 1 := by
  have hpositive : 0 ≤ bornTracePairing ρ.matrix
      (1 - F) (1 : Matrix dB dB ℂ) :=
    trace_mul_posSemidef_nonneg ρ.positive
      (hFcomplement.kronecker Matrix.PosSemidef.one)
  have hdiff : bornTracePairing ρ.matrix
      (1 - F) (1 : Matrix dB dB ℂ) =
      bornTracePairing ρ.matrix
        (1 : Matrix dA dA ℂ) (1 : Matrix dB dB ℂ) -
      bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) := by
    simp
  rw [hdiff, bornTracePairing_one_one] at hpositive
  linarith

theorem matrixLogEntropy_born_lower_bound_right
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (hFcomplement : (1 - F).PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (hGcomplement : (1 - G).PosSemidef) :
    -bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) ≤
      Real.negMulLog (bornTracePairing ρ.matrix F G) := by
  classical
  have hp_nonneg : 0 ≤ bornTracePairing ρ.matrix F G :=
    trace_mul_posSemidef_nonneg ρ.positive (hF.kronecker hG)
  have hmass_le :
      bornTracePairing ρ.matrix F G ≤
        bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) := by
    calc
      bornTracePairing ρ.matrix F G =
        ∑ i : dB,
          rightSpectralBornWeight ρ F G hG i *
            hG.isHermitian.eigenvalues i :=
          (rightSpectralBornWeight_moment ρ F G hG).symm
      _ ≤ ∑ i : dB, rightSpectralBornWeight ρ F G hG i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_of_le_one_right
          (rightSpectralBornWeight_nonneg ρ F hF G hG i)
          (positiveContraction_eigenvalue_le_one G hG hGcomplement i)
      _ = bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) :=
        rightSpectralBornWeight_sum ρ F G hG
  by_cases hp : bornTracePairing ρ.matrix F G = 0
  · have hzero :
        (∑ i : dB,
          rightSpectralBornWeight ρ F G hG i *
            hG.isHermitian.eigenvalues i) = 0 := by
        rw [rightSpectralBornWeight_moment, hp]
    have hterm (i : dB) :
        rightSpectralBornWeight ρ F G hG i *
          hG.isHermitian.eigenvalues i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg
          (rightSpectralBornWeight_nonneg ρ F hF G hG j)
          (hG.eigenvalues_nonneg j))).mp hzero i (Finset.mem_univ i)
    have hentropy :
        (∑ i : dB,
          rightSpectralBornWeight ρ F G hG i *
            Real.negMulLog (hG.isHermitian.eigenvalues i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases mul_eq_zero.mp (hterm i) with hw | he
      · simp [hw]
      · simp [he]
    calc
      -bornTracePairing ρ.matrix F
          (cfc (fun z : ℝ => z * Real.log z) G) =
        ∑ i : dB,
          rightSpectralBornWeight ρ F G hG i *
            Real.negMulLog (hG.isHermitian.eigenvalues i) :=
          rightSpectralBornWeight_negEntropy ρ F G hG
      _ = 0 := hentropy
      _ ≤ Real.negMulLog (bornTracePairing ρ.matrix F G) := by
        rw [hp]
        simp
  · have hp_pos : 0 < bornTracePairing ρ.matrix F G :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hp)
    have hW_pos : 0 <
        bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ) :=
      lt_of_lt_of_le hp_pos hmass_le
    have hscalar := finite_weighted_entropy_le_of_weight_bound
      (Finset.univ : Finset dB)
      (rightSpectralBornWeight ρ F G hG)
      hG.isHermitian.eigenvalues
      (W := bornTracePairing ρ.matrix F (1 : Matrix dB dB ℂ))
      (N := (1 : ℝ))
      (p := bornTracePairing ρ.matrix F G)
      (fun i _ => rightSpectralBornWeight_nonneg ρ F hF G hG i)
      (fun i _ => hG.eigenvalues_nonneg i)
      hW_pos hp_pos
      (rightSpectralBornWeight_sum ρ F G hG)
      (rightSpectralBornWeight_moment ρ F G hG)
      (bornTracePairing_le_one_one ρ F hFcomplement)
    calc
      -bornTracePairing ρ.matrix F
          (cfc (fun z : ℝ => z * Real.log z) G) =
        ∑ i : dB,
          rightSpectralBornWeight ρ F G hG i *
            Real.negMulLog (hG.isHermitian.eigenvalues i) :=
        rightSpectralBornWeight_negEntropy ρ F G hG
      _ ≤ bornTracePairing ρ.matrix F G *
          Real.log (1 / bornTracePairing ρ.matrix F G) := hscalar
      _ = Real.negMulLog (bornTracePairing ρ.matrix F G) := by
        rw [one_div, Real.log_inv]
        simp [Real.negMulLog]

section HistoryNormalization

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullSubsetHistoryFieldEquiv
    {n : ℕ} (D L : Finset (Fin n)) :
    FullSubsetHistory X Y n D L ≃
      (({i : Fin n // i ∈ D} → X × Y) ×
       ({i : Fin n // i ∈ L} → X) ×
       ({i : Fin n // i ∈ fullHistoryRemaining n D L} → Y)) where
  toFun h :=
    (fun i => (h.aliceConditioned i, h.bobConditioned i),
      h.aliceRevealed, h.bobRemaining)
  invFun t :=
    ⟨fun i => (t.1 i).1,
      fun i => (t.1 i).2,
      t.2.1, t.2.2⟩
  left_inv h := by
    apply FullSubsetHistory.ext <;> rfl
  right_inv t := by
    rcases t with ⟨q, x, y⟩
    simp

theorem fullHistoryWeight_sum
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) :
    (∑ h : FullSubsetHistory X Y n D L,
      fullHistoryWeight G h) = 1 := by
  classical
  let Dsub := {i : Fin n // i ∈ D}
  let Lsub := {i : Fin n // i ∈ L}
  let Rsub := {i : Fin n // i ∈ fullHistoryRemaining n D L}
  have hD :
      (∑ q : Dsub → X × Y,
        ∏ i : Dsub, G.questionWeight (q i).1 (q i).2) = 1 := by
    calc
      (∑ q : Dsub → X × Y,
        ∏ i : Dsub, G.questionWeight (q i).1 (q i).2) =
        ∏ _i : Dsub, ∑ z : X × Y,
          G.questionWeight z.1 z.2 := by
          exact (Fintype.prod_sum
            (fun _i : Dsub => fun z : X × Y =>
              G.questionWeight z.1 z.2)).symm
      _ = ∏ _i : Dsub, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [Fintype.sum_prod_type]
        exact G.weight_normalized
      _ = 1 := by simp
  have hL :
      (∑ x : Lsub → X,
        ∏ i : Lsub, G.marginalX (x i)) = 1 := by
    calc
      (∑ x : Lsub → X,
        ∏ i : Lsub, G.marginalX (x i)) =
        ∏ _i : Lsub, ∑ z : X, G.marginalX z := by
          exact (Fintype.prod_sum
            (fun _i : Lsub => fun z : X => G.marginalX z)).symm
      _ = 1 := by simp [G.marginalX_normalized]
  have hR :
      (∑ y : Rsub → Y,
        ∏ i : Rsub, G.marginalY (y i)) = 1 := by
    calc
      (∑ y : Rsub → Y,
        ∏ i : Rsub, G.marginalY (y i)) =
        ∏ _i : Rsub, ∑ z : Y, G.marginalY z := by
          exact (Fintype.prod_sum
            (fun _i : Rsub => fun z : Y => G.marginalY z)).symm
      _ = 1 := by simp [G.marginalY_normalized]
  let f : (Dsub → X × Y) × (Lsub → X) × (Rsub → Y) → ℝ :=
    fun t =>
      (∏ i : Dsub, G.questionWeight (t.1 i).1 (t.1 i).2) *
      (∏ i : Lsub, G.marginalX (t.2.1 i)) *
      (∏ i : Rsub, G.marginalY (t.2.2 i))
  calc
    (∑ h : FullSubsetHistory X Y n D L,
      fullHistoryWeight G h) =
      ∑ q : Dsub → X × Y,
      ∑ x : Lsub → X,
      ∑ y : Rsub → Y,
        (∏ i : Dsub, G.questionWeight (q i).1 (q i).2) *
        (∏ i : Lsub, G.marginalX (x i)) *
        (∏ i : Rsub, G.marginalY (y i)) := by
        simpa only [fullHistoryWeight, fullSubsetHistoryFieldEquiv,
          Equiv.coe_fn_mk, Fintype.sum_prod_type,
          f, Dsub, Lsub, Rsub] using
          (fullSubsetHistoryFieldEquiv (X := X) (Y := Y) D L).sum_comp f
    _ =
      (∑ q : Dsub → X × Y,
        ∏ i : Dsub, G.questionWeight (q i).1 (q i).2) *
      (∑ x : Lsub → X,
        ∏ i : Lsub, G.marginalX (x i)) *
      (∑ y : Rsub → Y,
        ∏ i : Rsub, G.marginalY (y i)) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      congr 1
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
    _ = 1 := by rw [hD, hL, hR]; norm_num

theorem fullHistoryWinIndicator_le_one
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) :
    fullHistoryWinIndicator G h α β ≤ 1 := by
  classical
  unfold fullHistoryWinIndicator
  split <;> norm_num

end HistoryNormalization

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullHistoryAnswerCount
    {A B : Type*} [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) : ℝ :=
  (Fintype.card ({i : Fin n // i ∈ D} → A) : ℝ) *
    (Fintype.card ({i : Fin n // i ∈ D} → B) : ℝ)

theorem fullHistoryAnswerCount_eq
    {A B : Type*} [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) :
    fullHistoryAnswerCount (A := A) (B := B) D =
      (Fintype.card A : ℝ) ^ D.card *
        (Fintype.card B : ℝ) ^ D.card := by
  classical
  simp [fullHistoryAnswerCount]

abbrev FullHistoryEntropyAtom
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (n : ℕ) (D L : Finset (Fin n)) :=
  FullSubsetHistory X Y n D L ×
    ({i : Fin n // i ∈ D} → A) ×
    ({i : Fin n // i ∈ D} → B)

def fullHistoryAtomCountingWeight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) : ℝ :=
  fullHistoryWeight G t.1 *
    fullHistoryWinIndicator G t.1 t.2.1 t.2.2

def fullHistoryAtomBornMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) : ℝ :=
  bornTracePairing S.state.matrix
    (fullHistoryAliceFilter G n S D L t.1 t.2.1)
    (fullHistoryBobFilter G n S D L t.1 t.2.2)

theorem fullHistoryAtomCountingWeight_nonneg
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) :
    0 ≤ fullHistoryAtomCountingWeight G D L t := by
  exact mul_nonneg (fullHistoryWeight_nonneg G t.1)
    (fullHistoryWinIndicator_nonneg G t.1 t.2.1 t.2.2)

theorem fullHistoryAtomBornMass_nonneg
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) :
    0 ≤ fullHistoryAtomBornMass G n S D L t := by
  exact trace_mul_posSemidef_nonneg S.state.positive
    ((fullHistoryAliceFilter_posSemidef G n S D L t.1 t.2.1).kronecker
      (fullHistoryBobFilter_posSemidef G n S D L t.1 t.2.2))

theorem bornTracePairing_contractions_le_one
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (hFcomplement : (1 - F).PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (hGcomplement : (1 - G).PosSemidef) :
    bornTracePairing ρ.matrix F G ≤ 1 := by
  have hpositive : 0 ≤
      bornTracePairing ρ.matrix (1 - F) G :=
    trace_mul_posSemidef_nonneg ρ.positive
      (hFcomplement.kronecker hG)
  have hdiff : bornTracePairing ρ.matrix (1 - F) G =
      bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G -
        bornTracePairing ρ.matrix F G := by
    simp
  rw [hdiff] at hpositive
  have hone := bornTracePairing_one_le_one ρ G hGcomplement
  linarith

theorem fullHistoryAtomBornMass_le_one
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (t : FullHistoryEntropyAtom X Y A B n D L) :
    fullHistoryAtomBornMass G n S D L t ≤ 1 := by
  exact bornTracePairing_contractions_le_one S.state
    (fullHistoryAliceFilter G n S D L t.1 t.2.1)
    (fullHistoryAliceFilter_complement_posSemidef G n S D L t.1 t.2.1)
    (fullHistoryBobFilter G n S D L t.1 t.2.2)
    (fullHistoryBobFilter_posSemidef G n S D L t.1 t.2.2)
    (fullHistoryBobFilter_complement_posSemidef G n S D L t.1 t.2.2)

theorem fullHistoryAtomCountingWeight_sum_le
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) :
    (∑ t : FullHistoryEntropyAtom X Y A B n D L,
      fullHistoryAtomCountingWeight G D L t) ≤
      fullHistoryAnswerCount (A := A) (B := B) D := by
  classical
  calc
    (∑ t : FullHistoryEntropyAtom X Y A B n D L,
      fullHistoryAtomCountingWeight G D L t) =
      ∑ h : FullSubsetHistory X Y n D L,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β := by
        simp [fullHistoryAtomCountingWeight, Fintype.sum_prod_type]
    _ ≤ ∑ h : FullSubsetHistory X Y n D L,
        ∑ _α : {i : Fin n // i ∈ D} → A,
        ∑ _β : {i : Fin n // i ∈ D} → B,
          fullHistoryWeight G h := by
      apply Finset.sum_le_sum
      intro h _
      apply Finset.sum_le_sum
      intro α _
      apply Finset.sum_le_sum
      intro β _
      exact mul_le_of_le_one_right
        (fullHistoryWeight_nonneg G h)
        (fullHistoryWinIndicator_le_one G h α β)
    _ = fullHistoryAnswerCount (A := A) (B := B) D *
        (∑ h : FullSubsetHistory X Y n D L,
          fullHistoryWeight G h) := by
      simp [fullHistoryAnswerCount, Finset.mul_sum,
        mul_assoc]
    _ = fullHistoryAnswerCount (A := A) (B := B) D := by
      rw [fullHistoryWeight_sum G D L]
      ring

theorem fullHistoryAtomBornMass_sum
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D) :
    (∑ t : FullHistoryEntropyAtom X Y A B n D L,
      fullHistoryAtomCountingWeight G D L t *
        fullHistoryAtomBornMass G n S D L t) =
      (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) := by
  classical
  simpa [fullHistoryAtomCountingWeight, fullHistoryAtomBornMass,
    Fintype.sum_prod_type] using
    fullSubsetHistory_mass_eq_postselection G n S D L hL

theorem fullHistoryAtomEntropy_le
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D)
    (hp : 0 < (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) :
    (∑ t : FullHistoryEntropyAtom X Y A B n D L,
      fullHistoryAtomCountingWeight G D L t *
        Real.negMulLog (fullHistoryAtomBornMass G n S D L t)) ≤
      (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) *
        Real.log
          (fullHistoryAnswerCount (A := A) (B := B) D /
            (strategyEventLaw (G.repeat n) S).eventMass
              (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) := by
  classical
  let p := (strategyEventLaw (G.repeat n) S).eventMass
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
  let w := fullHistoryAtomCountingWeight G D L
  let q := fullHistoryAtomBornMass G n S D L
  let W : ℝ := ∑ t : FullHistoryEntropyAtom X Y A B n D L, w t
  have hmass :
      (∑ t : FullHistoryEntropyAtom X Y A B n D L,
        w t * q t) = p :=
    fullHistoryAtomBornMass_sum G n S D L hL
  have hpW : p ≤ W := by
    calc
      p = ∑ t : FullHistoryEntropyAtom X Y A B n D L,
          w t * q t := hmass.symm
      _ ≤ ∑ t : FullHistoryEntropyAtom X Y A B n D L,
          w t := by
        apply Finset.sum_le_sum
        intro t _
        exact mul_le_of_le_one_right
          (fullHistoryAtomCountingWeight_nonneg G D L t)
          (fullHistoryAtomBornMass_le_one G n S D L t)
      _ = W := rfl
  have hW : 0 < W := lt_of_lt_of_le hp hpW
  have hbound : W ≤ fullHistoryAnswerCount (A := A) (B := B) D :=
    fullHistoryAtomCountingWeight_sum_le G D L
  exact finite_weighted_entropy_le_of_weight_bound
    (Finset.univ : Finset (FullHistoryEntropyAtom X Y A B n D L))
    w q
    (fun t _ => fullHistoryAtomCountingWeight_nonneg G D L t)
    (fun t _ => fullHistoryAtomBornMass_nonneg G n S D L t)
    hW hp rfl hmass hbound

theorem fullHistoryAliceEntropyPotential_lower_bound
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D)
    (hp : 0 < (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) :
    -((strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) *
      Real.log
        (fullHistoryAnswerCount (A := A) (B := B) D /
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D))) ≤
      fullHistoryAliceEntropyPotential G n S D L := by
  classical
  have hpoint :
      -fullHistoryAliceEntropyPotential G n S D L ≤
        ∑ t : FullHistoryEntropyAtom X Y A B n D L,
          fullHistoryAtomCountingWeight G D L t *
            Real.negMulLog (fullHistoryAtomBornMass G n S D L t) := by
    simp only [fullHistoryAliceEntropyPotential,
      fullHistoryAtomCountingWeight, fullHistoryAtomBornMass,
      Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro h _
    apply Finset.sum_le_sum
    intro α _
    apply Finset.sum_le_sum
    intro β _
    have hw := mul_nonneg (fullHistoryWeight_nonneg G h)
      (fullHistoryWinIndicator_nonneg G h α β)
    have hlocal := matrixLogEntropy_born_lower_bound_left S.state
      (fullHistoryAliceFilter G n S D L h α)
      (fullHistoryAliceFilter_posSemidef G n S D L h α)
      (fullHistoryAliceFilter_complement_posSemidef G n S D L h α)
      (fullHistoryBobFilter G n S D L h β)
      (fullHistoryBobFilter_posSemidef G n S D L h β)
      (fullHistoryBobFilter_complement_posSemidef G n S D L h β)
    nlinarith [mul_le_mul_of_nonneg_left hlocal hw]
  have hscalar := fullHistoryAtomEntropy_le G n S D L hL hp
  linarith

end

noncomputable section

open scoped BigOperators

@[ext (iff := false)] structure FullCoordinateRevealHistory
    (X Y : Type*) [Fintype X] [Fintype Y]
    (n : ℕ) (D L : Finset (Fin n)) (i : Fin n) where
  aliceConditioned : {j : Fin n // j ∈ D} → X
  bobConditioned : {j : Fin n // j ∈ D} → Y
  aliceRevealed : {j : Fin n // j ∈ L} → X
  bobRemaining :
    {j : Fin n // j ∈ fullHistoryRemaining n D (insert i L)} → Y
  deriving Fintype

theorem fullHistoryRemaining_insert_subset
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n) :
    fullHistoryRemaining n D (insert i L) ⊆
      fullHistoryRemaining n D L := by
  intro j hj
  simp only [fullHistoryRemaining, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_insert] at hj ⊢
  exact ⟨hj.1, fun h => hj.2 (Or.inr h)⟩

def fullCoordinateBaseOfOldHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullSubsetHistory X Y n D L) :
    FullCoordinateRevealHistory X Y n D L i where
  aliceConditioned := h.aliceConditioned
  bobConditioned := h.bobConditioned
  aliceRevealed := h.aliceRevealed
  bobRemaining := fun j => h.bobRemaining
    ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩

def fullCoordinateOldHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i)
    (y : Y) : FullSubsetHistory X Y n D L := by
  classical
  refine ⟨h.aliceConditioned, h.bobConditioned, h.aliceRevealed,
    fun j => if hj : (j : Fin n) = i then y else
      h.bobRemaining ⟨j, ?_⟩⟩
  have hjD : (j : Fin n) ∉ D :=
    (Finset.mem_sdiff.mp
      (Finset.mem_sdiff.mp j.property).1).2
  have hjL : (j : Fin n) ∉ L :=
    (Finset.mem_sdiff.mp j.property).2
  simp [fullHistoryRemaining, hjD, hjL, hj]

def fullCoordinateBaseOfNewHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullSubsetHistory X Y n D (insert i L)) :
    FullCoordinateRevealHistory X Y n D L i where
  aliceConditioned := h.aliceConditioned
  bobConditioned := h.bobConditioned
  aliceRevealed := fun j => h.aliceRevealed
    ⟨j, Finset.mem_insert_of_mem j.property⟩
  bobRemaining := h.bobRemaining

def fullCoordinateNewHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i)
    (x : X) : FullSubsetHistory X Y n D (insert i L) := by
  classical
  refine ⟨h.aliceConditioned, h.bobConditioned,
    fun j => if hj : (j : Fin n) = i then x else
      h.aliceRevealed ⟨j, ?_⟩,
    h.bobRemaining⟩
  exact (Finset.mem_insert.mp j.property).resolve_left hj

def fullCoordinateOldHistoryEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    FullSubsetHistory X Y n D L ≃
      FullCoordinateRevealHistory X Y n D L i × Y where
  toFun h :=
    (fullCoordinateBaseOfOldHistory D L i h,
      h.bobRemaining
        ⟨i, by simp [fullHistoryRemaining, hiD, hiL]⟩)
  invFun t := fullCoordinateOldHistory D L i t.1 t.2
  left_inv h := by
    apply FullSubsetHistory.ext
    · rfl
    · rfl
    · rfl
    · funext j
      by_cases hj : (j : Fin n) = i
      · subst i
        simp [fullCoordinateOldHistory,
          fullCoordinateBaseOfOldHistory]
      · simp [fullCoordinateOldHistory,
          fullCoordinateBaseOfOldHistory, hj]
  right_inv t := by
    rcases t with ⟨h, y⟩
    apply Prod.ext
    · apply FullCoordinateRevealHistory.ext
      · rfl
      · rfl
      · rfl
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          have hnot : (j : Fin n) ∉ insert i L :=
            (Finset.mem_sdiff.mp j.property).2
          apply hnot
          simp [he]
        simp [fullCoordinateBaseOfOldHistory,
          fullCoordinateOldHistory, hj]
    · simp [fullCoordinateOldHistory]

def fullCoordinateNewHistoryEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiL : i ∉ L) :
    FullSubsetHistory X Y n D (insert i L) ≃
      FullCoordinateRevealHistory X Y n D L i × X where
  toFun h :=
    (fullCoordinateBaseOfNewHistory D L i h,
      h.aliceRevealed ⟨i, Finset.mem_insert_self i L⟩)
  invFun t := fullCoordinateNewHistory D L i t.1 t.2
  left_inv h := by
    apply FullSubsetHistory.ext
    · rfl
    · rfl
    · funext j
      by_cases hj : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i L⟩ :
              {j : Fin n // j ∈ insert i L}) :=
          Subtype.ext hj
        subst j
        simp [fullCoordinateNewHistory,
          fullCoordinateBaseOfNewHistory]
      · simp [fullCoordinateNewHistory,
          fullCoordinateBaseOfNewHistory, hj]
    · rfl
  right_inv t := by
    rcases t with ⟨h, x⟩
    apply Prod.ext
    · apply FullCoordinateRevealHistory.ext
      · rfl
      · rfl
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          exact hiL (he ▸ j.property)
        simp [fullCoordinateBaseOfNewHistory,
          fullCoordinateNewHistory, hj]
      · rfl
    · simp [fullCoordinateNewHistory]

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem finsetSubtype_prod_insert
    {ι T : Type*} [DecidableEq ι] [CommMonoid T]
    (s : Finset ι) (i : ι) (hi : i ∉ s)
    (f : {j : ι // j ∈ insert i s} → T) :
    (∏ j : {j : ι // j ∈ insert i s}, f j) =
      f ⟨i, Finset.mem_insert_self i s⟩ *
        ∏ j : {j : ι // j ∈ s},
          f ⟨j, Finset.mem_insert_of_mem j.property⟩ := by
  classical
  let e := Finset.subtypeInsertEquivOption hi
  let g : Option {j : ι // j ∈ s} → T
    | none => f ⟨i, Finset.mem_insert_self i s⟩
    | some j => f ⟨j, Finset.mem_insert_of_mem j.property⟩
  have hcomp (j : {j : ι // j ∈ insert i s}) :
      g (e j) = f j := by
    rcases j with ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      simp [e, g, Finset.subtypeInsertEquivOption]
    · simp [e, g, Finset.subtypeInsertEquivOption, hji]
  calc
    (∏ j : {j : ι // j ∈ insert i s}, f j) =
      ∏ j : {j : ι // j ∈ insert i s}, g (e j) := by
        apply Finset.prod_congr rfl
        intro j _
        exact (hcomp j).symm
    _ = ∏ j : Option {j : ι // j ∈ s}, g j := e.prod_comp g
    _ = g none * ∏ j : {j : ι // j ∈ s}, g (some j) :=
      Fintype.prod_option g
    _ = _ := rfl

def fullHistoryRemainingCoordinateEquiv
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    {j : Fin n // j ∈ fullHistoryRemaining n D L} ≃
      Option {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} where
  toFun j :=
    if hj : (j : Fin n) = i then none
    else some ⟨j, by
      have hjD : (j : Fin n) ∉ D :=
        (Finset.mem_sdiff.mp
          (Finset.mem_sdiff.mp j.property).1).2
      have hjL : (j : Fin n) ∉ L :=
        (Finset.mem_sdiff.mp j.property).2
      simp [fullHistoryRemaining, hjD, hjL, hj]⟩
  invFun
    | none => ⟨i, by simp [fullHistoryRemaining, hiD, hiL]⟩
    | some j =>
      ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩
  left_inv j := by
    apply Subtype.ext
    by_cases hj : (j : Fin n) = i
    · simp [hj]
    · simp [hj]
  right_inv j := by
    cases j with
    | none => simp
    | some j =>
      have hj : (j : Fin n) ≠ i := by
        intro he
        have hnot : (j : Fin n) ∉ insert i L :=
          (Finset.mem_sdiff.mp j.property).2
        apply hnot
        simp [he]
      simp [hj]

theorem fullHistoryRemaining_prod_split
    {n : ℕ} {T : Type*} [CommMonoid T]
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (f : {j : Fin n // j ∈ fullHistoryRemaining n D L} → T) :
    (∏ j : {j : Fin n // j ∈ fullHistoryRemaining n D L}, f j) =
      f ⟨i, by simp [fullHistoryRemaining, hiD, hiL]⟩ *
        ∏ j : {j : Fin n //
          j ∈ fullHistoryRemaining n D (insert i L)},
          f ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩ := by
  classical
  let e := fullHistoryRemainingCoordinateEquiv D L i hiD hiL
  let g : Option {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → T
    | none => f ⟨i, by simp [fullHistoryRemaining, hiD, hiL]⟩
    | some j =>
      f ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩
  have hcomp (j : {j : Fin n //
      j ∈ fullHistoryRemaining n D L}) :
      g (e j) = f j := by
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, by simp [fullHistoryRemaining, hiD, hiL]⟩ :
            {j : Fin n // j ∈ fullHistoryRemaining n D L}) :=
        Subtype.ext hj
      subst j
      simp [e, g, fullHistoryRemainingCoordinateEquiv]
    · simp [e, g, fullHistoryRemainingCoordinateEquiv, hj]
  calc
    (∏ j : {j : Fin n // j ∈ fullHistoryRemaining n D L}, f j) =
      ∏ j : {j : Fin n // j ∈ fullHistoryRemaining n D L},
        g (e j) := by
          apply Finset.prod_congr rfl
          intro j _
          exact (hcomp j).symm
    _ = ∏ j : Option {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)}, g j :=
      e.prod_comp g
    _ = g none * ∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)}, g (some j) :=
      Fintype.prod_option g
    _ = _ := rfl

section CoordinateWeights

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullCoordinateBaseWeight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i) : ℝ :=
  (∏ j : {j : Fin n // j ∈ D},
    G.questionWeight (h.aliceConditioned j) (h.bobConditioned j)) *
  (∏ j : {j : Fin n // j ∈ L},
    G.marginalX (h.aliceRevealed j)) *
  (∏ j : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)},
    G.marginalY (h.bobRemaining j))

theorem fullCoordinateBaseWeight_nonneg
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i) :
    0 ≤ fullCoordinateBaseWeight G D L i h := by
  unfold fullCoordinateBaseWeight
  exact mul_nonneg
    (mul_nonneg
      (Finset.prod_nonneg fun j _ =>
        G.weight_nonneg (h.aliceConditioned j) (h.bobConditioned j))
      (Finset.prod_nonneg fun j _ =>
        G.marginalX_nonneg (h.aliceRevealed j)))
    (Finset.prod_nonneg fun j _ => G.marginalY_nonneg (h.bobRemaining j))

theorem fullCoordinateOldHistory_weight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (h : FullCoordinateRevealHistory X Y n D L i) (y : Y) :
    fullHistoryWeight G (fullCoordinateOldHistory D L i h y) =
      fullCoordinateBaseWeight G D L i h * G.marginalY y := by
  classical
  have hold (j : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)}) :
      (fullCoordinateOldHistory D L i h y).bobRemaining
        ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩ =
      h.bobRemaining j := by
    have hj : (j : Fin n) ≠ i := by
      intro he
      have hnot : (j : Fin n) ∉ insert i L :=
        (Finset.mem_sdiff.mp j.property).2
      apply hnot
      simp [he]
    simp [fullCoordinateOldHistory, hj]
  unfold fullHistoryWeight fullCoordinateBaseWeight
  change
    (∏ j : {j : Fin n // j ∈ D},
      G.questionWeight (h.aliceConditioned j) (h.bobConditioned j)) *
    (∏ j : {j : Fin n // j ∈ L},
      G.marginalX (h.aliceRevealed j)) *
    (∏ j : {j : Fin n // j ∈ fullHistoryRemaining n D L},
      G.marginalY
        ((fullCoordinateOldHistory D L i h y).bobRemaining j)) = _
  rw [fullHistoryRemaining_prod_split D L i hiD hiL]
  simp_rw [hold]
  simp [fullCoordinateOldHistory]
  ring

theorem fullCoordinateNewHistory_weight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiL : i ∉ L)
    (h : FullCoordinateRevealHistory X Y n D L i) (x : X) :
    fullHistoryWeight G (fullCoordinateNewHistory D L i h x) =
      fullCoordinateBaseWeight G D L i h * G.marginalX x := by
  classical
  have hnew (j : {j : Fin n // j ∈ L}) :
      (fullCoordinateNewHistory D L i h x).aliceRevealed
        ⟨j, Finset.mem_insert_of_mem j.property⟩ =
      h.aliceRevealed j := by
    have hj : (j : Fin n) ≠ i := by
      intro he
      exact hiL (he ▸ j.property)
    simp [fullCoordinateNewHistory, hj]
  unfold fullHistoryWeight fullCoordinateBaseWeight
  change
    (∏ j : {j : Fin n // j ∈ D},
      G.questionWeight (h.aliceConditioned j) (h.bobConditioned j)) *
    (∏ j : {j : Fin n // j ∈ insert i L},
      G.marginalX
        ((fullCoordinateNewHistory D L i h x).aliceRevealed j)) *
    (∏ j : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)},
      G.marginalY (h.bobRemaining j)) = _
  rw [finsetSubtype_prod_insert L i hiL]
  simp_rw [hnew]
  simp [fullCoordinateNewHistory]
  ring

end CoordinateWeights

end

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem finitePurificationMatrix_pair_difference_gram_apply
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a b : ι) (i j : d) :
    ((finitePurificationMatrix F M positive hM a -
          finitePurificationMatrix F M positive hM b).conjTranspose *
        (finitePurificationMatrix F M positive hM a -
          finitePurificationMatrix F M positive hM b)) i j =
      ∑ r : d,
        inner ℂ
          (ensemblePurificationSubspaceEntry F M positive hM a r i -
            ensemblePurificationSubspaceEntry F M positive hM b r i)
          (ensemblePurificationSubspaceEntry F M positive hM a r j -
            ensemblePurificationSubspaceEntry F M positive hM b r j) := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sub_apply, finitePurificationMatrix, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  let basis := commonPurificationOrthonormalBasis F M positive hM
  let u := ensemblePurificationSubspaceEntry F M positive hM a r i
  let u₀ := ensemblePurificationSubspaceEntry F M positive hM b r i
  let v := ensemblePurificationSubspaceEntry F M positive hM a r j
  let v₀ := ensemblePurificationSubspaceEntry F M positive hM b r j
  have hisometry := basis.repr.inner_map_map (u - u₀) (v - v₀)
  change
    (∑ k, star (basis.repr u k - basis.repr u₀ k) *
      (basis.repr v k - basis.repr v₀ k)) =
      inner ℂ (u - u₀) (v - v₀)
  rw [← hisometry, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, map_sub, mul_comm]

theorem ensemblePurificationSubspaceEntry_pair_difference_inner_eq_integral
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a b : ι) (r i j : d) :
    inner ℂ
      (ensemblePurificationSubspaceEntry F M positive hM a r i -
        ensemblePurificationSubspaceEntry F M positive hM b r i)
      (ensemblePurificationSubspaceEntry F M positive hM a r j -
        ensemblePurificationSubspaceEntry F M positive hM b r j) =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s r i -
          spectralPurificationFilter (F b) (positive b) s r i) *
        (spectralPurificationFilter (F a) (positive a) s r j -
          spectralPurificationFilter (F b) (positive b) s r j) := by
  rw [Submodule.coe_inner, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  let fi := spectralPurificationFilterEntryLp
    (F a) (positive a) r i
  let gi := spectralPurificationFilterEntryLp
    (F b) (positive b) r i
  let fj := spectralPurificationFilterEntryLp
    (F a) (positive a) r j
  let gj := spectralPurificationFilterEntryLp
    (F b) (positive b) r j
  have hsubi := Lp.coeFn_sub fi gi
  have hsubj := Lp.coeFn_sub fj gj
  have hfi := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r i
  have hgi := spectralPurificationFilterEntryLp_coeFn
    (F b) (positive b) r i
  have hfj := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r j
  have hgj := spectralPurificationFilterEntryLp_coeFn
    (F b) (positive b) r j
  filter_upwards [hsubi, hsubj, hfi, hgi, hfj, hgj]
    with s hi hj hfi' hgi' hfj' hgj'
  change inner ℂ ((fi - gi) s) ((fj - gj) s) = _
  rw [hi, hj]
  change inner ℂ (fi s - gi s) (fj s - gj s) = _
  change
    inner ℂ
      ((spectralPurificationFilterEntryLp
        (F a) (positive a) r i : ℝ → ℂ) s -
        (spectralPurificationFilterEntryLp
          (F b) (positive b) r i : ℝ → ℂ) s)
      ((spectralPurificationFilterEntryLp
        (F a) (positive a) r j : ℝ → ℂ) s -
        (spectralPurificationFilterEntryLp
          (F b) (positive b) r j : ℝ → ℂ) s) = _
  rw [hfi', hgi', hfj', hgj']
  simp [RCLike.inner_apply, mul_comm]

theorem finitePurificationMatrix_pair_difference_gram_eq_integral
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a b : ι) :
    (finitePurificationMatrix F M positive hM a -
        finitePurificationMatrix F M positive hM b).conjTranspose *
      (finitePurificationMatrix F M positive hM a -
        finitePurificationMatrix F M positive hM b) =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter (F b) (positive b) s) *
        (spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter (F b) (positive b) s) := by
  classical
  have hdelta :
      MemLp (fun s : ℝ =>
        spectralPurificationFilter (F a) (positive a) s -
          spectralPurificationFilter (F b) (positive b) s)
        2 (volume.restrict (Ioi 0)) :=
    (spectralPurificationFilter_memLp_two (F a) (positive a)).sub
      (spectralPurificationFilter_memLp_two (F b) (positive b))
  have hmatrix := spectralPurificationFilter_difference_gram_integrable
    (F a) (F b) (positive a) (positive b)
  have hrows :
      ∀ i : d,
        Integrable
          (fun s : ℝ =>
            (star (spectralPurificationFilter (F a) (positive a) s -
                spectralPurificationFilter (F b) (positive b) s) *
              (spectralPurificationFilter (F a) (positive a) s -
                spectralPurificationFilter (F b) (positive b) s)) i)
          (volume.restrict (Ioi 0)) :=
    fun i => hmatrix.eval i
  ext i j
  rw [finitePurificationMatrix_pair_difference_gram_apply]
  rw [MeasureTheory.eval_integral hrows i,
    MeasureTheory.eval_integral (fun k => (hrows i).eval k) j]
  simp_rw [ensemblePurificationSubspaceEntry_pair_difference_inner_eq_integral]
  have hproduct (r : d) :
      Integrable
        (fun s : ℝ =>
          star (spectralPurificationFilter (F a) (positive a) s r i -
            spectralPurificationFilter (F b) (positive b) s r i) *
          (spectralPurificationFilter (F a) (positive a) s r j -
            spectralPurificationFilter (F b) (positive b) s r j))
        (volume.restrict (Ioi 0)) :=
    (((hdelta.eval r).eval i).star).integrable_mul
      ((hdelta.eval r).eval j)
  rw [← integral_finsetSum Finset.univ (fun r _ => hproduct r)]
  apply integral_congr_ae
  filter_upwards with s
  simp [Matrix.mul_apply, Matrix.star_apply]

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem finiteLocalPurificationVector_sub_left
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA KA' : Matrix eA S.Alice ℂ)
    (KB : Matrix eB S.Bob ℂ) :
    finiteLocalPurificationVector S KA KB -
        finiteLocalPurificationVector S KA' KB =
      finiteLocalPurificationVector S (KA - KA') KB := by
  have hmatrix :
      finiteLocalPurificationJointMatrix S KA KB -
        finiteLocalPurificationJointMatrix S KA' KB =
      finiteLocalPurificationJointMatrix S (KA - KA') KB := by
    ext ⟨⟨a, k⟩, b⟩ ⟨⟨a', k'⟩, b'⟩
    simp [finiteLocalPurificationJointMatrix,
      Matrix.kroneckerMap_apply, sub_mul]
  unfold finiteLocalPurificationVector
  rw [← WithLp.toLp_sub, ← Matrix.sub_mulVec, hmatrix]

theorem finiteLocalPurificationVector_sub_right
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ)
    (KB KB' : Matrix eB S.Bob ℂ) :
    finiteLocalPurificationVector S KA KB -
        finiteLocalPurificationVector S KA KB' =
      finiteLocalPurificationVector S KA (KB - KB') := by
  have hmatrix :
      finiteLocalPurificationJointMatrix S KA KB -
        finiteLocalPurificationJointMatrix S KA KB' =
      finiteLocalPurificationJointMatrix S KA (KB - KB') := by
    ext ⟨⟨a, k⟩, b⟩ ⟨⟨a', k'⟩, b'⟩
    simp [finiteLocalPurificationJointMatrix,
      Matrix.kroneckerMap_apply, mul_sub]
  unfold finiteLocalPurificationVector
  rw [← WithLp.toLp_sub, ← Matrix.sub_mulVec, hmatrix]

theorem finiteLocalPurificationVector_sub_left_norm_sq
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA KA' : Matrix eA S.Alice ℂ)
    (KB : Matrix eB S.Bob ℂ) :
    ‖finiteLocalPurificationVector S KA KB -
        finiteLocalPurificationVector S KA' KB‖ ^ 2 =
      bornTracePairing S.state.matrix
        ((KA - KA').conjTranspose * (KA - KA'))
        (KB.conjTranspose * KB) := by
  rw [finiteLocalPurificationVector_sub_left,
    finiteLocalPurificationVector_norm_sq]
  rfl

theorem finiteLocalPurificationVector_sub_right_norm_sq
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ)
    (KB KB' : Matrix eB S.Bob ℂ) :
    ‖finiteLocalPurificationVector S KA KB -
        finiteLocalPurificationVector S KA KB'‖ ^ 2 =
      bornTracePairing S.state.matrix
        (KA.conjTranspose * KA)
        ((KB - KB').conjTranspose * (KB - KB')) := by
  rw [finiteLocalPurificationVector_sub_right,
    finiteLocalPurificationVector_norm_sq]
  rfl

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullCoordinateAliceQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A) (x : X) :
    Matrix S.Alice S.Alice ℂ :=
  fullHistoryAliceFilter G n S D (insert i L)
    (fullCoordinateNewHistory D L i r x) α

def fullCoordinateAliceMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A) (y : Y) :
    Matrix S.Alice S.Alice ℂ :=
  fullHistoryAliceFilter G n S D L
    (fullCoordinateOldHistory D L i r y) α

def fullCoordinateBobQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B) (y : Y) :
    Matrix S.Bob S.Bob ℂ :=
  fullHistoryBobFilter G n S D L
    (fullCoordinateOldHistory D L i r y) β

def fullCoordinateBobMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B) (x : X) :
    Matrix S.Bob S.Bob ℂ :=
  fullHistoryBobFilter G n S D (insert i L)
    (fullCoordinateNewHistory D L i r x) β

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def fullCoordinateAssembleHiddenAlice
    {X : Type*} {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (x : X)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    {j : Fin n // j ∈ fullHistoryRemaining n D L} → X := by
  classical
  intro j
  by_cases hj : (j : Fin n) = i
  · exact x
  · exact hidden ⟨j, by
      have hjD : (j : Fin n) ∉ D :=
        (Finset.mem_sdiff.mp
          (Finset.mem_sdiff.mp j.property).1).2
      have hjL : (j : Fin n) ∉ L :=
        (Finset.mem_sdiff.mp j.property).2
      simp [fullHistoryRemaining, hjD, hjL, hj]⟩

def fullCoordinateHiddenAliceEquiv
    {X : Type*} [Fintype X] {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    ({j : Fin n // j ∈ fullHistoryRemaining n D L} → X) ≃
      X × ({j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} → X) where
  toFun hidden :=
    (hidden ⟨i, by simp [fullHistoryRemaining, hiD, hiL]⟩,
      fun j => hidden
        ⟨j, fullHistoryRemaining_insert_subset D L i j.property⟩)
  invFun t := fullCoordinateAssembleHiddenAlice D L i t.1 t.2
  left_inv hidden := by
    funext j
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, by simp [fullHistoryRemaining, hiD, hiL]⟩ :
            {j : Fin n // j ∈ fullHistoryRemaining n D L}) :=
        Subtype.ext hj
      subst j
      simp [fullCoordinateAssembleHiddenAlice]
    · simp [fullCoordinateAssembleHiddenAlice, hj]
  right_inv t := by
    rcases t with ⟨x, hidden⟩
    apply Prod.ext
    · simp [fullCoordinateAssembleHiddenAlice]
    · funext j
      have hj : (j : Fin n) ≠ i := by
        intro he
        have hnot : (j : Fin n) ∉ insert i L :=
          (Finset.mem_sdiff.mp j.property).2
        apply hnot
        simp [he]
      simp [fullCoordinateAssembleHiddenAlice, hj]

def fullCoordinateAssembleHiddenBob
    {Y : Type*} {n : ℕ}
    (L : Finset (Fin n)) (i : Fin n)
    (y : Y) (hidden : {j : Fin n // j ∈ L} → Y) :
    {j : Fin n // j ∈ insert i L} → Y := by
  classical
  intro j
  by_cases hj : (j : Fin n) = i
  · exact y
  · exact hidden
      ⟨j, (Finset.mem_insert.mp j.property).resolve_left hj⟩

def fullCoordinateHiddenBobEquiv
    {Y : Type*} [Fintype Y] {n : ℕ}
    (L : Finset (Fin n)) (i : Fin n) (hiL : i ∉ L) :
    ({j : Fin n // j ∈ insert i L} → Y) ≃
      Y × ({j : Fin n // j ∈ L} → Y) where
  toFun hidden :=
    (hidden ⟨i, Finset.mem_insert_self i L⟩,
      fun j => hidden ⟨j, Finset.mem_insert_of_mem j.property⟩)
  invFun t := fullCoordinateAssembleHiddenBob L i t.1 t.2
  left_inv hidden := by
    funext j
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, Finset.mem_insert_self i L⟩ :
            {j : Fin n // j ∈ insert i L}) :=
        Subtype.ext hj
      subst j
      simp [fullCoordinateAssembleHiddenBob]
    · simp [fullCoordinateAssembleHiddenBob, hj]
  right_inv t := by
    rcases t with ⟨y, hidden⟩
    apply Prod.ext
    · simp [fullCoordinateAssembleHiddenBob]
    · funext j
      have hj : (j : Fin n) ≠ i := by
        intro he
        exact hiL (he ▸ j.property)
      simp [fullCoordinateAssembleHiddenBob, hj]

section CoordinateFilters

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem fullCoordinateAliceQuestion_eq
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    fullHistoryAliceQuestion
        (fullCoordinateOldHistory D L i r y)
        (fullCoordinateAssembleHiddenAlice D L i x hidden) =
      fullHistoryAliceQuestion
        (fullCoordinateNewHistory D L i r x) hidden := by
  classical
  funext j
  by_cases hjD : j ∈ D
  · simp [fullHistoryAliceQuestion, fullCoordinateOldHistory,
      fullCoordinateNewHistory, hjD]
  · by_cases hjL : j ∈ L
    · have hji : j ≠ i := by
        intro he
        exact hiL (he ▸ hjL)
      simp [fullHistoryAliceQuestion, fullCoordinateOldHistory,
        fullCoordinateNewHistory, hjD, hjL, hji]
    · by_cases hji : j = i
      · subst j
        simp [fullHistoryAliceQuestion,
          fullCoordinateAssembleHiddenAlice,
          fullCoordinateNewHistory,
          hiD, hiL]
      · simp [fullHistoryAliceQuestion,
          fullCoordinateAssembleHiddenAlice,
                    hjD, hjL, hji]

theorem fullCoordinateBobQuestion_eq
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n // j ∈ L} → Y) :
    fullHistoryBobQuestion
        (fullCoordinateNewHistory D L i r x)
        (fullCoordinateAssembleHiddenBob L i y hidden) =
      fullHistoryBobQuestion
        (fullCoordinateOldHistory D L i r y) hidden := by
  classical
  funext j
  by_cases hjD : j ∈ D
  · simp [fullHistoryBobQuestion, fullCoordinateOldHistory,
      fullCoordinateNewHistory, hjD]
  · by_cases hjL : j ∈ L
    · have hji : j ≠ i := by
        intro he
        exact hiL (he ▸ hjL)
      simp [fullHistoryBobQuestion,
        fullCoordinateAssembleHiddenBob,
                hjD, hjL, hji]
    · by_cases hji : j = i
      · subst j
        simp [fullHistoryBobQuestion,
          fullCoordinateAssembleHiddenBob,
          fullCoordinateOldHistory,           hiD, hiL]
      · simp [fullHistoryBobQuestion,
                    fullCoordinateOldHistory, fullCoordinateNewHistory,
          hjD, hjL, hji]

theorem fullCoordinateHiddenAliceWeight_split
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    fullHistoryHiddenAliceWeight G
        (fullCoordinateOldHistory D L i r y)
        (fullCoordinateAssembleHiddenAlice D L i x hidden) =
      G.conditionalXGivenY y x *
        fullHistoryHiddenAliceWeight G
          (fullCoordinateNewHistory D L i r x) hidden := by
  classical
  unfold fullHistoryHiddenAliceWeight
  rw [fullHistoryRemaining_prod_split D L i hiD hiL]
  simp only [fullCoordinateOldHistory,
    fullCoordinateAssembleHiddenAlice, dite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have hj : (j : Fin n) ≠ i := by
    intro he
    have hnot : (j : Fin n) ∉ insert i L :=
      (Finset.mem_sdiff.mp j.property).2
    apply hnot
    simp [he]
  simp [fullCoordinateNewHistory,
    hj]

theorem fullCoordinateHiddenBobWeight_split
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n // j ∈ L} → Y) :
    fullHistoryHiddenBobWeight G
        (fullCoordinateNewHistory D L i r x)
        (fullCoordinateAssembleHiddenBob L i y hidden) =
      G.conditionalYGivenX x y *
        fullHistoryHiddenBobWeight G
          (fullCoordinateOldHistory D L i r y) hidden := by
  classical
  unfold fullHistoryHiddenBobWeight
  rw [finsetSubtype_prod_insert L i hiL]
  simp only [fullCoordinateNewHistory,
    fullCoordinateAssembleHiddenBob, dite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have hj : (j : Fin n) ≠ i := by
    intro he
    exact hiL (he ▸ j.property)
  simp [fullCoordinateOldHistory,     hj]

theorem fullCoordinateAliceFilter_conditional_mean
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (y : Y) :
    fullCoordinateAliceMeanFilter G n S D L i r α y =
      conditionalAliceAverage G
        (fullCoordinateAliceQuestionFilter G n S D L i r α) y := by
  classical
  let e := fullCoordinateHiddenAliceEquiv
    (X := X) D L i hiD hiL
  let f : X × ({j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) →
      Matrix S.Alice S.Alice ℂ := fun t =>
    (G.conditionalXGivenY y t.1 *
      fullHistoryHiddenAliceWeight G
        (fullCoordinateNewHistory D L i r t.1) t.2) •
      conditionedAliceEffect G n S D α
        (fullHistoryAliceQuestion
          (fullCoordinateNewHistory D L i r t.1) t.2)
  unfold fullCoordinateAliceMeanFilter
    fullCoordinateAliceQuestionFilter
  calc
    fullHistoryAliceFilter G n S D L
      (fullCoordinateOldHistory D L i r y) α =
      ∑ hidden : ({j : Fin n //
        j ∈ fullHistoryRemaining n D L} → X), f (e hidden) := by
        unfold fullHistoryAliceFilter
        apply Finset.sum_congr rfl
        intro hidden _
        have he := e.symm_apply_apply hidden
        change fullCoordinateAssembleHiddenAlice
          D L i (e hidden).1 (e hidden).2 = hidden at he
        conv_lhs => rw [← he]
        rw [fullCoordinateHiddenAliceWeight_split
          G D L i hiD hiL r (e hidden).1 y (e hidden).2]
        rw [fullCoordinateAliceQuestion_eq
          D L i hiD hiL r (e hidden).1 y (e hidden).2]
    _ = ∑ t : X × ({j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} → X),
          f t := e.sum_comp f
    _ = conditionalAliceAverage G
        (fun x => fullHistoryAliceFilter G n S D (insert i L)
          (fullCoordinateNewHistory D L i r x) α) y := by
      simp [f, conditionalAliceAverage, fullHistoryAliceFilter,
        Fintype.sum_prod_type, Finset.smul_sum, smul_smul]

theorem fullCoordinateBobFilter_conditional_mean
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B)
    (x : X) :
    fullCoordinateBobMeanFilter G n S D L i r β x =
      conditionalBobAverage G
        (fullCoordinateBobQuestionFilter G n S D L i r β) x := by
  classical
  let e := fullCoordinateHiddenBobEquiv
    (Y := Y) L i hiL
  let f : Y × ({j : Fin n // j ∈ L} → Y) →
      Matrix S.Bob S.Bob ℂ := fun t =>
    (G.conditionalYGivenX x t.1 *
      fullHistoryHiddenBobWeight G
        (fullCoordinateOldHistory D L i r t.1) t.2) •
      conditionedBobEffect G n S D β
        (fullHistoryBobQuestion
          (fullCoordinateOldHistory D L i r t.1) t.2)
  unfold fullCoordinateBobMeanFilter
    fullCoordinateBobQuestionFilter
  calc
    fullHistoryBobFilter G n S D (insert i L)
      (fullCoordinateNewHistory D L i r x) β =
      ∑ hidden : ({j : Fin n // j ∈ insert i L} → Y),
        f (e hidden) := by
        unfold fullHistoryBobFilter
        apply Finset.sum_congr rfl
        intro hidden _
        have he := e.symm_apply_apply hidden
        change fullCoordinateAssembleHiddenBob
          L i (e hidden).1 (e hidden).2 = hidden at he
        conv_lhs => rw [← he]
        rw [fullCoordinateHiddenBobWeight_split
          G D L i hiL r x (e hidden).1 (e hidden).2]
        rw [fullCoordinateBobQuestion_eq
          D L i hiD hiL r x (e hidden).1 (e hidden).2]
    _ = ∑ t : Y × ({j : Fin n // j ∈ L} → Y), f t :=
      e.sum_comp f
    _ = conditionalBobAverage G
        (fun y => fullHistoryBobFilter G n S D L
          (fullCoordinateOldHistory D L i r y) β) x := by
      simp [f, conditionalBobAverage, fullHistoryBobFilter,
        Fintype.sum_prod_type, Finset.smul_sum, smul_smul]

end CoordinateFilters

theorem matrixLogEntropy_weighted_jensen_posSemidef
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef) :
    ((∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
      cfc (fun z : ℝ => z * Real.log z) M).PosSemidef := by
  classical
  let hM : M.PosSemidef := by
    rw [← mean]
    exact weighted_positive_matrix_mean weight F nonnegative positive
  have hgap := finite_purification_log_entropy_jensen
    weight F M nonnegative normalized mean positive
  change
    ((∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
      cfc (fun z : ℝ => z * Real.log z) M -
      (∑ i : ι, weight i •
        ((finitePurificationMatrix F M positive hM i -
            meanFinitePurificationMatrix F M positive hM).conjTranspose *
          (finitePurificationMatrix F M positive hM i -
            meanFinitePurificationMatrix F M positive hM)))).PosSemidef
    at hgap
  have hvariance :
      (∑ i : ι, weight i •
        ((finitePurificationMatrix F M positive hM i -
            meanFinitePurificationMatrix F M positive hM).conjTranspose *
          (finitePurificationMatrix F M positive hM i -
            meanFinitePurificationMatrix F M positive hM))).PosSemidef := by
    apply Matrix.posSemidef_sum Finset.univ
    intro i _
    exact (Matrix.posSemidef_conjTranspose_mul_self
      (finitePurificationMatrix F M positive hM i -
        meanFinitePurificationMatrix F M positive hM)).smul
      (nonnegative i)
  convert hgap.add hvariance using 1 ; module

section ConditionalJensen

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem conditionalAlice_matrixLogEntropy_gap_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    (G : Game X Y A B)
    (H : X → Matrix d d ℂ)
    (hH : ∀ x, (H x).PosSemidef)
    (y : Y) (hy : 0 < G.marginalY y) :
    (conditionalAliceAverage G
        (fun x => cfc (fun z : ℝ => z * Real.log z) (H x)) y -
      cfc (fun z : ℝ => z * Real.log z)
        (conditionalAliceAverage G H y)).PosSemidef := by
  exact matrixLogEntropy_weighted_jensen_posSemidef
    (G.conditionalXGivenY y) H
    (conditionalAliceAverage G H y)
    (fun x => G.conditionalXGivenY_nonneg y x)
    (G.conditionalXGivenY_sum y hy)
    rfl hH

def fullCoordinateAliceEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) : ℝ :=
  ∑ y : Y, G.marginalY y *
    bornTracePairing S.state.matrix
      (conditionalAliceAverage G
        (fun x => cfc (fun z : ℝ => z * Real.log z)
          (fullCoordinateAliceQuestionFilter G n S D L i r α x)) y -
        cfc (fun z : ℝ => z * Real.log z)
          (fullCoordinateAliceMeanFilter G n S D L i r α y))
      (fullCoordinateBobQuestionFilter G n S D L i r β y)

theorem fullCoordinateAliceEntropyIncrement_eq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) :
    (∑ x : X, G.marginalX x *
      bornTracePairing S.state.matrix
        (cfc (fun z : ℝ => z * Real.log z)
          (fullCoordinateAliceQuestionFilter G n S D L i r α x))
        (fullCoordinateBobMeanFilter G n S D L i r β x)) -
    (∑ y : Y, G.marginalY y *
      bornTracePairing S.state.matrix
        (cfc (fun z : ℝ => z * Real.log z)
          (fullCoordinateAliceMeanFilter G n S D L i r α y))
        (fullCoordinateBobQuestionFilter G n S D L i r β y)) =
      fullCoordinateAliceEntropyIncrement G n S D L i r α β := by
  have h := alice_reveal_increment G
    (bornTracePairing S.state.matrix)
    (fullCoordinateAliceQuestionFilter G n S D L i r α)
    (fullCoordinateAliceMeanFilter G n S D L i r α)
    (fullCoordinateBobQuestionFilter G n S D L i r β)
    (fun F => cfc (fun z : ℝ => z * Real.log z) F)
  simp_rw [← fullCoordinateBobFilter_conditional_mean
    G n S D L i hiD hiL r β] at h
  exact h

theorem fullCoordinateAliceEntropyIncrement_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) :
    0 ≤ fullCoordinateAliceEntropyIncrement G n S D L i r α β := by
  unfold fullCoordinateAliceEntropyIncrement
  apply Finset.sum_nonneg
  intro y _
  by_cases hy : G.marginalY y = 0
  · simp [hy]
  · have hypos : 0 < G.marginalY y :=
      lt_of_le_of_ne (G.marginalY_nonneg y) (Ne.symm hy)
    have hmean := fullCoordinateAliceFilter_conditional_mean
      G n S D L i hiD hiL r α y
    have hgap :
        (conditionalAliceAverage G
          (fun x => cfc (fun z : ℝ => z * Real.log z)
            (fullCoordinateAliceQuestionFilter G n S D L i r α x)) y -
          cfc (fun z : ℝ => z * Real.log z)
            (fullCoordinateAliceMeanFilter G n S D L i r α y)).PosSemidef := by
      rw [hmean]
      exact conditionalAlice_matrixLogEntropy_gap_posSemidef G
        (fullCoordinateAliceQuestionFilter G n S D L i r α)
        (fun x => fullHistoryAliceFilter_posSemidef G n S D
          (insert i L) (fullCoordinateNewHistory D L i r x) α)
        y hypos
    exact mul_nonneg (G.marginalY_nonneg y)
      (trace_mul_posSemidef_nonneg S.state.positive
        (hgap.kronecker
          (fullHistoryBobFilter_posSemidef G n S D L
            (fullCoordinateOldHistory D L i r y) β)))

end ConditionalJensen

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def fullCoordinateBaseWinIndicator
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) : ℝ := by
  classical
  exact if ∀ j : {j : Fin n // j ∈ D},
    G.predicate (r.aliceConditioned j) (r.bobConditioned j)
      (α j) (β j) = true then 1 else 0

theorem fullCoordinateBaseWinIndicator_nonneg
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) :
    0 ≤ fullCoordinateBaseWinIndicator G D L i r α β := by
  classical
  unfold fullCoordinateBaseWinIndicator
  split <;> norm_num

theorem fullCoordinateOldHistory_winIndicator_eq
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (y : Y)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) :
    fullHistoryWinIndicator G
      (fullCoordinateOldHistory D L i r y) α β =
      fullCoordinateBaseWinIndicator G D L i r α β := by
  classical
  simp [fullHistoryWinIndicator, fullCoordinateBaseWinIndicator,
    fullCoordinateOldHistory]

theorem fullCoordinateNewHistory_winIndicator_eq
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) :
    fullHistoryWinIndicator G
      (fullCoordinateNewHistory D L i r x) α β =
      fullCoordinateBaseWinIndicator G D L i r α β := by
  classical
  simp [fullHistoryWinIndicator, fullCoordinateBaseWinIndicator,
    fullCoordinateNewHistory]

theorem fullCoordinate_three_sum_rotate
    {I J K T : Type*}
    [Fintype I] [Fintype J] [Fintype K] [AddCommMonoid T]
    (f : I → J → K → T) :
    (∑ i : I, ∑ j : J, ∑ k : K, f i j k) =
      ∑ j : J, ∑ k : K, ∑ i : I, f i j k := by
  calc
    (∑ i : I, ∑ j : J, ∑ k : K, f i j k) =
      ∑ j : J, ∑ i : I, ∑ k : K, f i j k := by
        rw [Finset.sum_comm]
    _ = ∑ j : J, ∑ k : K, ∑ i : I, f i j k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]

theorem fullCoordinateOldHistory_sum
    {T : Type*} [AddCommMonoid T]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (f : FullSubsetHistory X Y n D L → T) :
    (∑ h : FullSubsetHistory X Y n D L, f h) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ y : Y, f (fullCoordinateOldHistory D L i r y) := by
  classical
  simpa [fullCoordinateOldHistoryEquiv, Fintype.sum_prod_type]
    using ((fullCoordinateOldHistoryEquiv
      (X := X) (Y := Y) D L i hiD hiL).symm.sum_comp f).symm

theorem fullCoordinateNewHistory_sum
    {T : Type*} [AddCommMonoid T]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiL : i ∉ L)
    (f : FullSubsetHistory X Y n D (insert i L) → T) :
    (∑ h : FullSubsetHistory X Y n D (insert i L), f h) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ x : X, f (fullCoordinateNewHistory D L i r x) := by
  classical
  simpa [fullCoordinateNewHistoryEquiv, Fintype.sum_prod_type]
    using ((fullCoordinateNewHistoryEquiv
      (X := X) (Y := Y) D L i hiL).symm.sum_comp f).symm

theorem fullCoordinateWeightedOldSum
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (value : (h : FullSubsetHistory X Y n D L) →
      ({j : Fin n // j ∈ D} → A) →
      ({j : Fin n // j ∈ D} → B) → ℝ) :
    (∑ h : FullSubsetHistory X Y n D L,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullCoordinateBaseWeight G D L i r *
          fullCoordinateBaseWinIndicator G D L i r α β *
          (∑ y : Y, G.marginalY y *
            value (fullCoordinateOldHistory D L i r y) α β) := by
  classical
  calc
    (∑ h : FullSubsetHistory X Y n D L,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ y : Y,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullHistoryWeight G (fullCoordinateOldHistory D L i r y) *
          fullHistoryWinIndicator G
            (fullCoordinateOldHistory D L i r y) α β *
          value (fullCoordinateOldHistory D L i r y) α β :=
      fullCoordinateOldHistory_sum D L i hiD hiL
        (fun h => ∑ α : {j : Fin n // j ∈ D} → A,
          ∑ β : {j : Fin n // j ∈ D} → B,
            fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
              value h α β)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [fullCoordinate_three_sum_rotate]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [fullCoordinateOldHistory_weight G D L i hiD hiL r y,
        fullCoordinateOldHistory_winIndicator_eq G D L i r y α β]
      ring

theorem fullCoordinateWeightedNewSum
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiL : i ∉ L)
    (value : (h : FullSubsetHistory X Y n D (insert i L)) →
      ({j : Fin n // j ∈ D} → A) →
      ({j : Fin n // j ∈ D} → B) → ℝ) :
    (∑ h : FullSubsetHistory X Y n D (insert i L),
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullCoordinateBaseWeight G D L i r *
          fullCoordinateBaseWinIndicator G D L i r α β *
          (∑ x : X, G.marginalX x *
            value (fullCoordinateNewHistory D L i r x) α β) := by
  classical
  calc
    (∑ h : FullSubsetHistory X Y n D (insert i L),
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ x : X,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullHistoryWeight G (fullCoordinateNewHistory D L i r x) *
          fullHistoryWinIndicator G
            (fullCoordinateNewHistory D L i r x) α β *
          value (fullCoordinateNewHistory D L i r x) α β :=
      fullCoordinateNewHistory_sum D L i hiL
        (fun h => ∑ α : {j : Fin n // j ∈ D} → A,
          ∑ β : {j : Fin n // j ∈ D} → B,
            fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
              value h α β)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [fullCoordinate_three_sum_rotate]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [fullCoordinateNewHistory_weight G D L i hiL r x,
        fullCoordinateNewHistory_winIndicator_eq G D L i r x α β]
      ring

def fullCoordinateAliceTotalEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n) : ℝ :=
  ∑ r : FullCoordinateRevealHistory X Y n D L i,
  ∑ α : {j : Fin n // j ∈ D} → A,
  ∑ β : {j : Fin n // j ∈ D} → B,
    fullCoordinateBaseWeight G D L i r *
      fullCoordinateBaseWinIndicator G D L i r α β *
      fullCoordinateAliceEntropyIncrement G n S D L i r α β

theorem fullHistoryAliceEntropyPotential_increment
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    fullHistoryAliceEntropyPotential G n S D (insert i L) -
        fullHistoryAliceEntropyPotential G n S D L =
      fullCoordinateAliceTotalEntropyIncrement G n S D L i := by
  classical
  unfold fullHistoryAliceEntropyPotential
    fullCoordinateAliceTotalEntropyIncrement
  rw [fullCoordinateWeightedNewSum G D L i hiL
    (fun h α β => bornTracePairing S.state.matrix
      (cfc (fun z : ℝ => z * Real.log z)
        (fullHistoryAliceFilter G n S D (insert i L) h α))
      (fullHistoryBobFilter G n S D (insert i L) h β))]
  rw [fullCoordinateWeightedOldSum G D L i hiD hiL
    (fun h α β => bornTracePairing S.state.matrix
      (cfc (fun z : ℝ => z * Real.log z)
        (fullHistoryAliceFilter G n S D L h α))
      (fullHistoryBobFilter G n S D L h β))]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro β _
  rw [← mul_sub]
  congr 1
  exact fullCoordinateAliceEntropyIncrement_eq
    G n S D L i hiD hiL r α β

theorem fullCoordinateAliceTotalEntropyIncrement_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    0 ≤ fullCoordinateAliceTotalEntropyIncrement G n S D L i := by
  unfold fullCoordinateAliceTotalEntropyIncrement
  exact Finset.sum_nonneg fun r _ =>
    Finset.sum_nonneg fun α _ =>
      Finset.sum_nonneg fun β _ =>
        mul_nonneg
          (mul_nonneg (fullCoordinateBaseWeight_nonneg G D L i r)
            (fullCoordinateBaseWinIndicator_nonneg G D L i r α β))
          (fullCoordinateAliceEntropyIncrement_nonneg
            G n S D L i hiD hiL r α β)

end

noncomputable section

open scoped BigOperators

abbrev SourceRemainingCoordinate {n : ℕ} (D : Finset (Fin n)) :=
  ↥(Finset.univ \ D)

abbrev SourceRemainingPermutation {n : ℕ} (D : Finset (Fin n)) :=
  Equiv.Perm (SourceRemainingCoordinate D)

def sourceRemainingPermutationRank
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D) :
    SourceRemainingCoordinate D ≃ Fin (Finset.univ \ D).card :=
  π.symm.trans (Finset.equivFin (Finset.univ \ D))

def sourceRemainingPermutationCoordinateSubtype
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    SourceRemainingCoordinate D :=
  (sourceRemainingPermutationRank D π).symm k

def sourceRemainingPermutationCoordinate
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) : Fin n :=
  (sourceRemainingPermutationCoordinateSubtype D π k).val

@[simp] theorem sourceRemainingPermutationRank_coordinate
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationRank D π
      (sourceRemainingPermutationCoordinateSubtype D π k) = k := by
  simp [sourceRemainingPermutationCoordinateSubtype]

theorem sourceRemainingPermutationCoordinate_not_mem
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationCoordinate D π k ∉ D := by
  have h := (sourceRemainingPermutationCoordinateSubtype D π k).property
  exact (Finset.mem_sdiff.mp h).2

def sourceRemainingPermutationPrefixSubtype
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin ((Finset.univ \ D).card + 1)) :
    Finset (SourceRemainingCoordinate D) := by
  classical
  exact Finset.univ.filter fun i =>
    (sourceRemainingPermutationRank D π i).val < k.val

def sourceRemainingPermutationPrefix
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin ((Finset.univ \ D).card + 1)) : Finset (Fin n) := by
  classical
  exact (sourceRemainingPermutationPrefixSubtype D π k).image
    (fun i : SourceRemainingCoordinate D => i.val)

theorem sourceRemainingPermutationPrefix_subset
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin ((Finset.univ \ D).card + 1)) :
    sourceRemainingPermutationPrefix D π k ⊆ Finset.univ \ D := by
  classical
  intro i hi
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
  simpa [hj] using j.property

theorem sourceRemainingPermutationCoordinate_not_mem_prefix
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationCoordinate D π k ∉
      sourceRemainingPermutationPrefix D π k.castSucc := by
  classical
  intro hmem
  obtain ⟨j, hj, hval⟩ := Finset.mem_image.mp hmem
  have heq : j = sourceRemainingPermutationCoordinateSubtype D π k := by
    apply Subtype.ext
    exact hval
  subst j
  have hlt := (Finset.mem_filter.mp hj).2
  simp at hlt

theorem sourceRemainingPermutationPrefixSubtype_succ
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationPrefixSubtype D π k.succ =
      insert (sourceRemainingPermutationCoordinateSubtype D π k)
        (sourceRemainingPermutationPrefixSubtype D π k.castSucc) := by
  classical
  ext i
  simp only [sourceRemainingPermutationPrefixSubtype,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  change
    (sourceRemainingPermutationRank D π i).val < k.val + 1 ↔
      i = sourceRemainingPermutationCoordinateSubtype D π k ∨
        (sourceRemainingPermutationRank D π i).val < k.val
  constructor
  · intro hi
    by_cases hlt : (sourceRemainingPermutationRank D π i).val < k.val
    · exact Or.inr hlt
    · left
      apply (sourceRemainingPermutationRank D π).injective
      have heq :
          sourceRemainingPermutationRank D π i = k := by
        apply Fin.ext
        omega
      simpa using heq
  · intro hi
    rcases hi with hi | hi
    · subst i
      simp
    · omega

theorem sourceRemainingPermutationPrefix_succ
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationPrefix D π k.succ =
      insert (sourceRemainingPermutationCoordinate D π k)
        (sourceRemainingPermutationPrefix D π k.castSucc) := by
  classical
  unfold sourceRemainingPermutationPrefix
  rw [sourceRemainingPermutationPrefixSubtype_succ,
    Finset.image_insert]
  rfl

@[simp] theorem sourceRemainingPermutationPrefix_zero
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D) :
    sourceRemainingPermutationPrefix D π 0 = ∅ := by
  classical
  simp [sourceRemainingPermutationPrefix,
    sourceRemainingPermutationPrefixSubtype]

@[simp] theorem sourceRemainingPermutationPrefix_last
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D) :
    sourceRemainingPermutationPrefix D π
        (Fin.last (Finset.univ \ D).card) =
      Finset.univ \ D := by
  classical
  ext i
  constructor
  · intro hi
    exact sourceRemainingPermutationPrefix_subset D π _ hi
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨(⟨i, hi⟩ : SourceRemainingCoordinate D), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      (sourceRemainingPermutationRank D π
        (⟨i, hi⟩ : SourceRemainingCoordinate D)).isLt⟩

theorem sourceRemainingPermutationCoordinate_sum
    {T : Type*} [AddCommMonoid T]
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (f : Fin n → T) :
    (∑ k : Fin (Finset.univ \ D).card,
      f (sourceRemainingPermutationCoordinate D π k)) =
      ∑ i : SourceRemainingCoordinate D, f i.val := by
  classical
  exact (sourceRemainingPermutationRank D π).symm.sum_comp
    (fun i : SourceRemainingCoordinate D => f i.val)

theorem fin_sum_successive_sub
    {m : ℕ} (f : Fin (m + 1) → ℝ) :
    (∑ k : Fin m, (f k.succ - f k.castSucc)) =
      f (Fin.last m) - f 0 := by
  rw [Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ f
  have hlast := Fin.sum_univ_castSucc f
  linarith

section ActualEntropyBudgets

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def sourcePermutationAliceEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) : ℝ :=
  fullCoordinateAliceTotalEntropyIncrement G n S D
    (sourceRemainingPermutationPrefix D π k.castSucc)
    (sourceRemainingPermutationCoordinate D π k)

theorem sourcePermutationAliceEntropyIncrement_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    0 ≤ sourcePermutationAliceEntropyIncrement G n S D π k := by
  apply fullCoordinateAliceTotalEntropyIncrement_nonneg
  · exact sourceRemainingPermutationCoordinate_not_mem D π k
  · exact sourceRemainingPermutationCoordinate_not_mem_prefix D π k

theorem sourcePermutationAliceEntropyPotential_step
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    fullHistoryAliceEntropyPotential G n S D
        (sourceRemainingPermutationPrefix D π k.succ) -
      fullHistoryAliceEntropyPotential G n S D
        (sourceRemainingPermutationPrefix D π k.castSucc) =
      sourcePermutationAliceEntropyIncrement G n S D π k := by
  rw [sourceRemainingPermutationPrefix_succ]
  exact fullHistoryAliceEntropyPotential_increment G n S D
    (sourceRemainingPermutationPrefix D π k.castSucc)
    (sourceRemainingPermutationCoordinate D π k)
    (sourceRemainingPermutationCoordinate_not_mem D π k)
    (sourceRemainingPermutationCoordinate_not_mem_prefix D π k)

theorem sourcePermutationAliceEntropyIncrement_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (π : SourceRemainingPermutation D) :
    (∑ k : Fin (Finset.univ \ D).card,
      sourcePermutationAliceEntropyIncrement G n S D π k) =
      fullHistoryAliceEntropyPotential G n S D (Finset.univ \ D) -
        fullHistoryAliceEntropyPotential G n S D ∅ := by
  calc
    (∑ k : Fin (Finset.univ \ D).card,
      sourcePermutationAliceEntropyIncrement G n S D π k) =
      ∑ k : Fin (Finset.univ \ D).card,
        (fullHistoryAliceEntropyPotential G n S D
            (sourceRemainingPermutationPrefix D π k.succ) -
          fullHistoryAliceEntropyPotential G n S D
            (sourceRemainingPermutationPrefix D π k.castSucc)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (sourcePermutationAliceEntropyPotential_step G n S D π k).symm
    _ = fullHistoryAliceEntropyPotential G n S D
            (sourceRemainingPermutationPrefix D π
              (Fin.last (Finset.univ \ D).card)) -
          fullHistoryAliceEntropyPotential G n S D
            (sourceRemainingPermutationPrefix D π 0) :=
      fin_sum_successive_sub
        (fun k => fullHistoryAliceEntropyPotential G n S D
          (sourceRemainingPermutationPrefix D π k))
    _ = _ := by simp

theorem sourcePermutationAliceEntropyIncrement_sum_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hp : 0 < (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D))
    (π : SourceRemainingPermutation D) :
    (∑ k : Fin (Finset.univ \ D).card,
      sourcePermutationAliceEntropyIncrement G n S D π k) ≤
      (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) *
        Real.log
          (fullHistoryAnswerCount (A := A) (B := B) D /
            (strategyEventLaw (G.repeat n) S).eventMass
              (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) := by
  classical
  rw [sourcePermutationAliceEntropyIncrement_sum]
  have hlast := fullHistoryAliceEntropyPotential_nonpos
    G n S D (Finset.univ \ D)
  have hfirst := fullHistoryAliceEntropyPotential_lower_bound
    G n S D ∅ (Finset.empty_subset _) hp
  linarith

def sourceUniformPermutationAverage
    {n : ℕ} (D : Finset (Fin n))
    (f : SourceRemainingPermutation D →
      Fin (Finset.univ \ D).card → ℝ) : ℝ :=
  (∑ π : SourceRemainingPermutation D,
    ∑ k : Fin (Finset.univ \ D).card, f π k) /
    ((Fintype.card (SourceRemainingPermutation D) : ℝ) *
      ((Finset.univ \ D).card : ℝ))

theorem sourceRemainingPermutation_card_pos
    {n : ℕ} (D : Finset (Fin n)) :
    0 < (Fintype.card (SourceRemainingPermutation D) : ℝ) := by
  classical
  exact_mod_cast (Fintype.card_pos_iff.mpr
    ⟨Equiv.refl (SourceRemainingCoordinate D)⟩ :
      0 < Fintype.card (SourceRemainingPermutation D))

theorem sourceUniformPermutationAverage_le
    {n : ℕ} (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    (f : SourceRemainingPermutation D →
      Fin (Finset.univ \ D).card → ℝ)
    {C : ℝ}
    (hC : ∀ π : SourceRemainingPermutation D,
      (∑ k : Fin (Finset.univ \ D).card, f π k) ≤ C) :
    sourceUniformPermutationAverage D f ≤
      C / ((Finset.univ \ D).card : ℝ) := by
  classical
  have hperm := sourceRemainingPermutation_card_pos D
  have hmreal : 0 < ((Finset.univ \ D).card : ℝ) := by
    exact_mod_cast hm
  have hden : 0 <
      (Fintype.card (SourceRemainingPermutation D) : ℝ) *
        ((Finset.univ \ D).card : ℝ) :=
    mul_pos hperm hmreal
  have hsum :
      (∑ π : SourceRemainingPermutation D,
        ∑ k : Fin (Finset.univ \ D).card, f π k) ≤
        (Fintype.card (SourceRemainingPermutation D) : ℝ) * C := by
    calc
      (∑ π : SourceRemainingPermutation D,
        ∑ k : Fin (Finset.univ \ D).card, f π k) ≤
          ∑ _π : SourceRemainingPermutation D, C := by
        apply Finset.sum_le_sum
        intro π _
        exact hC π
      _ = (Fintype.card (SourceRemainingPermutation D) : ℝ) * C := by
        simp
  unfold sourceUniformPermutationAverage
  calc
    (∑ π : SourceRemainingPermutation D,
        ∑ k : Fin (Finset.univ \ D).card, f π k) /
      ((Fintype.card (SourceRemainingPermutation D) : ℝ) *
        ((Finset.univ \ D).card : ℝ)) ≤
      ((Fintype.card (SourceRemainingPermutation D) : ℝ) * C) /
        ((Fintype.card (SourceRemainingPermutation D) : ℝ) *
          ((Finset.univ \ D).card : ℝ)) :=
        (div_le_div_iff_of_pos_right hden).mpr hsum
    _ = C / ((Finset.univ \ D).card : ℝ) :=
      mul_div_mul_left C ((Finset.univ \ D).card : ℝ) hperm.ne'

theorem sourceUniformPermutationAverage_nonneg
    {n : ℕ} (D : Finset (Fin n))
    (f : SourceRemainingPermutation D →
      Fin (Finset.univ \ D).card → ℝ)
    (hf : ∀ π k, 0 ≤ f π k) :
    0 ≤ sourceUniformPermutationAverage D f := by
  classical
  apply div_nonneg
  · exact Finset.sum_nonneg fun π _ =>
      Finset.sum_nonneg fun k _ => hf π k
  · exact mul_nonneg
      (Nat.cast_nonneg (Fintype.card (SourceRemainingPermutation D)))
      (Nat.cast_nonneg (Finset.univ \ D).card)

theorem sourceUniformPermutationAliceEntropyBudget
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    (hp : 0 < (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) :
    sourceUniformPermutationAverage D
        (sourcePermutationAliceEntropyIncrement G n S D) ≤
      (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) *
        Real.log
          (fullHistoryAnswerCount (A := A) (B := B) D /
            (strategyEventLaw (G.repeat n) S).eventMass
              (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) /
          ((Finset.univ \ D).card : ℝ) := by
  apply sourceUniformPermutationAverage_le D hm
  intro π
  exact sourcePermutationAliceEntropyIncrement_sum_le G n S D hp π

end ActualEntropyBudgets

end

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

def exactLeft
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) : Finset M :=
  Finset.univ.filter fun j => j ≠ coordinate ∧ partition j = false

def exactRight
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) : Finset M :=
  Finset.univ.filter fun j => j ≠ coordinate ∧ partition j = true

theorem exactLeft_coordinate_not_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) :
    coordinate ∉ exactLeft coordinate partition := by
  simp [exactLeft]

theorem exactRight_coordinate_not_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) :
    coordinate ∉ exactRight coordinate partition := by
  simp [exactRight]

structure ExactForwardSeed
    (M : Type*) [Fintype M] [DecidableEq M] where
  coordinate : M
  partition : M → Bool
  leftOrder : Equiv.Perm
    {j : M // j ∈ exactLeft coordinate partition}
  rightOrder : Equiv.Perm
    {j : M // j ∈ exactRight coordinate partition}
  leftCut : Fin ((exactLeft coordinate partition).card + 1)
  rightCut : Fin ((exactRight coordinate partition).card + 1)
  deriving Fintype

abbrev ExactRemainingSeed
    {n : ℕ} (D : Finset (Fin n)) :=
  ExactForwardSeed (SourceRemainingCoordinate D)

def exactLeftRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactLeft seed.coordinate seed.partition} ≃
      Fin (exactLeft seed.coordinate seed.partition).card :=
  seed.leftOrder.symm.trans
    (Finset.equivFin (exactLeft seed.coordinate seed.partition))

def exactRightRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactRight seed.coordinate seed.partition} ≃
      Fin (exactRight seed.coordinate seed.partition).card :=
  seed.rightOrder.symm.trans
    (Finset.equivFin (exactRight seed.coordinate seed.partition))

def exactLeftPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M //
      j ∈ exactLeft seed.coordinate seed.partition} =>
      (exactLeftRank seed j).val < seed.leftCut.val)).image
        Subtype.val

def exactRightPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M //
      j ∈ exactRight seed.coordinate seed.partition} =>
      (exactRightRank seed j).val < seed.rightCut.val)).image
        Subtype.val

theorem exactLeftPrefix_subset
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactLeftPrefix seed ⊆
      exactLeft seed.coordinate seed.partition := by
  intro j hj
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hj
  exact ha ▸ a.property

theorem exactRightPrefix_subset
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactRightPrefix seed ⊆
      exactRight seed.coordinate seed.partition := by
  intro j hj
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hj
  exact ha ▸ a.property

def exactSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : ℝ :=
  (1 / (Fintype.card M : ℝ)) *
    (1 / (Fintype.card (M → Bool) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactLeft seed.coordinate seed.partition}) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactRight seed.coordinate seed.partition}) : ℝ)) *
    (1 / ((exactLeft
      seed.coordinate seed.partition).card + 1 : ℝ)) *
    (1 / ((exactRight
      seed.coordinate seed.partition).card + 1 : ℝ))

theorem exactSeedWeight_nonneg
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    0 ≤ exactSeedWeight seed := by
  unfold exactSeedWeight
  positivity

abbrev ExactSeedTuple
    (M : Type*) [Fintype M] [DecidableEq M] :=
  Σ i : M, Σ partition : M → Bool,
    (Equiv.Perm {j : M // j ∈ exactLeft i partition}) ×
    (Equiv.Perm {j : M // j ∈ exactRight i partition}) ×
    Fin ((exactLeft i partition).card + 1) ×
    Fin ((exactRight i partition).card + 1)

def exactSeedEquiv
    (M : Type*) [Fintype M] [DecidableEq M] :
    ExactForwardSeed M ≃ ExactSeedTuple M where
  toFun seed := ⟨seed.coordinate, seed.partition,
    seed.leftOrder, seed.rightOrder, seed.leftCut, seed.rightCut⟩
  invFun t :=
    ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1,
      t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv seed := by
    cases seed
    rfl
  right_inv t := by
    rcases t with ⟨i, partition, leftOrder, rightOrder,
      leftCut, rightCut⟩
    rfl

@[simp] theorem exactSeedEquiv_symm_apply
    {M : Type*} [Fintype M] [DecidableEq M]
    (t : ExactSeedTuple M) :
    (exactSeedEquiv M).symm t =
      ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1,
        t.2.2.2.2.1, t.2.2.2.2.2⟩ := by
  rfl

theorem exactForwardSeed_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (f : ExactForwardSeed M → ℝ) :
    (∑ seed : ExactForwardSeed M, f seed) =
      ∑ i : M,
      ∑ partition : M → Bool,
      ∑ leftOrder : Equiv.Perm
        {j : M // j ∈ exactLeft i partition},
      ∑ rightOrder : Equiv.Perm
        {j : M // j ∈ exactRight i partition},
      ∑ leftCut : Fin ((exactLeft i partition).card + 1),
      ∑ rightCut : Fin ((exactRight i partition).card + 1),
        f ⟨i, partition, leftOrder, rightOrder, leftCut, rightCut⟩ := by
  classical
  calc
    (∑ seed : ExactForwardSeed M, f seed) =
        ∑ t : ExactSeedTuple M,
          f ((exactSeedEquiv M).symm t) :=
      ((exactSeedEquiv M).symm.sum_comp f).symm
    _ = _ := by
      simp [Fintype.sum_sigma, Fintype.sum_prod_type,
        exactSeedEquiv_symm_apply]

theorem exactUniform_sum
    {T : Type*} [Fintype T]
    (positive : 0 < Fintype.card T) :
    (∑ _t : T, (1 / (Fintype.card T : ℝ))) = 1 := by
  have hcard : (Fintype.card T : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

theorem exactUniform_sum_mul
    {T : Type*} [Fintype T]
    (positive : 0 < Fintype.card T) (value : ℝ) :
    (∑ _t : T,
      value * (1 / (Fintype.card T : ℝ))) = value := by
  rw [← Finset.mul_sum, exactUniform_sum positive]
  ring

theorem exactPrefixUniform_sum_mul
    (m : ℕ) (value : ℝ) :
    (∑ _k : Fin (m + 1),
      value * (1 / ((m : ℝ) + 1))) = value := by
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    (exactUniform_sum_mul
      (T := Fin (m + 1)) (by simp) value)

theorem exactPermutationUniform_sum_mul
    {T : Type*} [Fintype T] (value : ℝ) :
    (∑ _π : Equiv.Perm T,
      value * (1 / (Fintype.card (Equiv.Perm T) : ℝ))) = value := by
  exact exactUniform_sum_mul
    (Fintype.card_pos_iff.mpr ⟨Equiv.refl T⟩) value

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false

theorem common_finite_purification_pair_jensen
    {ι κ d : Type*}
    [Fintype ι] [Fintype κ] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ)
    (F : κ → Matrix d d ℂ)
    (anchor : Matrix d d ℂ)
    (positive : ∀ k, (F k).PosSemidef)
    (hanchor : anchor.PosSemidef)
    (choose : ι → κ) (meanIndex : κ)
    (nonnegative : ∀ a, 0 ≤ weight a)
    (normalized : (∑ a : ι, weight a) = 1)
    (mean : (∑ a : ι, weight a • F (choose a)) = F meanIndex) :
    ((∑ a : ι, weight a •
        cfc (fun z : ℝ => z * Real.log z) (F (choose a))) -
      cfc (fun z : ℝ => z * Real.log z) (F meanIndex) -
      (∑ a : ι, weight a •
        ((finitePurificationMatrix F anchor positive hanchor (choose a) -
            finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
          (finitePurificationMatrix F anchor positive hanchor (choose a) -
            finitePurificationMatrix F anchor positive hanchor meanIndex)))).PosSemidef := by
  classical
  let H : ι → Matrix d d ℂ := fun a => F (choose a)
  let M : Matrix d d ℂ := F meanIndex
  have hH : ∀ a, (H a).PosSemidef := fun a => positive (choose a)
  have hM : M.PosSemidef := positive meanIndex
  have hmean : (∑ a : ι, weight a • H a) = M := mean
  have hlocal := finite_purification_log_entropy_jensen
    weight H M nonnegative normalized hmean hH
  change
    ((∑ a : ι, weight a •
        cfc (fun z : ℝ => z * Real.log z) (H a)) -
      cfc (fun z : ℝ => z * Real.log z) M -
      (∑ a : ι, weight a •
        ((finitePurificationMatrix H M hH hM a -
            meanFinitePurificationMatrix H M hH hM).conjTranspose *
          (finitePurificationMatrix H M hH hM a -
            meanFinitePurificationMatrix H M hH hM)))).PosSemidef at hlocal
  have hpair (a : ι) :
      (finitePurificationMatrix F anchor positive hanchor (choose a) -
          finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
        (finitePurificationMatrix F anchor positive hanchor (choose a) -
          finitePurificationMatrix F anchor positive hanchor meanIndex) =
      (finitePurificationMatrix H M hH hM a -
          meanFinitePurificationMatrix H M hH hM).conjTranspose *
        (finitePurificationMatrix H M hH hM a -
          meanFinitePurificationMatrix H M hH hM) := by
    rw [finitePurificationMatrix_pair_difference_gram_eq_integral,
      finitePurificationMatrix_difference_gram_eq_integral]
  change
    ((∑ a : ι, weight a •
        cfc (fun z : ℝ => z * Real.log z) (H a)) -
      cfc (fun z : ℝ => z * Real.log z) M -
      (∑ a : ι, weight a •
        ((finitePurificationMatrix F anchor positive hanchor (choose a) -
            finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
          (finitePurificationMatrix F anchor positive hanchor (choose a) -
            finitePurificationMatrix F anchor positive hanchor meanIndex)))).PosSemidef
  simp_rw [hpair]
  exact hlocal

theorem commonFinitePurification_weighted_left_variation_le
    {X Y A B ι κ eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype ι] [Fintype κ] [Fintype eB]
    {G : Game X Y A B} (S : Strategy G)
    (weight : ι → ℝ)
    (F : κ → Matrix S.Alice S.Alice ℂ)
    (anchor : Matrix S.Alice S.Alice ℂ)
    (positive : ∀ k, (F k).PosSemidef)
    (hanchor : anchor.PosSemidef)
    (choose : ι → κ) (meanIndex : κ)
    (nonnegative : ∀ a, 0 ≤ weight a)
    (normalized : (∑ a : ι, weight a) = 1)
    (mean : (∑ a : ι, weight a • F (choose a)) = F meanIndex)
    (KB : Matrix eB S.Bob ℂ) :
    (∑ a : ι, weight a *
      ‖finiteLocalPurificationVector S
          (finitePurificationMatrix F anchor positive hanchor (choose a)) KB -
        finiteLocalPurificationVector S
          (finitePurificationMatrix F anchor positive hanchor meanIndex) KB‖ ^ 2) ≤
      bornTracePairing S.state.matrix
        ((∑ a : ι, weight a •
            cfc (fun z : ℝ => z * Real.log z) (F (choose a))) -
          cfc (fun z : ℝ => z * Real.log z) (F meanIndex))
        (KB.conjTranspose * KB) := by
  classical
  have hJ := common_finite_purification_pair_jensen
    weight F anchor positive hanchor choose meanIndex
    nonnegative normalized mean
  have hnonneg := trace_mul_posSemidef_nonneg S.state.positive
    (hJ.kronecker (Matrix.posSemidef_conjTranspose_mul_self KB))
  change
    0 ≤ bornTracePairing S.state.matrix
      (((∑ a : ι, weight a •
          cfc (fun z : ℝ => z * Real.log z) (F (choose a))) -
        cfc (fun z : ℝ => z * Real.log z) (F meanIndex)) -
       (∑ a : ι, weight a •
        ((finitePurificationMatrix F anchor positive hanchor (choose a) -
            finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
          (finitePurificationMatrix F anchor positive hanchor (choose a) -
            finitePurificationMatrix F anchor positive hanchor meanIndex))))
      (KB.conjTranspose * KB) at hnonneg
  have hsum :
      bornTracePairing S.state.matrix
        (∑ a : ι, weight a •
          ((finitePurificationMatrix F anchor positive hanchor (choose a) -
              finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
            (finitePurificationMatrix F anchor positive hanchor (choose a) -
              finitePurificationMatrix F anchor positive hanchor meanIndex)))
        (KB.conjTranspose * KB) =
        ∑ a : ι, weight a *
          ‖finiteLocalPurificationVector S
              (finitePurificationMatrix F anchor positive hanchor (choose a)) KB -
            finiteLocalPurificationVector S
              (finitePurificationMatrix F anchor positive hanchor meanIndex) KB‖ ^ 2 := by
    simp only [map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [finiteLocalPurificationVector_sub_left_norm_sq]
  rw [map_sub] at hnonneg
  change
    0 ≤
      bornTracePairing S.state.matrix
        ((∑ a : ι, weight a •
            cfc (fun z : ℝ => z * Real.log z) (F (choose a))) -
          cfc (fun z : ℝ => z * Real.log z) (F meanIndex))
        (KB.conjTranspose * KB) -
      bornTracePairing S.state.matrix
        (∑ a : ι, weight a •
          ((finitePurificationMatrix F anchor positive hanchor (choose a) -
              finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
            (finitePurificationMatrix F anchor positive hanchor (choose a) -
              finitePurificationMatrix F anchor positive hanchor meanIndex)))
        (KB.conjTranspose * KB) at hnonneg
  rw [hsum] at hnonneg
  linarith

theorem commonFinitePurification_weighted_right_variation_le
    {X Y A B ι κ eA : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype ι] [Fintype κ] [Fintype eA]
    {G : Game X Y A B} (S : Strategy G)
    (weight : ι → ℝ)
    (F : κ → Matrix S.Bob S.Bob ℂ)
    (anchor : Matrix S.Bob S.Bob ℂ)
    (positive : ∀ k, (F k).PosSemidef)
    (hanchor : anchor.PosSemidef)
    (choose : ι → κ) (meanIndex : κ)
    (nonnegative : ∀ b, 0 ≤ weight b)
    (normalized : (∑ b : ι, weight b) = 1)
    (mean : (∑ b : ι, weight b • F (choose b)) = F meanIndex)
    (KA : Matrix eA S.Alice ℂ) :
    (∑ b : ι, weight b *
      ‖finiteLocalPurificationVector S KA
          (finitePurificationMatrix F anchor positive hanchor (choose b)) -
        finiteLocalPurificationVector S KA
          (finitePurificationMatrix F anchor positive hanchor meanIndex)‖ ^ 2) ≤
      bornTracePairing S.state.matrix
        (KA.conjTranspose * KA)
        ((∑ b : ι, weight b •
            cfc (fun z : ℝ => z * Real.log z) (F (choose b))) -
          cfc (fun z : ℝ => z * Real.log z) (F meanIndex)) := by
  classical
  have hJ := common_finite_purification_pair_jensen
    weight F anchor positive hanchor choose meanIndex
    nonnegative normalized mean
  have hnonneg := trace_mul_posSemidef_nonneg S.state.positive
    ((Matrix.posSemidef_conjTranspose_mul_self KA).kronecker hJ)
  change
    0 ≤ bornTracePairing S.state.matrix
      (KA.conjTranspose * KA)
      (((∑ b : ι, weight b •
          cfc (fun z : ℝ => z * Real.log z) (F (choose b))) -
        cfc (fun z : ℝ => z * Real.log z) (F meanIndex)) -
       (∑ b : ι, weight b •
        ((finitePurificationMatrix F anchor positive hanchor (choose b) -
            finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
          (finitePurificationMatrix F anchor positive hanchor (choose b) -
            finitePurificationMatrix F anchor positive hanchor meanIndex)))) at hnonneg
  have hsum :
      bornTracePairing S.state.matrix
        (KA.conjTranspose * KA)
        (∑ b : ι, weight b •
          ((finitePurificationMatrix F anchor positive hanchor (choose b) -
              finitePurificationMatrix F anchor positive hanchor meanIndex).conjTranspose *
            (finitePurificationMatrix F anchor positive hanchor (choose b) -
              finitePurificationMatrix F anchor positive hanchor meanIndex))) =
        ∑ b : ι, weight b *
          ‖finiteLocalPurificationVector S KA
              (finitePurificationMatrix F anchor positive hanchor (choose b)) -
            finiteLocalPurificationVector S KA
              (finitePurificationMatrix F anchor positive hanchor meanIndex)‖ ^ 2 := by
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [finiteLocalPurificationVector_sub_right_norm_sq]
  rw [map_sub, hsum] at hnonneg
  linarith

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem rectangular_matrix_quadratic_compression
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (K : Matrix e d ℂ) (E : Matrix e e ℂ)
    (z : EuclideanSpace ℂ d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := e) (𝕜 := ℂ) E)
      (toLp 2 (K.mulVec (ofLp z))) =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)
          (K.conjTranspose * E * K)) z := by
  unfold quadraticExpectation
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  change
    (E.mulVec (K.mulVec (ofLp z)) ⬝ᵥ
      star (K.mulVec (ofLp z))).re =
    ((K.conjTranspose * E * K).mulVec (ofLp z) ⬝ᵥ
      star (ofLp z)).re
  rw [dotProduct_comm (E.mulVec (K.mulVec (ofLp z))),
    Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  rw [dotProduct_comm]

theorem finiteLocalPurificationJointMatrix_compression
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    [DecidableEq eA] [DecidableEq eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ)
    (EA : Matrix eA eA ℂ) (EB : Matrix eB eB ℂ) :
    (finiteLocalPurificationJointMatrix S KA KB).conjTranspose *
        (((EA ⊗ₖ
            (1 : Matrix (S.Alice × S.Bob)
              (S.Alice × S.Bob) ℂ)) ⊗ₖ EB)) *
        finiteLocalPurificationJointMatrix S KA KB =
      (((KA.conjTranspose * EA * KA) ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob)
            (S.Alice × S.Bob) ℂ)) ⊗ₖ
        (KB.conjTranspose * EB * KB)) := by
  unfold finiteLocalPurificationJointMatrix
  rw [Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp

theorem finiteLocalPurificationVector_quadratic
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype eA] [Fintype eB]
    [DecidableEq eA] [DecidableEq eB]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ)
    (EA : Matrix eA eA ℂ) (EB : Matrix eB eB ℂ) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (eA × (S.Alice × S.Bob)) × eB) (𝕜 := ℂ)
        (((EA ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob)
            (S.Alice × S.Bob) ℂ)) ⊗ₖ EB)))
      (finiteLocalPurificationVector S KA KB) =
      bornTracePairing S.state.matrix
        (KA.conjTranspose * EA * KA)
        (KB.conjTranspose * EB * KB) := by
  unfold finiteLocalPurificationVector
  rw [rectangular_matrix_quadratic_compression,
    finiteLocalPurificationJointMatrix_compression]
  exact strategyPurificationVector_quadratic S
    (KA.conjTranspose * EA * KA)
    (KB.conjTranspose * EB * KB)

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def conditionedAliceCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (xs : Fin n → X) (i : Fin n) (a : A) :
    Matrix S.Alice S.Alice ℂ := by
  classical
  exact ∑ answers : Fin n → A,
    if (∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
      answers i = a
    then (S.aliceMeasurement xs).effect answers
    else 0

def conditionedBobCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {j : Fin n // j ∈ D} → B)
    (ys : Fin n → Y) (i : Fin n) (b : B) :
    Matrix S.Bob S.Bob ℂ := by
  classical
  exact ∑ answers : Fin n → B,
    if (∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
      answers i = b
    then (S.bobMeasurement ys).effect answers
    else 0

theorem conditionedAliceCoordinateEffect_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (xs : Fin n → X) (i : Fin n) (a : A) :
    (conditionedAliceCoordinateEffect G n S D α xs i a).PosSemidef := by
  classical
  unfold conditionedAliceCoordinateEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.aliceMeasurement xs).positive answers
  · exact Matrix.PosSemidef.zero

theorem conditionedBobCoordinateEffect_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {j : Fin n // j ∈ D} → B)
    (ys : Fin n → Y) (i : Fin n) (b : B) :
    (conditionedBobCoordinateEffect G n S D β ys i b).PosSemidef := by
  classical
  unfold conditionedBobCoordinateEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.bobMeasurement ys).positive answers
  · exact Matrix.PosSemidef.zero

theorem conditionedAliceCoordinateEffect_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (xs : Fin n → X) (i : Fin n) :
    (∑ a : A, conditionedAliceCoordinateEffect G n S D α xs i a) =
      conditionedAliceEffect G n S D α xs := by
  classical
  unfold conditionedAliceCoordinateEffect conditionedAliceEffect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro answers _
  calc
    (∑ a : A,
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
        answers i = a
      then (S.aliceMeasurement xs).effect answers
      else 0) =
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
        answers i = answers i
      then (S.aliceMeasurement xs).effect answers
      else 0 := by
        apply Fintype.sum_eq_single (answers i)
        intro a ha
        simp [ha.symm]
    _ = _ := by simp

theorem conditionedBobCoordinateEffect_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {j : Fin n // j ∈ D} → B)
    (ys : Fin n → Y) (i : Fin n) :
    (∑ b : B, conditionedBobCoordinateEffect G n S D β ys i b) =
      conditionedBobEffect G n S D β ys := by
  classical
  unfold conditionedBobCoordinateEffect conditionedBobEffect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro answers _
  calc
    (∑ b : B,
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
        answers i = b
      then (S.bobMeasurement ys).effect answers
      else 0) =
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
        answers i = answers i
      then (S.bobMeasurement ys).effect answers
      else 0 := by
        apply Fintype.sum_eq_single (answers i)
        intro b hb
        simp [hb.symm]
    _ = _ := by simp

def fullHistoryAliceCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {j : Fin n // j ∈ D} → A)
    (i : Fin n) (a : A) :
    Matrix S.Alice S.Alice ℂ :=
  ∑ hidden : {j : Fin n // j ∈ fullHistoryRemaining n D L} → X,
    fullHistoryHiddenAliceWeight G h hidden •
      conditionedAliceCoordinateEffect G n S D α
        (fullHistoryAliceQuestion h hidden) i a

def fullHistoryBobCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (β : {j : Fin n // j ∈ D} → B)
    (i : Fin n) (b : B) :
    Matrix S.Bob S.Bob ℂ :=
  ∑ hidden : {j : Fin n // j ∈ L} → Y,
    fullHistoryHiddenBobWeight G h hidden •
      conditionedBobCoordinateEffect G n S D β
        (fullHistoryBobQuestion h hidden) i b

def fullCoordinateAliceRefinementEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (x : X) (a : A) : Matrix S.Alice S.Alice ℂ :=
  fullHistoryAliceCoordinateEffect G n S D (insert i L)
    (fullCoordinateNewHistory D L i r x) α i a

def fullCoordinateBobRefinementEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B)
    (y : Y) (b : B) : Matrix S.Bob S.Bob ℂ :=
  fullHistoryBobCoordinateEffect G n S D L
    (fullCoordinateOldHistory D L i r y) β i b

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

structure ExactRevealHistory
    (X Y : Type*) [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) where
  aliceConditioned : {j : Fin n // j ∈ D} → X
  bobConditioned : {j : Fin n // j ∈ D} → Y
  aliceLeft :
    {j : SourceRemainingCoordinate D //
      j ∈ exactLeft seed.coordinate seed.partition} → X
  bobRight :
    {j : SourceRemainingCoordinate D //
      j ∈ exactRight seed.coordinate seed.partition} → Y
  bobLeftPrefix :
    {j : SourceRemainingCoordinate D //
      j ∈ exactLeftPrefix seed} → Y
  aliceRightPrefix :
    {j : SourceRemainingCoordinate D //
      j ∈ exactRightPrefix seed} → X

abbrev ExactRevealHistoryTuple
    (X Y : Type*) [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :=
  ({j : Fin n // j ∈ D} → X) ×
  ({j : Fin n // j ∈ D} → Y) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactLeft seed.coordinate seed.partition} → X) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactRight seed.coordinate seed.partition} → Y) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactLeftPrefix seed} → Y) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactRightPrefix seed} → X)

def exactRevealHistoryEquiv
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    ExactRevealHistory X Y D seed ≃
      ExactRevealHistoryTuple X Y D seed where
  toFun h := ⟨h.aliceConditioned, h.bobConditioned,
    h.aliceLeft, h.bobRight, h.bobLeftPrefix, h.aliceRightPrefix⟩
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1,
    t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv h := by cases h; rfl
  right_inv t := by
    rcases t with ⟨ac, bc, al, br, bl, ar⟩
    rfl

noncomputable instance exactRevealHistoryFintype
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    Fintype (ExactRevealHistory X Y D seed) := by
  classical
  exact Fintype.ofEquiv (ExactRevealHistoryTuple X Y D seed)
    (exactRevealHistoryEquiv
      (X := X) (Y := Y) D seed).symm

abbrev ExactFullQuestion
    (X Y : Type*) (n : ℕ) :=
  (Fin n → X) × (Fin n → Y)

def exactRevealCode
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n) :
    ExactRevealHistory X Y D seed where
  aliceConditioned j := q.1 j.val
  bobConditioned j := q.2 j.val
  aliceLeft j := q.1 j.val.val
  bobRight j := q.2 j.val.val
  bobLeftPrefix j := q.2 j.val.val
  aliceRightPrefix j := q.1 j.val.val

def exactPriorQuestionWeight
    (G : Game X Y A B) (n : ℕ)
    (q : ExactFullQuestion X Y n) : ℝ :=
  (G.repeat n).questionWeight q.1 q.2

theorem exactPriorQuestionWeight_nonneg
    (G : Game X Y A B) (n : ℕ)
    (q : ExactFullQuestion X Y n) :
    0 ≤ exactPriorQuestionWeight G n q :=
  (G.repeat n).weight_nonneg q.1 q.2

theorem exactPriorQuestionWeight_sum
    (G : Game X Y A B) (n : ℕ) :
    (∑ q : ExactFullQuestion X Y n,
      exactPriorQuestionWeight G n q) = 1 := by
  simpa [exactPriorQuestionWeight,
    Fintype.sum_prod_type] using (G.repeat n).weight_normalized

def exactRevealMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history
    then exactPriorQuestionWeight G n q
    else 0

theorem exactRevealMass_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed) :
    0 ≤ exactRevealMass G n D seed history := by
  unfold exactRevealMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPriorQuestionWeight_nonneg G n q
  · exact le_rfl

theorem exactRevealMass_sum
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    (∑ history : ExactRevealHistory X Y D seed,
      exactRevealMass G n D seed history) = 1 := by
  classical
  unfold exactRevealMass
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_ite_eq]
  exact exactPriorQuestionWeight_sum G n

def exactAliceQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
    then exactPriorQuestionWeight G n q
    else 0

def exactBobQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
    then exactPriorQuestionWeight G n q
    else 0

def exactJointQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x ∧
      q.2 seed.coordinate.val = y
    then exactPriorQuestionWeight G n q
    else 0

theorem exactAliceQuestionMass_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) :
    0 ≤ exactAliceQuestionMass G n D seed history x := by
  unfold exactAliceQuestionMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPriorQuestionWeight_nonneg G n q
  · exact le_rfl

theorem exactBobQuestionMass_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) :
    0 ≤ exactBobQuestionMass G n D seed history y := by
  unfold exactBobQuestionMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPriorQuestionWeight_nonneg G n q
  · exact le_rfl

def exactAliceQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) : Matrix S.Alice S.Alice ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
    then
      (exactPriorQuestionWeight G n q /
        exactAliceQuestionMass G n D seed history x) •
        conditionedAliceEffect G n S D answer q.1
    else 0

def exactBobQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) : Matrix S.Bob S.Bob ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
    then
      (exactPriorQuestionWeight G n q /
        exactBobQuestionMass G n D seed history y) •
        conditionedBobEffect G n S D answer q.2
    else 0

theorem exactAliceQuestionFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) :
    (exactAliceQuestionFilter
      G n S D seed history answer x).PosSemidef := by
  unfold exactAliceQuestionFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedAliceEffect_positive G n S D answer q.1).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactAliceQuestionMass_nonneg
          G n D seed history x))
  · exact Matrix.PosSemidef.zero

theorem exactBobQuestionFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) :
    (exactBobQuestionFilter
      G n S D seed history answer y).PosSemidef := by
  unfold exactBobQuestionFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedBobEffect_positive G n S D answer q.2).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactBobQuestionMass_nonneg
          G n D seed history y))
  · exact Matrix.PosSemidef.zero

def exactAliceMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (y : Y) : Matrix S.Alice S.Alice ℂ :=
  ∑ x : X, G.conditionalXGivenY y x •
    exactAliceQuestionFilter G n S D seed history answer x

def exactBobMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) : Matrix S.Bob S.Bob ℂ :=
  ∑ y : Y, G.conditionalYGivenX x y •
    exactBobQuestionFilter G n S D seed history answer y

theorem exactAliceMeanFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (y : Y) :
    (exactAliceMeanFilter
      G n S D seed history answer y).PosSemidef := by
  unfold exactAliceMeanFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro x _
  exact (exactAliceQuestionFilter_posSemidef
    G n S D seed history answer x).smul
    (G.conditionalXGivenY_nonneg y x)

theorem exactBobMeanFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) :
    (exactBobMeanFilter
      G n S D seed history answer x).PosSemidef := by
  unfold exactBobMeanFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro y _
  exact (exactBobQuestionFilter_posSemidef
    G n S D seed history answer y).smul
    (G.conditionalYGivenX_nonneg x y)

def exactAliceCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (a : A) : Matrix S.Alice S.Alice ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
    then
      (exactPriorQuestionWeight G n q /
        exactAliceQuestionMass G n D seed history x) •
        conditionedAliceCoordinateEffect G n S D answer q.1
          seed.coordinate.val a
    else 0

def exactBobCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) (b : B) : Matrix S.Bob S.Bob ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
    then
      (exactPriorQuestionWeight G n q /
        exactBobQuestionMass G n D seed history y) •
        conditionedBobCoordinateEffect G n S D answer q.2
          seed.coordinate.val b
    else 0

theorem exactAliceCoordinateFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (a : A) :
    (exactAliceCoordinateFilter
      G n S D seed history answer x a).PosSemidef := by
  unfold exactAliceCoordinateFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedAliceCoordinateEffect_posSemidef
      G n S D answer q.1 seed.coordinate.val a).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactAliceQuestionMass_nonneg
          G n D seed history x))
  · exact Matrix.PosSemidef.zero

theorem exactBobCoordinateFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) (b : B) :
    (exactBobCoordinateFilter
      G n S D seed history answer y b).PosSemidef := by
  unfold exactBobCoordinateFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedBobCoordinateEffect_posSemidef
      G n S D answer q.2 seed.coordinate.val b).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactBobQuestionMass_nonneg
          G n D seed history y))
  · exact Matrix.PosSemidef.zero

theorem exactAliceCoordinateFilter_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) :
    (∑ a : A,
      exactAliceCoordinateFilter
        G n S D seed history answer x a) =
      exactAliceQuestionFilter
        G n S D seed history answer x := by
  classical
  unfold exactAliceCoordinateFilter
    exactAliceQuestionFilter
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
  · simp [hq, ← Finset.smul_sum,
      conditionedAliceCoordinateEffect_sum]
  · simp [hq]

theorem exactBobCoordinateFilter_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) :
    (∑ b : B,
      exactBobCoordinateFilter
        G n S D seed history answer y b) =
      exactBobQuestionFilter
        G n S D seed history answer y := by
  classical
  unfold exactBobCoordinateFilter
    exactBobQuestionFilter
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
  · simp [hq, ← Finset.smul_sum,
      conditionedBobCoordinateEffect_sum]
  · simp [hq]

def exactAlicePurificationFamily
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A) :
    Sum X Y → Matrix S.Alice S.Alice ℂ :=
  Sum.elim
    (exactAliceQuestionFilter G n S D seed history answer)
    (exactAliceMeanFilter G n S D seed history answer)

def exactBobPurificationFamily
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B) :
    Sum Y X → Matrix S.Bob S.Bob ℂ :=
  Sum.elim
    (exactBobQuestionFilter G n S D seed history answer)
    (exactBobMeanFilter G n S D seed history answer)

theorem exactAlicePurificationFamily_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (q : Sum X Y) :
    (exactAlicePurificationFamily
      G n S D seed history answer q).PosSemidef := by
  cases q with
  | inl x =>
      exact exactAliceQuestionFilter_posSemidef
        G n S D seed history answer x
  | inr y =>
      exact exactAliceMeanFilter_posSemidef
        G n S D seed history answer y

theorem exactBobPurificationFamily_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (q : Sum Y X) :
    (exactBobPurificationFamily
      G n S D seed history answer q).PosSemidef := by
  cases q with
  | inl y =>
      exact exactBobQuestionFilter_posSemidef
        G n S D seed history answer y
  | inr x =>
      exact exactBobMeanFilter_posSemidef
        G n S D seed history answer x

abbrev ExactAliceLiftIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A) :=
  S.Alice × Fin (Module.finrank ℂ
    (commonPurificationSubspace
      (exactAlicePurificationFamily
        G n S D seed history answer)
      (0 : Matrix S.Alice S.Alice ℂ)
      (exactAlicePurificationFamily_posSemidef
        G n S D seed history answer)
      Matrix.PosSemidef.zero))

abbrev ExactBobLiftIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B) :=
  S.Bob × Fin (Module.finrank ℂ
    (commonPurificationSubspace
      (exactBobPurificationFamily
        G n S D seed history answer)
      (0 : Matrix S.Bob S.Bob ℂ)
      (exactBobPurificationFamily_posSemidef
        G n S D seed history answer)
      Matrix.PosSemidef.zero))

def exactAlicePurificationMatrix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (q : Sum X Y) :
    Matrix (ExactAliceLiftIndex
      G n S D seed history answer) S.Alice ℂ :=
  finitePurificationMatrix
    (exactAlicePurificationFamily
      G n S D seed history answer)
    0
    (exactAlicePurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

def exactBobPurificationMatrix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (q : Sum Y X) :
    Matrix (ExactBobLiftIndex
      G n S D seed history answer) S.Bob ℂ :=
  finitePurificationMatrix
    (exactBobPurificationFamily
      G n S D seed history answer)
    0
    (exactBobPurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

theorem exactAlicePurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (q : Sum X Y) :
    (exactAlicePurificationMatrix
      G n S D seed history answer q).conjTranspose *
      exactAlicePurificationMatrix
        G n S D seed history answer q =
      exactAlicePurificationFamily
        G n S D seed history answer q :=
  finitePurificationMatrix_gram
    (exactAlicePurificationFamily
      G n S D seed history answer)
    0
    (exactAlicePurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

theorem exactBobPurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (q : Sum Y X) :
    (exactBobPurificationMatrix
      G n S D seed history answer q).conjTranspose *
      exactBobPurificationMatrix
        G n S D seed history answer q =
      exactBobPurificationFamily
        G n S D seed history answer q :=
  finitePurificationMatrix_gram
    (exactBobPurificationFamily
      G n S D seed history answer)
    0
    (exactBobPurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

@[ext (iff := false)] structure ExactHistoryFlag
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) where
  seed : ExactRemainingSeed D
  history : ExactRevealHistory X Y D seed
  aliceAnswer : {j : Fin n // j ∈ D} → A
  bobAnswer : {j : Fin n // j ∈ D} → B

abbrev ExactHistoryFlagTuple
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) :=
  Σ seed : ExactRemainingSeed D,
    ExactRevealHistory X Y D seed ×
      ({j : Fin n // j ∈ D} → A) ×
      ({j : Fin n // j ∈ D} → B)

def exactHistoryFlagEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    ExactHistoryFlag X Y A B D ≃
      ExactHistoryFlagTuple X Y A B D where
  toFun r := ⟨r.seed, r.history, r.aliceAnswer, r.bobAnswer⟩
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv r := by cases r; rfl
  right_inv t := by
    rcases t with ⟨seed, history, aliceAnswer, bobAnswer⟩
    rfl

noncomputable instance exactHistoryFlagFintype
    {n : ℕ} (D : Finset (Fin n)) :
    Fintype (ExactHistoryFlag X Y A B D) := by
  classical
  exact Fintype.ofEquiv (ExactHistoryFlagTuple X Y A B D)
    (exactHistoryFlagEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm

theorem exactHistoryFlag_sum
    {n : ℕ} (D : Finset (Fin n))
    (f : ExactHistoryFlag X Y A B D → ℝ) :
    (∑ r : ExactHistoryFlag X Y A B D, f r) =
      ∑ seed : ExactRemainingSeed D,
      ∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        f ⟨seed, history, aliceAnswer, bobAnswer⟩ := by
  classical
  calc
    (∑ r : ExactHistoryFlag X Y A B D, f r) =
        ∑ t : ExactHistoryFlagTuple X Y A B D,
          f ((exactHistoryFlagEquiv
            (X := X) (Y := Y) (A := A) (B := B) D).symm t) :=
      ((exactHistoryFlagEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm.sum_comp f).symm
    _ = _ := by
      simp [Fintype.sum_sigma, Fintype.sum_prod_type,
        exactHistoryFlagEquiv]

abbrev ExactAliceLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :=
  ExactAliceLiftIndex
    G n S D r.seed r.history r.aliceAnswer × (S.Alice × S.Bob)

abbrev ExactBobLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :=
  ExactBobLiftIndex
    G n S D r.seed r.history r.bobAnswer

def exactUnnormalizedPsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) :=
  finiteLocalPurificationVector S
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))

def exactUnnormalizedPhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) :=
  finiteLocalPurificationVector S
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inr y))
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))

def exactUnnormalizedGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) :=
  finiteLocalPurificationVector S
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inr x))

theorem exactUnnormalizedPsi_norm_sq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2 =
      bornTracePairing S.state.matrix
        (exactAliceQuestionFilter
          G n S D r.seed r.history r.aliceAnswer x)
        (exactBobQuestionFilter
          G n S D r.seed r.history r.bobAnswer y) := by
  unfold exactUnnormalizedPsi
  rw [finiteLocalPurificationVector_norm_sq,
    exactAlicePurificationMatrix_gram,
    exactBobPurificationMatrix_gram]
  rfl

theorem exactAliceQuestionPurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x)).conjTranspose *
      exactAlicePurificationMatrix
        G n S D r.seed r.history r.aliceAnswer (.inl x) =
      exactAliceQuestionFilter
        G n S D r.seed r.history r.aliceAnswer x :=
  exactAlicePurificationMatrix_gram
    G n S D r.seed r.history r.aliceAnswer (.inl x)

theorem exactBobQuestionPurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y)).conjTranspose *
      exactBobPurificationMatrix
        G n S D r.seed r.history r.bobAnswer (.inl y) =
      exactBobQuestionFilter
        G n S D r.seed r.history r.bobAnswer y :=
  exactBobPurificationMatrix_gram
    G n S D r.seed r.history r.bobAnswer (.inl y)

def exactAliceRefinedPOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) :
    POVM A (ExactAliceLiftIndex
      G n S D r.seed r.history r.aliceAnswer) :=
  purifiedRefinedPOVM
    (exactAliceQuestionFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceQuestionFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactAliceQuestionPurificationMatrix_gram G n S D r x)
    (exactAliceCoordinateFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_sum
      G n S D r.seed r.history r.aliceAnswer x)
    a₀

def exactBobRefinedPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) :
    POVM B (ExactBobLiftIndex
      G n S D r.seed r.history r.bobAnswer) :=
  purifiedRefinedPOVM
    (exactBobQuestionFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobQuestionFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))
    (exactBobQuestionPurificationMatrix_gram G n S D r y)
    (exactBobCoordinateFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_sum
      G n S D r.seed r.history r.bobAnswer y)
    b₀

theorem exactAliceRefinedPOVM_compression
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) (a : A) :
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x)).conjTranspose *
      (exactAliceRefinedPOVM G n S D r a₀ x).effect a *
      exactAlicePurificationMatrix
        G n S D r.seed r.history r.aliceAnswer (.inl x) =
      exactAliceCoordinateFilter
        G n S D r.seed r.history r.aliceAnswer x a := by
  exact purifiedRefinedPOVM_compression
    (exactAliceQuestionFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceQuestionFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactAliceQuestionPurificationMatrix_gram G n S D r x)
    (exactAliceCoordinateFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_sum
      G n S D r.seed r.history r.aliceAnswer x)
    a₀ a

theorem exactBobRefinedPOVM_compression
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) (b : B) :
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y)).conjTranspose *
      (exactBobRefinedPOVM G n S D r b₀ y).effect b *
      exactBobPurificationMatrix
        G n S D r.seed r.history r.bobAnswer (.inl y) =
      exactBobCoordinateFilter
        G n S D r.seed r.history r.bobAnswer y b := by
  exact purifiedRefinedPOVM_compression
    (exactBobQuestionFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobQuestionFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))
    (exactBobQuestionPurificationMatrix_gram G n S D r y)
    (exactBobCoordinateFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_sum
      G n S D r.seed r.history r.bobAnswer y)
    b₀ b

theorem exactRefinedPOVM_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) (a : A) (b : B) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r)
        (𝕜 := ℂ)
        (((exactAliceRefinedPOVM
          G n S D r a₀ x).effect a ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob)
            (S.Alice × S.Bob) ℂ)) ⊗ₖ
          (exactBobRefinedPOVM
            G n S D r b₀ y).effect b))
      (exactUnnormalizedPsi G n S D r x y) =
      bornTracePairing S.state.matrix
        (exactAliceCoordinateFilter
          G n S D r.seed r.history r.aliceAnswer x a)
        (exactBobCoordinateFilter
          G n S D r.seed r.history r.bobAnswer y b) := by
  unfold exactUnnormalizedPsi
  rw [finiteLocalPurificationVector_quadratic,
    exactAliceRefinedPOVM_compression,
    exactBobRefinedPOVM_compression]

abbrev ExactPaddedLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :=
  PUnit.{1} ⊕
    (ExactAliceLocalIndex G n S D r ⊕
      ExactBobLocalIndex G n S D r)

def exactPaddedVector
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  toLp 2 fun q =>
    match q.1, q.2 with
    | .inr (.inl a), .inr (.inr b) => z (a, b)
    | _, _ => 0

theorem exactPaddedVector_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)) :
    ‖exactPaddedVector G n S D r z‖ = ‖z‖ := by
  classical
  have hsquare :
      ‖exactPaddedVector G n S D r z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, exactPaddedVector,
      Fintype.sum_prod_type, Fintype.sum_sum_type]
  nlinarith [norm_nonneg (exactPaddedVector G n S D r z),
    norm_nonneg z]

theorem exactPaddedVector_sub
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (u v : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)) :
    exactPaddedVector G n S D r (u - v) =
      exactPaddedVector G n S D r u -
        exactPaddedVector G n S D r v := by
  classical
  ext q
  rcases q with ⟨a, b⟩
  rcases a with a | (a | a) <;>
    rcases b with b | (b | b) <;>
    simp [exactPaddedVector]

def exactPaddedDefault
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) := by
  classical
  exact PiLp.single 2 (.inl PUnit.unit, .inl PUnit.unit) (1 : ℂ)

theorem exactPaddedDefault_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    ‖exactPaddedDefault G n S D r‖ = 1 := by
  classical
  simp [exactPaddedDefault]

def exactPsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  normalizeOrDefault (exactPaddedDefault G n S D r)
    (exactPaddedVector G n S D r
      (exactUnnormalizedPsi G n S D r x y))

def exactPhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  normalizeOrDefault (exactPaddedDefault G n S D r)
    (exactPaddedVector G n S D r
      (exactUnnormalizedPhi G n S D r y))

def exactGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  normalizeOrDefault (exactPaddedDefault G n S D r)
    (exactPaddedVector G n S D r
      (exactUnnormalizedGamma G n S D r x))

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactAliceQuestionCompatible
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (xs : Fin n → X) : Prop :=
  (∀ j : {j : Fin n // j ∈ D},
      xs j.val = history.aliceConditioned j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactLeft seed.coordinate seed.partition},
      xs j.val.val = history.aliceLeft j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactRightPrefix seed},
      xs j.val.val = history.aliceRightPrefix j) ∧
  xs seed.coordinate.val = x

def exactBobQuestionCompatible
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) (ys : Fin n → Y) : Prop :=
  (∀ j : {j : Fin n // j ∈ D},
      ys j.val = history.bobConditioned j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactRight seed.coordinate seed.partition},
      ys j.val.val = history.bobRight j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactLeftPrefix seed},
      ys j.val.val = history.bobLeftPrefix j) ∧
  ys seed.coordinate.val = y

theorem exactRevealCode_compatible_iff
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs : Fin n → X) (ys : Fin n → Y) :
    (exactRevealCode D seed (xs, ys) = history ∧
      xs seed.coordinate.val = x ∧ ys seed.coordinate.val = y) ↔
      exactAliceQuestionCompatible
        D seed history x xs ∧
      exactBobQuestionCompatible
        D seed history y ys := by
  constructor
  · rintro ⟨h, hx, hy⟩
    subst history
    exact ⟨⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, hx⟩,
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, hy⟩⟩
  · rintro ⟨⟨hxc, hxl, hxr, hx⟩,
      ⟨hyc, hyr, hyl, hy⟩⟩
    refine ⟨?_, hx, hy⟩
    cases history with
    | mk ac bc al br bl ar =>
      have hac :
          (fun j : {j : Fin n // j ∈ D} => xs j.val) = ac :=
        funext hxc
      have hbc :
          (fun j : {j : Fin n // j ∈ D} => ys j.val) = bc :=
        funext hyc
      have hal :
          (fun j : {j : SourceRemainingCoordinate D //
            j ∈ exactLeft seed.coordinate seed.partition} =>
            xs j.val.val) = al :=
        funext hxl
      have hbr :
          (fun j : {j : SourceRemainingCoordinate D //
            j ∈ exactRight seed.coordinate seed.partition} =>
            ys j.val.val) = br :=
        funext hyr
      have hbl :
          (fun j : {j : SourceRemainingCoordinate D //
            j ∈ exactLeftPrefix seed} =>
            ys j.val.val) = bl :=
        funext hyl
      have har :
          (fun j : {j : SourceRemainingCoordinate D //
            j ∈ exactRightPrefix seed} =>
            xs j.val.val) = ar :=
        funext hxr
      cases hac
      cases hbc
      cases hal
      cases hbr
      cases hbl
      cases har
      rfl

theorem exactCompatible_coordinate_eq_or
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs xs' : Fin n → X) (ys ys' : Fin n → Y)
    (ha : exactAliceQuestionCompatible
      D seed history x xs)
    (ha' : exactAliceQuestionCompatible
      D seed history x xs')
    (hb : exactBobQuestionCompatible
      D seed history y ys)
    (hb' : exactBobQuestionCompatible
      D seed history y ys')
    (j : Fin n) :
    xs j = xs' j ∨ ys j = ys' j := by
  by_cases hj : j ∈ D
  · left
    exact (ha.1 ⟨j, hj⟩).trans (ha'.1 ⟨j, hj⟩).symm
  · let jr : SourceRemainingCoordinate D :=
      ⟨j, by simp [hj]⟩
    by_cases hcoordinate : jr = seed.coordinate
    · left
      have hval : j = seed.coordinate.val :=
        congrArg Subtype.val hcoordinate
      rw [hval]
      exact ha.2.2.2.trans ha'.2.2.2.symm
    · cases hbit : seed.partition jr with
      | false =>
          left
          have hleft :
              jr ∈ exactLeft
                seed.coordinate seed.partition := by
            simp [exactLeft, hcoordinate, hbit]
          exact (ha.2.1 ⟨jr, hleft⟩).trans
            (ha'.2.1 ⟨jr, hleft⟩).symm
      | true =>
          right
          have hright :
              jr ∈ exactRight
                seed.coordinate seed.partition := by
            simp [exactRight, hcoordinate, hbit]
          exact (hb.2.1 ⟨jr, hright⟩).trans
            (hb'.2.1 ⟨jr, hright⟩).symm

theorem exactQuestionWeight_rectangle
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs xs' : Fin n → X) (ys ys' : Fin n → Y)
    (ha : exactAliceQuestionCompatible
      D seed history x xs)
    (ha' : exactAliceQuestionCompatible
      D seed history x xs')
    (hb : exactBobQuestionCompatible
      D seed history y ys)
    (hb' : exactBobQuestionCompatible
      D seed history y ys') :
    (G.repeat n).questionWeight xs ys *
        (G.repeat n).questionWeight xs' ys' =
      (G.repeat n).questionWeight xs ys' *
        (G.repeat n).questionWeight xs' ys := by
  simp only [Game.repeat_questionWeight]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rcases exactCompatible_coordinate_eq_or
    D seed history x y xs xs' ys ys'
    ha ha' hb hb' j with hAlice | hBob
  · simp [hAlice, mul_comm]
  · simp [hBob]

def exactFiberQuestionWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs : Fin n → X) (ys : Fin n → Y) : ℝ :=
  if exactAliceQuestionCompatible
      D seed history x xs ∧
      exactBobQuestionCompatible
        D seed history y ys
  then (G.repeat n).questionWeight xs ys
  else 0

theorem exactFiberQuestionWeight_rectangle
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs xs' : Fin n → X) (ys ys' : Fin n → Y) :
    exactFiberQuestionWeight
        G n D seed history x y xs ys *
      exactFiberQuestionWeight
        G n D seed history x y xs' ys' =
    exactFiberQuestionWeight
        G n D seed history x y xs ys' *
      exactFiberQuestionWeight
        G n D seed history x y xs' ys := by
  classical
  by_cases ha : exactAliceQuestionCompatible
      D seed history x xs <;>
    by_cases ha' : exactAliceQuestionCompatible
      D seed history x xs' <;>
    by_cases hb : exactBobQuestionCompatible
      D seed history y ys <;>
    by_cases hb' : exactBobQuestionCompatible
      D seed history y ys' <;>
    simp [exactFiberQuestionWeight,
      ha, ha', hb, hb']
  simpa only [Game.repeat_questionWeight] using
    (exactQuestionWeight_rectangle
      G n D seed history x y xs xs' ys ys'
      ha ha' hb hb')

def exactFiberAliceMarginal
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) (xs : Fin n → X) : ℝ :=
  ∑ ys : Fin n → Y,
    exactFiberQuestionWeight G n D seed history x y xs ys

def exactFiberBobMarginal
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) (ys : Fin n → Y) : ℝ :=
  ∑ xs : Fin n → X,
    exactFiberQuestionWeight G n D seed history x y xs ys

def exactFiberQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) : ℝ :=
  ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
    exactFiberQuestionWeight G n D seed history x y xs ys

theorem exactFiberQuestionWeight_mul_mass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs : Fin n → X) (ys : Fin n → Y) :
    exactFiberQuestionWeight
        G n D seed history x y xs ys *
      exactFiberQuestionMass G n D seed history x y =
    exactFiberAliceMarginal
        G n D seed history x y xs *
      exactFiberBobMarginal
        G n D seed history x y ys := by
  classical
  symm
  calc
    exactFiberAliceMarginal
        G n D seed history x y xs *
      exactFiberBobMarginal
        G n D seed history x y ys =
      ∑ u : Fin n → Y, ∑ v : Fin n → X,
        exactFiberQuestionWeight
          G n D seed history x y xs u *
        exactFiberQuestionWeight
          G n D seed history x y v ys := by
      unfold exactFiberAliceMarginal
        exactFiberBobMarginal
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
    _ = ∑ u : Fin n → Y, ∑ v : Fin n → X,
        exactFiberQuestionWeight
          G n D seed history x y xs ys *
        exactFiberQuestionWeight
          G n D seed history x y v u := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      exact exactFiberQuestionWeight_rectangle
        G n D seed history x y xs v u ys
    _ = ∑ v : Fin n → X, ∑ u : Fin n → Y,
        exactFiberQuestionWeight
          G n D seed history x y xs ys *
        exactFiberQuestionWeight
          G n D seed history x y v u := by
      rw [Finset.sum_comm]
    _ = exactFiberQuestionWeight
        G n D seed history x y xs ys *
      exactFiberQuestionMass
        G n D seed history x y := by
      unfold exactFiberQuestionMass
      simp only [Finset.mul_sum]

end

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1200000

attribute [local instance] Classical.propDecidable

theorem exactFintypeCard_eq
    {T : Type*} (first second : Fintype T) :
    @Fintype.card T first = @Fintype.card T second :=
  @Fintype.card_congr T T first second (Equiv.refl T)

theorem exactSeedWeight_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M) :
    (∑ seed : ExactForwardSeed M,
      exactSeedWeight seed) = 1 := by
  classical
  have hbits : 0 < Fintype.card (M → Bool) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  rw [exactForwardSeed_sum]
  conv_rhs => rw [← exactUniform_sum nonempty]
  apply Finset.sum_congr (by ext; simp)
  intro coordinate _
  conv_rhs =>
    rw [← exactUniform_sum_mul hbits
      (1 / (Fintype.card M : ℝ))]
  apply Finset.sum_congr (by ext; simp)
  intro partition _
  letI : DecidableEq
      {j : M // j ∈ exactLeft coordinate partition} :=
    fun a b => Classical.propDecidable (a = b)
  letI : DecidableEq
      {j : M // j ∈ exactRight coordinate partition} :=
    fun a b => Classical.propDecidable (a = b)
  conv_rhs =>
    rw [← exactPermutationUniform_sum_mul
      (T := {j : M // j ∈ exactLeft coordinate partition})
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)))]
  apply Finset.sum_congr (by ext; simp)
  intro leftOrder _
  conv_rhs =>
    rw [← exactPermutationUniform_sum_mul
      (T := {j : M // j ∈ exactRight coordinate partition})
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactLeft coordinate partition}) : ℝ)))]
  apply Finset.sum_congr (by ext; simp)
  intro rightOrder _
  conv_rhs =>
    rw [← exactPrefixUniform_sum_mul
      (exactLeft coordinate partition).card
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactLeft coordinate partition}) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactRight coordinate partition}) : ℝ)))]
  apply Finset.sum_congr (by ext; simp)
  intro leftCut _
  conv_rhs =>
    rw [← exactPrefixUniform_sum_mul
      (exactRight coordinate partition).card
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactLeft coordinate partition}) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactRight coordinate partition}) : ℝ)) *
        (1 / ((exactLeft coordinate partition).card + 1 : ℝ)))]
  apply Finset.sum_congr (by ext; simp)
  intro rightCut _
  simp only [exactSeedWeight]
  congr 2
  congr 3
  · apply congrArg (fun k : ℕ => (k : ℝ))
    exact exactFintypeCard_eq _ _
  · exact exactFintypeCard_eq _ _

end

noncomputable section

open scoped BigOperators

def HasExponentialBound (v : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, v n ≤ C * Real.exp (-c * (n : ℝ))

def HasSubexponentialWitness (v : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ C : ℝ, 0 < C →
    ∃ n : ℕ, C * Real.exp (-c * (n : ℝ)) < v n

theorem not_hasExponentialBound_iff (v : ℕ → ℝ) :
    ¬ HasExponentialBound v ↔ HasSubexponentialWitness v := by
  simp [HasExponentialBound, HasSubexponentialWitness]

theorem arbitrarily_large_witness_of_not_hasExponentialBound
    {v : ℕ → ℝ}
    (hv : ∀ n : ℕ, v n ≤ 1)
    (h_no_bound : ¬ HasExponentialBound v)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ Real.exp (-c * (n : ℝ)) < v n := by
  have h_witness := (not_hasExponentialBound_iff v).mp h_no_bound
  obtain ⟨n, hn⟩ :=
    h_witness c hc (Real.exp (c * (N : ℝ))) (Real.exp_pos _)
  have hN : N < n := by
    by_contra h_not
    have hnN : n ≤ N := Nat.le_of_not_gt h_not
    have hnN_real : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    have h_nonneg : 0 ≤ c * ((N : ℝ) - (n : ℝ)) :=
      mul_nonneg hc.le (sub_nonneg.mpr hnN_real)
    have h_lower :
        1 ≤ Real.exp (c * (N : ℝ)) * Real.exp (-c * (n : ℝ)) := by
      calc
        1 ≤ Real.exp (c * ((N : ℝ) - (n : ℝ))) :=
          Real.one_le_exp h_nonneg
        _ = Real.exp (c * (N : ℝ)) * Real.exp (-c * (n : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    linarith [hv n]
  refine ⟨n, hN, ?_⟩
  have h_prefactor : 1 ≤ Real.exp (c * (N : ℝ)) :=
    Real.one_le_exp (mul_nonneg hc.le (Nat.cast_nonneg _))
  calc
    Real.exp (-c * (n : ℝ)) =
        1 * Real.exp (-c * (n : ℝ)) := by rw [one_mul]
    _ ≤ Real.exp (c * (N : ℝ)) * Real.exp (-c * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right h_prefactor (Real.exp_pos _).le
    _ < v n := hn

end

noncomputable section

open scoped BigOperators

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def StandardQuantumParallelRepetition (G : Game X Y A B) : Prop :=
  entangledValue G < 1 →
    HasExponentialBound (repeatedEntangledValue G)

end

noncomputable section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker

theorem sum_positive_difference_eq_totalVariation
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∑ i, p i) = 1)
    (hq : (∑ i, q i) = 1) :
    (∑ i, max (p i - q i) 0) = finiteTotalVariation p q := by
  classical
  have hpoint (x : ℝ) : max x 0 = (|x| + x) / 2 := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx, abs_of_nonneg hx]
      ring
    · have hxneg : x < 0 := lt_of_not_ge hx
      rw [max_eq_right hxneg.le, abs_of_neg hxneg]
      ring
  have hzero : (∑ i, (p i - q i)) = 0 := by
    rw [Finset.sum_sub_distrib, hp, hq, sub_self]
  unfold finiteTotalVariation
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hzero, add_zero]

theorem finiteTotalVariation_comm
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) :
    finiteTotalVariation p q = finiteTotalVariation q p := by
  unfold finiteTotalVariation
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact abs_sub_comm (p i) (q i)

theorem expectation_le_add_totalVariation
    {ι : Type*} [Fintype ι]
    (p q f : ι → ℝ)
    (hp : (∑ i, p i) = 1)
    (hq : (∑ i, q i) = 1)
    (U : ℝ)
    (hfzero : ∀ i, 0 ≤ f i)
    (hfupper : ∀ i, f i ≤ U) :
    (∑ i, p i * f i) ≤
      (∑ i, q i * f i) + U * finiteTotalVariation p q := by
  classical
  have hterm (i : ι) :
      (p i - q i) * f i ≤ U * max (p i - q i) 0 := by
    by_cases hi : 0 ≤ p i - q i
    · rw [max_eq_left hi]
      nlinarith [mul_nonneg hi (sub_nonneg.mpr (hfupper i))]
    · have hineg : p i - q i < 0 := lt_of_not_ge hi
      rw [max_eq_right hineg.le]
      simp only [mul_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hineg.le (hfzero i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hpositive := sum_positive_difference_eq_totalVariation p q hp hq
  calc
    (∑ i, p i * f i) =
        (∑ i, q i * f i) + ∑ i, (p i - q i) * f i := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ ≤ (∑ i, q i * f i) +
          ∑ i, U * max (p i - q i) 0 := by
      linarith
    _ = (∑ i, q i * f i) +
          U * finiteTotalVariation p q := by
      rw [← Finset.mul_sum, hpositive]

theorem winning_expectation_transfer
    {ι : Type*} [Fintype ι]
    (p q win : ι → ℝ)
    (hp : (∑ i, p i) = 1)
    (hq : (∑ i, q i) = 1)
    (hzero : ∀ i, 0 ≤ win i)
    (hone : ∀ i, win i ≤ 1) :
    (∑ i, q i * win i) - finiteTotalVariation p q ≤
      ∑ i, p i * win i := by
  have h := expectation_le_add_totalVariation
    q p win hq hp (1 : ℝ) hzero hone
  rw [← finiteTotalVariation_comm p q] at h
  norm_num at h ⊢
  linarith

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

section ActualSharedFlag

variable {X Y A B dA dB J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
variable [Fintype J] [DecidableEq J]

def pureVerifierEffect
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB)
    (x : X) (y : Y) : Matrix (dA × dB) (dA × dB) ℂ :=
  (pureVectorStrategy G z hz PA PB).winningEffect x y

theorem pureVectorWinningProbability_eq
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB) :
    (pureVectorStrategy G z hz PA PB).winProbability =
      ∑ x : X, ∑ y : Y, G.questionWeight x y *
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := dA × dB) (𝕜 := ℂ)
            (pureVerifierEffect G z hz PA PB x y)) z := by
  classical
  rw [(pureVectorStrategy G z hz PA PB).winProbability_eq_winningEffect_born]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact pureDensityMatrix_trace_mul z hz
    (pureVerifierEffect G z hz PA PB x y)

def flaggedQuestionWeight
    (G : Game X Y A B) (flagWeight : J → ℝ)
    (ω : J × (X × Y)) : ℝ :=
  flagWeight ω.1 * G.questionWeight ω.2.1 ω.2.2

omit [Fintype J] [DecidableEq J] in

theorem flaggedQuestionWeight_nonneg
    (G : Game X Y A B) (flagWeight : J → ℝ)
    (nonnegative : ∀ j, 0 ≤ flagWeight j)
    (ω : J × (X × Y)) :
    0 ≤ flaggedQuestionWeight G flagWeight ω :=
  mul_nonneg (nonnegative ω.1)
    (G.weight_nonneg ω.2.1 ω.2.2)

omit [DecidableEq J] in

theorem flaggedQuestionWeight_sum
    (G : Game X Y A B) (flagWeight : J → ℝ)
    (normalized : (∑ j, flagWeight j) = 1) :
    (∑ ω : J × (X × Y),
      flaggedQuestionWeight G flagWeight ω) = 1 := by
  classical
  simp [flaggedQuestionWeight, Fintype.sum_prod_type,
    ← Finset.mul_sum, G.weight_normalized, normalized]

end ActualSharedFlag

end

noncomputable section

open Filter
open scoped Topology

def universalErrorCeiling (K₀ : ℝ) : ℝ :=
  K₀ * (1 + (2 : ℝ) ^ (1 / 6 : ℝ)) + 2

def totalSamplingLoss (K₀ α η lam : ℝ) : ℝ :=
  5 * lam +
    2 * (K₀ * (α ^ (1 / 12 : ℝ) +
        (32 * η) ^ (1 / 12 : ℝ)) +
      Real.sqrt (8 * η) + universalErrorCeiling K₀ * lam)

def roundedWinningLowerBound (ε K₀ α η lam : ℝ) : ℝ :=
  1 - ε / 2 - totalSamplingLoss K₀ α η lam

theorem totalSamplingLoss_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (K₀ : ℝ) {α η lam : ι → ℝ}
    (hα : Tendsto α l (𝓝 0))
    (hη : Tendsto η l (𝓝 0))
    (hlam : Tendsto lam l (𝓝 0)) :
    Tendsto (fun i => totalSamplingLoss K₀ (α i) (η i) (lam i))
      l (𝓝 0) := by
  have hαroot :
      Tendsto (fun i => (α i) ^ (1 / 12 : ℝ)) l (𝓝 0) :=
    hα.rpow_const_nhds_zero (by norm_num)
  have hηscaled : Tendsto (fun i => 32 * η i) l (𝓝 0) := by
    simpa using hη.const_mul (32 : ℝ)
  have hηroot :
      Tendsto (fun i => (32 * η i) ^ (1 / 12 : ℝ)) l (𝓝 0) :=
    hηscaled.rpow_const_nhds_zero (by norm_num)
  have hηeight : Tendsto (fun i => 8 * η i) l (𝓝 0) := by
    simpa using hη.const_mul (8 : ℝ)
  have hsqrt : Tendsto (fun i => Real.sqrt (8 * η i)) l (𝓝 0) := by
    simpa using hηeight.sqrt
  have hquantum :
      Tendsto
        (fun i => K₀ * ((α i) ^ (1 / 12 : ℝ) +
          (32 * η i) ^ (1 / 12 : ℝ))) l (𝓝 0) := by
    simpa using (hαroot.add hηroot).const_mul K₀
  have hceiling :
      Tendsto (fun i => universalErrorCeiling K₀ * lam i)
        l (𝓝 0) := by
    simpa using hlam.const_mul (universalErrorCeiling K₀)
  have hinner :
      Tendsto
        (fun i => K₀ * ((α i) ^ (1 / 12 : ℝ) +
            (32 * η i) ^ (1 / 12 : ℝ)) +
          Real.sqrt (8 * η i) + universalErrorCeiling K₀ * lam i)
        l (𝓝 0) := by
    simpa using (hquantum.add hsqrt).add hceiling
  have hclassical : Tendsto (fun i => 5 * lam i) l (𝓝 0) := by
    simpa using hlam.const_mul (5 : ℝ)
  have hdouble :
      Tendsto
        (fun i => 2 *
          (K₀ * ((α i) ^ (1 / 12 : ℝ) +
              (32 * η i) ^ (1 / 12 : ℝ)) +
            Real.sqrt (8 * η i) + universalErrorCeiling K₀ * lam i))
        l (𝓝 0) := by
    simpa using hinner.const_mul (2 : ℝ)
  simpa [totalSamplingLoss] using hclassical.add hdouble

theorem totalSamplingLoss_eventually_lt
    {ι : Type*} {l : Filter ι}
    (K₀ : ℝ) {α η lam : ι → ℝ}
    (hα : Tendsto α l (𝓝 0))
    (hη : Tendsto η l (𝓝 0))
    (hlam : Tendsto lam l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, totalSamplingLoss K₀ (α i) (η i) (lam i) < ε :=
  (totalSamplingLoss_tendsto_zero K₀ hα hη hlam).eventually
    (gt_mem_nhds hε)

theorem source_equation_twenty_nine_contradiction
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (S : Strategy G)
    (K₀ α η lam : ℝ)
    (hbound :
      roundedWinningLowerBound (1 - entangledValue G)
        K₀ α η lam ≤ S.winProbability)
    (herror :
      totalSamplingLoss K₀ α η lam < (1 - entangledValue G) / 2) :
    False := by
  have hsup : S.winProbability ≤ entangledValue G := by
    unfold entangledValue
    exact le_csSup (winProbabilities_bddAbove G) ⟨S, rfl⟩
  unfold roundedWinningLowerBound at hbound
  linarith

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem matched_payoff_discard_le
    {ι : Type*} [Fintype ι]
    (weight payoff : ι → ℝ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (payoff_le_one : ∀ i, payoff i ≤ 1)
    (matched : ι → Bool) :
    (∑ i, weight i * payoff i) -
        (∑ i, weight i * if matched i then 0 else 1) ≤
      ∑ i, weight i * if matched i then payoff i else 0 := by
  classical
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : matched i = true
  · simp [hi]
  · have hone := payoff_le_one i
    simp only [Bool.not_eq_true] at hi
    simp [hi]
    nlinarith [mul_nonneg (nonnegative i)
      (sub_nonneg.mpr hone)]

end

noncomputable section

open scoped BigOperators

theorem squared_state_triangle
    {E : Type*} [NormedAddCommGroup E]
    (gamma psi phi : E) :
    ‖gamma - phi‖ ^ 2 ≤
      2 * (‖gamma - psi‖ ^ 2 + ‖psi - phi‖ ^ 2) := by
  have hsplit : gamma - phi = (gamma - psi) + (psi - phi) := by
    abel
  have htriangle :
      ‖gamma - phi‖ ≤ ‖gamma - psi‖ + ‖psi - phi‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  have hnonneg : 0 ≤ ‖gamma - phi‖ := norm_nonneg _
  have ha : 0 ≤ ‖gamma - psi‖ := norm_nonneg _
  have hb : 0 ≤ ‖psi - phi‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖gamma - psi‖ - ‖psi - phi‖)]

theorem source_equation_twenty_one
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (weight : ι → ℝ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (gamma psi phi : ι → E)
    (η : ℝ)
    (hgamma : (∑ i, weight i * ‖gamma i - psi i‖ ^ 2) ≤ 8 * η)
    (hphi : (∑ i, weight i * ‖psi i - phi i‖ ^ 2) ≤ 8 * η) :
    (∑ i, weight i * ‖gamma i - phi i‖ ^ 2) ≤ 32 * η := by
  classical
  calc
    (∑ i, weight i * ‖gamma i - phi i‖ ^ 2) ≤
        ∑ i, weight i *
          (2 * (‖gamma i - psi i‖ ^ 2 + ‖psi i - phi i‖ ^ 2)) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left
            (squared_state_triangle (gamma i) (psi i) (phi i))
            (nonnegative i)
    _ = 2 *
          ((∑ i, weight i * ‖gamma i - psi i‖ ^ 2) +
           (∑ i, weight i * ‖psi i - phi i‖ ^ 2)) := by
          calc
            (∑ i, weight i *
              (2 * (‖gamma i - psi i‖ ^ 2 + ‖psi i - phi i‖ ^ 2))) =
                ∑ i, (2 * (weight i * ‖gamma i - psi i‖ ^ 2) +
                  2 * (weight i * ‖psi i - phi i‖ ^ 2)) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
            _ = _ := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
              ring
    _ ≤ 32 * η := by linarith

theorem weighted_rpow_mean_le
    {ι : Type*} [Fintype ι]
    (weight value : ι → ℝ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i, weight i) = 1)
    (value_nonnegative : ∀ i, 0 ≤ value i)
    {r : ℝ} (hrzero : 0 ≤ r) (hrone : r ≤ 1) :
    (∑ i, weight i * value i ^ r) ≤
      (∑ i, weight i * value i) ^ r := by
  classical
  simpa [smul_eq_mul] using
    (Real.concaveOn_rpow hrzero hrone).le_map_sum
      (t := Finset.univ)
      (w := weight)
      (p := value)
      (fun i _ => nonnegative i)
      normalized
      (fun i _ => value_nonnegative i)

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem fullHistoryRemaining_insert_conditioned
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n) :
    fullHistoryRemaining n (insert i D) L =
      fullHistoryRemaining n D (insert i L) := by
  ext j
  simp only [fullHistoryRemaining, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_insert]
  tauto

def fullHistoryRemainingInsertedEquiv
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n) :
    {j : Fin n // j ∈ fullHistoryRemaining n (insert i D) L} ≃
      {j : Fin n // j ∈ fullHistoryRemaining n D (insert i L)} :=
  Equiv.subtypeEquivRight fun j => by
    rw [fullHistoryRemaining_insert_conditioned D L i]

def fullCoordinateAnswerExtension
    {T : Type*} {n : ℕ}
    (D : Finset (Fin n)) (i : Fin n)
    (α : {j : Fin n // j ∈ D} → T) (a : T) :
    {j : Fin n // j ∈ insert i D} → T := by
  classical
  intro j
  by_cases hj : (j : Fin n) = i
  · exact a
  · exact α ⟨j, (Finset.mem_insert.mp j.property).resolve_left hj⟩

def fullCoordinateAnswerExtensionEquiv
    {T : Type*} [Fintype T] {n : ℕ}
    (D : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D) :
    (({j : Fin n // j ∈ D} → T) × T) ≃
      ({j : Fin n // j ∈ insert i D} → T) where
  toFun t := fullCoordinateAnswerExtension D i t.1 t.2
  invFun α :=
    (fun j => α ⟨j, Finset.mem_insert_of_mem j.property⟩,
      α ⟨i, Finset.mem_insert_self i D⟩)
  left_inv t := by
    rcases t with ⟨α, a⟩
    apply Prod.ext
    · funext j
      have hj : (j : Fin n) ≠ i := by
        intro he
        exact hiD (he ▸ j.property)
      simp [fullCoordinateAnswerExtension, hj]
    · simp [fullCoordinateAnswerExtension]
  right_inv α := by
    funext j
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, Finset.mem_insert_self i D⟩ :
            {j : Fin n // j ∈ insert i D}) := Subtype.ext hj
      subst j
      simp [fullCoordinateAnswerExtension]
    · simp [fullCoordinateAnswerExtension, hj]

def fullCoordinateInsertedHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y) :
    FullSubsetHistory X Y n (insert i D) L := by
  classical
  refine ⟨
    fullCoordinateAnswerExtension D i r.aliceConditioned x,
    fullCoordinateAnswerExtension D i r.bobConditioned y,
    r.aliceRevealed,
    fun j => r.bobRemaining ⟨j, ?_⟩⟩
  rw [← fullHistoryRemaining_insert_conditioned D L i]
  exact j.property

def fullCoordinateBaseOfInsertedHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullSubsetHistory X Y n (insert i D) L) :
    FullCoordinateRevealHistory X Y n D L i := by
  refine ⟨
    fun j => h.aliceConditioned
      ⟨j, Finset.mem_insert_of_mem j.property⟩,
    fun j => h.bobConditioned
      ⟨j, Finset.mem_insert_of_mem j.property⟩,
    h.aliceRevealed,
    fun j => h.bobRemaining ⟨j, ?_⟩⟩
  rw [fullHistoryRemaining_insert_conditioned D L i]
  exact j.property

def fullCoordinateInsertedHistoryEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) :
    (FullCoordinateRevealHistory X Y n D L i × X × Y) ≃
      FullSubsetHistory X Y n (insert i D) L where
  toFun t := fullCoordinateInsertedHistory D L i t.1 t.2.1 t.2.2
  invFun h :=
    (fullCoordinateBaseOfInsertedHistory D L i h,
      h.aliceConditioned ⟨i, Finset.mem_insert_self i D⟩,
      h.bobConditioned ⟨i, Finset.mem_insert_self i D⟩)
  left_inv t := by
    rcases t with ⟨r, x, y⟩
    apply Prod.ext
    · apply FullCoordinateRevealHistory.ext
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          exact hiD (he ▸ j.property)
        simp [fullCoordinateBaseOfInsertedHistory,
          fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension, hj]
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          exact hiD (he ▸ j.property)
        simp [fullCoordinateBaseOfInsertedHistory,
          fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension, hj]
      · rfl
      · rfl
    · apply Prod.ext <;>
        simp [fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension]
  right_inv h := by
    apply FullSubsetHistory.ext
    · funext j
      by_cases hj : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i D⟩ :
              {j : Fin n // j ∈ insert i D}) := Subtype.ext hj
        subst j
        simp [fullCoordinateInsertedHistory,
          fullCoordinateBaseOfInsertedHistory,
          fullCoordinateAnswerExtension]
      · simp [fullCoordinateInsertedHistory,
          fullCoordinateBaseOfInsertedHistory,
          fullCoordinateAnswerExtension, hj]
    · funext j
      by_cases hj : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i D⟩ :
              {j : Fin n // j ∈ insert i D}) := Subtype.ext hj
        subst j
        simp [fullCoordinateInsertedHistory,
          fullCoordinateBaseOfInsertedHistory,
          fullCoordinateAnswerExtension]
      · simp [fullCoordinateInsertedHistory,
          fullCoordinateBaseOfInsertedHistory,
          fullCoordinateAnswerExtension, hj]
    · rfl
    · rfl

section InsertedWeights

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem fullCoordinateInsertedHistory_weight
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y) :
    fullHistoryWeight G (fullCoordinateInsertedHistory D L i r x y) =
      fullCoordinateBaseWeight G D L i r * G.questionWeight x y := by
  classical
  have hremaining :
      (∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n (insert i D) L},
        G.marginalY
          ((fullCoordinateInsertedHistory D L i r x y).bobRemaining j)) =
      ∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)},
        G.marginalY (r.bobRemaining j) := by
    let e := fullHistoryRemainingInsertedEquiv D L i
    calc
      (∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n (insert i D) L},
        G.marginalY
          ((fullCoordinateInsertedHistory D L i r x y).bobRemaining j)) =
        ∏ j : {j : Fin n //
          j ∈ fullHistoryRemaining n (insert i D) L},
          G.marginalY (r.bobRemaining (e j)) := by
            apply Finset.prod_congr rfl
            intro j _
            rfl
      _ = _ := e.prod_comp (fun j => G.marginalY (r.bobRemaining j))
  have hpair (j : {j : Fin n // j ∈ D}) :
      G.questionWeight
        ((fullCoordinateInsertedHistory D L i r x y).aliceConditioned
          ⟨j, Finset.mem_insert_of_mem j.property⟩)
        ((fullCoordinateInsertedHistory D L i r x y).bobConditioned
          ⟨j, Finset.mem_insert_of_mem j.property⟩) =
      G.questionWeight (r.aliceConditioned j) (r.bobConditioned j) := by
    have hj : (j : Fin n) ≠ i := by
      intro he
      exact hiD (he ▸ j.property)
    simp [fullCoordinateInsertedHistory,
      fullCoordinateAnswerExtension, hj]
  unfold fullHistoryWeight fullCoordinateBaseWeight
  change
    (∏ j : {j : Fin n // j ∈ insert i D},
      G.questionWeight
        ((fullCoordinateInsertedHistory D L i r x y).aliceConditioned j)
        ((fullCoordinateInsertedHistory D L i r x y).bobConditioned j)) *
    (∏ j : {j : Fin n // j ∈ L},
      G.marginalX (r.aliceRevealed j)) *
    (∏ j : {j : Fin n //
      j ∈ fullHistoryRemaining n (insert i D) L},
      G.marginalY
        ((fullCoordinateInsertedHistory D L i r x y).bobRemaining j)) = _
  rw [finsetSubtype_prod_insert D i hiD]
  rw [hremaining]
  simp_rw [hpair]
  simp [fullCoordinateInsertedHistory,
    fullCoordinateAnswerExtension]
  ring

theorem conditionedAliceEffect_insert_eq_coordinate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D)
    (α : {j : Fin n // j ∈ D} → A)
    (a : A) (xs : Fin n → X) :
    conditionedAliceEffect G n S (insert i D)
      (fullCoordinateAnswerExtension D i α a) xs =
      conditionedAliceCoordinateEffect G n S D α xs i a := by
  classical
  unfold conditionedAliceEffect conditionedAliceCoordinateEffect
  apply Finset.sum_congr rfl
  intro answers _
  have hiff :
      (∀ (j : Fin n) (hj : j ∈ insert i D),
        answers j = fullCoordinateAnswerExtension D i α a ⟨j, hj⟩) ↔
      ((∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
        answers i = a) := by
    constructor
    · intro h
      constructor
      · intro j hj
        have hji : j ≠ i := by
          intro he
          exact hiD (he ▸ hj)
        simpa [fullCoordinateAnswerExtension, hji]
          using h j (Finset.mem_insert_of_mem hj)
      · simpa [fullCoordinateAnswerExtension]
          using h i (Finset.mem_insert_self i D)
    · rintro ⟨hD, ha⟩ j hj
      by_cases hji : j = i
      · subst j
        simpa [fullCoordinateAnswerExtension] using ha
      · have hjD := (Finset.mem_insert.mp hj).resolve_left hji
        simpa [fullCoordinateAnswerExtension, hji] using hD j hjD
  by_cases h :
      ∀ (j : Fin n) (hj : j ∈ insert i D),
        answers j = fullCoordinateAnswerExtension D i α a ⟨j, hj⟩
  · simp only [if_pos h, if_pos (hiff.mp h)]
  · have hnot := mt hiff.mpr h
    simp only [if_neg h, if_neg hnot]

theorem conditionedBobEffect_insert_eq_coordinate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D)
    (β : {j : Fin n // j ∈ D} → B)
    (b : B) (ys : Fin n → Y) :
    conditionedBobEffect G n S (insert i D)
      (fullCoordinateAnswerExtension D i β b) ys =
      conditionedBobCoordinateEffect G n S D β ys i b := by
  classical
  unfold conditionedBobEffect conditionedBobCoordinateEffect
  apply Finset.sum_congr rfl
  intro answers _
  have hiff :
      (∀ (j : Fin n) (hj : j ∈ insert i D),
        answers j = fullCoordinateAnswerExtension D i β b ⟨j, hj⟩) ↔
      ((∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
        answers i = b) := by
    constructor
    · intro h
      constructor
      · intro j hj
        have hji : j ≠ i := by
          intro he
          exact hiD (he ▸ hj)
        simpa [fullCoordinateAnswerExtension, hji]
          using h j (Finset.mem_insert_of_mem hj)
      · simpa [fullCoordinateAnswerExtension]
          using h i (Finset.mem_insert_self i D)
    · rintro ⟨hD, hb⟩ j hj
      by_cases hji : j = i
      · subst j
        simpa [fullCoordinateAnswerExtension] using hb
      · have hjD := (Finset.mem_insert.mp hj).resolve_left hji
        simpa [fullCoordinateAnswerExtension, hji] using hD j hjD
  by_cases h :
      ∀ (j : Fin n) (hj : j ∈ insert i D),
        answers j = fullCoordinateAnswerExtension D i β b ⟨j, hj⟩
  · simp only [if_pos h, if_pos (hiff.mp h)]
  · have hnot := mt hiff.mpr h
    simp only [if_neg h, if_neg hnot]

end InsertedWeights

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem conditionedCoordinateEffects_born_expansion
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B)
    (xs : Fin n → X) (ys : Fin n → Y)
    (i : Fin n) (a : A) (b : B) :
    bornTracePairing S.state.matrix
        (conditionedAliceCoordinateEffect G n S D α xs i a)
        (conditionedBobCoordinateEffect G n S D β ys i b) =
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        if (∀ (j : Fin n) (hj : j ∈ D), aa j = α ⟨j, hj⟩) ∧
          aa i = a then
          if (∀ (j : Fin n) (hj : j ∈ D), bb j = β ⟨j, hj⟩) ∧
            bb i = b then S.outcomeProbability xs ys aa bb else 0
        else 0 := by
  classical
  simp only [conditionedAliceCoordinateEffect,
    conditionedBobCoordinateEffect,
    map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro aa _
  split_ifs with ha
  · apply Finset.sum_congr rfl
    intro bb _
    split_ifs with hb
    · rfl
    · exact map_zero _
  · simp

end

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

def normalizedPureVector
    {d : Type*} [Fintype d]
    (z : EuclideanSpace ℂ d) : EuclideanSpace ℂ d :=
  ((‖z‖⁻¹ : ℝ) : ℂ) • z

theorem quadraticExpectation_normalizedPureVector
    {d : Type*} [Fintype d]
    (W : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d)
    (z : EuclideanSpace ℂ d) :
    quadraticExpectation W (normalizedPureVector z) =
      quadraticExpectation W z / ‖z‖ ^ 2 := by
  unfold quadraticExpectation normalizedPureVector
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp [Complex.mul_re, div_eq_mul_inv, pow_two]
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  · field_simp

end

noncomputable section

open scoped BigOperators

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exists_repeatedStrategy_of_lt_entangledValue
    (G : Game X Y A B) {n : ℕ} {r : ℝ}
    (hr : 0 < r)
    (hvalue : r < repeatedEntangledValue G n) :
    ∃ S : Strategy (G.repeat n), r < S.winProbability := by
  let values : Set ℝ :=
    Set.range (Strategy.winProbability (G := G.repeat n))
  have hnonempty : values.Nonempty := by
    by_contra hempty
    have heq : values = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    have hzero : repeatedEntangledValue G n = 0 := by
      change sSup values = 0
      rw [heq, Real.sSup_empty]
    linarith
  have hs : r < sSup values := by
    exact hvalue
  obtain ⟨v, ⟨S, hS⟩, hv⟩ := exists_lt_of_lt_csSup hnonempty hs
  subst v
  exact ⟨S, hv⟩

theorem exists_purifiedRepeatedStrategy_of_lt_entangledValue
    (G : Game X Y A B) {n : ℕ} {r : ℝ}
    (hr : 0 < r)
    (hvalue : r < repeatedEntangledValue G n) :
    ∃ S : Strategy (G.repeat n),
      r < (purifiedStrategy S).winProbability := by
  obtain ⟨S, hS⟩ :=
    exists_repeatedStrategy_of_lt_entangledValue G hr hvalue
  refine ⟨S, ?_⟩
  rwa [purifiedStrategy_winProbability]

theorem arbitrarily_large_purifiedRepeatedStrategy_of_subexponentialWitness
    (G : Game X Y A B)
    (hwitness : HasSubexponentialWitness (repeatedEntangledValue G))
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ n : ℕ, N < n ∧
      ∃ S : Strategy (G.repeat n),
        Real.exp (-c * (n : ℝ)) <
          (purifiedStrategy S).winProbability := by
  have hno : ¬ HasExponentialBound (repeatedEntangledValue G) :=
    (not_hasExponentialBound_iff (repeatedEntangledValue G)).mpr hwitness
  have hbounded (n : ℕ) : repeatedEntangledValue G n ≤ 1 :=
    entangledValue_le_one (G.repeat n)
  obtain ⟨n, hn, hvalue⟩ :=
    arbitrarily_large_witness_of_not_hasExponentialBound
      hbounded hno hc N
  exact ⟨n, hn,
    exists_purifiedRepeatedStrategy_of_lt_entangledValue G
      (Real.exp_pos _) hvalue⟩

theorem postselection_log_cost_le
    {θ p : ℝ} (hθ : 0 < θ) (hθp : θ ≤ p) :
    Real.log (1 / p) ≤ Real.log (1 / θ) := by
  have hp : 0 < p := lt_of_lt_of_le hθ hθp
  have hinv : 1 / p ≤ 1 / θ := by
    exact one_div_le_one_div_of_le hθ hθp
  exact Real.log_le_log (by positivity : 0 < 1 / p) hinv

theorem greedy_terminal_of_log_cost
    {θ η : ℝ} {T : ℕ}
    (hθ : 0 < θ)
    (hη_one : η ≤ 1)
    (hcost : Real.log (1 / θ) < η * (T : ℝ)) :
    (1 - η) ^ T < θ := by
  have hbase : 1 - η ≤ Real.exp (-η) := by
    have h := Real.add_one_le_exp (-η)
    linarith
  have hpow :
      (1 - η) ^ T ≤ Real.exp (-η) ^ T :=
    pow_le_pow_left₀ (sub_nonneg.mpr hη_one) hbase T
  have hlog : -η * (T : ℝ) < Real.log θ := by
    rw [one_div, Real.log_inv] at hcost
    linarith
  calc
    (1 - η) ^ T ≤ Real.exp (-η) ^ T := hpow
    _ = Real.exp (-η * (T : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ < θ := (Real.exp_lt_exp.mpr hlog).trans_eq
      (Real.exp_log hθ)

theorem divisorStopping_nat_bound
    {n q : ℕ} (hq : 0 < q) (hqn : q ≤ n) :
    n < 2 * (n / q) * q := by
  have hT : 0 < n / q := by
    apply (Nat.le_div_iff_mul_le hq).2
    simpa using hqn
  have hnext : n < (n / q + 1) * q := by
    exact (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self (n / q))
  have hfactor : n / q + 1 ≤ 2 * (n / q) := by
    omega
  exact hnext.trans_le (Nat.mul_le_mul_right q hfactor)

theorem sourceRate_mul_lt_divisorStopping
    {n q : ℕ} (hq : 0 < q) (hqn : q ≤ n)
    {η : ℝ} (hη : 0 < η) :
    (η / (4 * (q : ℝ))) * (n : ℝ) <
      η * ((n / q : ℕ) : ℝ) := by
  have hcast :
      (n : ℝ) < 2 * ((n / q : ℕ) : ℝ) * (q : ℝ) := by
    exact_mod_cast divisorStopping_nat_bound hq hqn
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hT : 0 < ((n / q : ℕ) : ℝ) := by
    exact_mod_cast ((Nat.le_div_iff_mul_le hq).2 (by simpa using hqn) :
      1 ≤ n / q)
  have hrate : 0 < η / (4 * (q : ℝ)) := by positivity
  calc
    (η / (4 * (q : ℝ))) * (n : ℝ) <
        (η / (4 * (q : ℝ))) *
          (2 * ((n / q : ℕ) : ℝ) * (q : ℝ)) :=
      mul_lt_mul_of_pos_left hcast hrate
    _ = η * ((n / q : ℕ) : ℝ) / 2 := by
      field_simp
      ; ring
    _ < η * ((n / q : ℕ) : ℝ) := by
      have hpositive : 0 < η * ((n / q : ℕ) : ℝ) :=
        mul_pos hη hT
      linarith

theorem repeatedStrategy_exists_divisor_greedy_conditioning
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    {η : ℝ} {q : ℕ}
    (hη : 0 < η) (hη_one : η ≤ 1)
    (hq : 0 < q) (hqn : q ≤ n)
    (hwitness :
      Real.exp (-(η / (4 * (q : ℝ))) * (n : ℝ)) <
        S.winProbability) :
    ∃ D : Finset (Fin n),
      D.card < n / q ∧
      S.winProbability ≤
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D) ∧
      (∑ i ∈ Finset.univ \ D,
        FiniteEventLaw.failureMass
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D i)
        <
      ((Finset.univ \ D).card : ℝ) *
        (η * (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D)) := by
  have hθ : 0 < S.winProbability :=
    lt_trans (Real.exp_pos _) hwitness
  have hlog :
      Real.log (1 / S.winProbability) <
        (η / (4 * (q : ℝ))) * (n : ℝ) := by
    have hlog' :
        -(η / (4 * (q : ℝ))) * (n : ℝ) <
          Real.log S.winProbability :=
      (Real.lt_log_iff_exp_lt hθ).mpr hwitness
    rw [one_div, Real.log_inv]
    linarith
  have hterminal :
      (1 - η) ^ (n / q) < S.winProbability := by
    apply greedy_terminal_of_log_cost hθ hη_one
    exact hlog.trans (sourceRate_mul_lt_divisorStopping hq hqn hη)
  apply repeatedStrategy_exists_greedy_conditioning
    G n S hθ hη hη_one (Nat.div_le_self n q) (le_refl _) hterminal

theorem divisor_greedy_card_mul_lt
    {n q : ℕ} (hq : 0 < q)
    {D : Finset (Fin n)} (hD : D.card < n / q) :
    D.card * q < n := by
  have hmul : D.card * q < (n / q) * q :=
    Nat.mul_lt_mul_of_pos_right hD hq
  exact hmul.trans_le (Nat.div_mul_le_self n q)

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

structure SourceHistoryFlag
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) where
  permutation : SourceRemainingPermutation D
  position : Fin (Finset.univ \ D).card
  history : FullCoordinateRevealHistory X Y n D
    (sourceRemainingPermutationPrefix D permutation position.castSucc)
    (sourceRemainingPermutationCoordinate D permutation position)
  aliceAnswer : {i : Fin n // i ∈ D} → A
  bobAnswer : {i : Fin n // i ∈ D} → B

abbrev SourceHistoryFlagTuple
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) :=
  Σ π : SourceRemainingPermutation D,
    Σ k : Fin (Finset.univ \ D).card,
      FullCoordinateRevealHistory X Y n D
        (sourceRemainingPermutationPrefix D π k.castSucc)
        (sourceRemainingPermutationCoordinate D π k) ×
      ({i : Fin n // i ∈ D} → A) ×
      ({i : Fin n // i ∈ D} → B)

def sourceHistoryFlagEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    SourceHistoryFlag X Y A B D ≃ SourceHistoryFlagTuple X Y A B D where
  toFun r := ⟨r.permutation, r.position,
    r.history, r.aliceAnswer, r.bobAnswer⟩
  invFun t := ⟨t.1, t.2.1,
    t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩
  left_inv r := by cases r; rfl
  right_inv t := by
    rcases t with ⟨π, k, r, α, β⟩
    rfl

noncomputable instance sourceHistoryFlagFintype
    {n : ℕ} (D : Finset (Fin n)) :
    Fintype (SourceHistoryFlag X Y A B D) := by
  classical
  exact Fintype.ofEquiv (SourceHistoryFlagTuple X Y A B D)
    (sourceHistoryFlagEquiv (X := X) (Y := Y)
      (A := A) (B := B) D).symm

theorem sourceHistoryFlag_sum
    {n : ℕ} (D : Finset (Fin n))
    (f : SourceHistoryFlag X Y A B D → ℝ) :
    (∑ r : SourceHistoryFlag X Y A B D, f r) =
      ∑ π : SourceRemainingPermutation D,
      ∑ k : Fin (Finset.univ \ D).card,
      ∑ r : FullCoordinateRevealHistory X Y n D
          (sourceRemainingPermutationPrefix D π k.castSucc)
          (sourceRemainingPermutationCoordinate D π k),
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        f ⟨π, k, r, α, β⟩ := by
  classical
  calc
    (∑ r : SourceHistoryFlag X Y A B D, f r) =
        ∑ t : SourceHistoryFlagTuple X Y A B D,
          f ((sourceHistoryFlagEquiv (X := X) (Y := Y)
            (A := A) (B := B) D).symm t) :=
      ((sourceHistoryFlagEquiv (X := X) (Y := Y)
        (A := A) (B := B) D).symm.sum_comp f).symm
    _ = _ := by
      simp [Fintype.sum_sigma, Fintype.sum_prod_type,
        sourceHistoryFlagEquiv]

def sourceHistoryPermutationPositionWeight
    {n : ℕ} (D : Finset (Fin n)) : ℝ :=
  1 / ((Fintype.card (SourceRemainingPermutation D) : ℝ) *
    ((Finset.univ \ D).card : ℝ))

def sourceHistoryRaw
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (r : SourceHistoryFlag X Y A B D) : ℝ :=
  sourceHistoryPermutationPositionWeight D *
    fullCoordinateBaseWeight G D
      (sourceRemainingPermutationPrefix D
        r.permutation r.position.castSucc)
      (sourceRemainingPermutationCoordinate D
        r.permutation r.position)
      r.history *
    fullCoordinateBaseWinIndicator G D
      (sourceRemainingPermutationPrefix D
        r.permutation r.position.castSucc)
      (sourceRemainingPermutationCoordinate D
        r.permutation r.position)
      r.history r.aliceAnswer r.bobAnswer

end

noncomputable section

open scoped BigOperators

section FiniteSamples

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

def postselectionMass
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) : ℝ :=
  law.eventMass (FiniteEventLaw.winEvent wins C)

omit [DecidableEq ι] in

theorem allWinMass_le_postselectionMass
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) :
    law.eventMass (FiniteEventLaw.winEvent wins Finset.univ) ≤
      postselectionMass law wins C :=
  law.allWinMass_le_partial wins C

omit [DecidableEq ι] in

theorem postselectionMass_le_one
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) :
    postselectionMass law wins C ≤ 1 := by
  calc
    postselectionMass law wins C ≤ law.eventMass Finset.univ :=
      law.eventMass_mono (Finset.subset_univ _)
    _ = 1 := law.eventMass_univ

def conditionalCoordinateFailure
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) (i : ι) : ℝ :=
  FiniteEventLaw.failureMass law wins C i /
    postselectionMass law wins C

def uniformRemainingFailure
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) : ℝ :=
  (∑ i ∈ Finset.univ \ C,
    conditionalCoordinateFailure law wins C i) /
    ((Finset.univ \ C).card : ℝ)

theorem uniformRemainingFailure_lt_of_failure_sum
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) {η : ℝ}
    (hp : 0 < postselectionMass law wins C)
    (hm : 0 < (Finset.univ \ C).card)
    (hfailure :
      (∑ i ∈ Finset.univ \ C,
        FiniteEventLaw.failureMass law wins C i) <
        ((Finset.univ \ C).card : ℝ) *
          (η * postselectionMass law wins C)) :
    uniformRemainingFailure law wins C < η := by
  have hmreal : 0 < ((Finset.univ \ C).card : ℝ) := by
    exact_mod_cast hm
  unfold uniformRemainingFailure conditionalCoordinateFailure
  rw [← Finset.sum_div]
  apply (div_lt_iff₀ hmreal).mpr
  apply (div_lt_iff₀ hp).mpr
  nlinarith

end FiniteSamples

section ActualRepeatedStrategy

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def repeatedPostselectionMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (C : Finset (Fin n)) : ℝ :=
  postselectionMass (strategyEventLaw (G.repeat n) S)
    (repeatedCoordinateWin G n) C

theorem repeated_winProbability_le_postselectionMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (C : Finset (Fin n)) :
    S.winProbability ≤ repeatedPostselectionMass G n S C := by
  rw [← repeated_allWinMass_eq G n S]
  exact allWinMass_le_postselectionMass
    (strategyEventLaw (G.repeat n) S) (repeatedCoordinateWin G n) C

theorem repeatedPostselectionMass_pos
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (C : Finset (Fin n))
    (hwin : 0 < S.winProbability) :
    0 < repeatedPostselectionMass G n S C :=
  lt_of_lt_of_le hwin
    (repeated_winProbability_le_postselectionMass G n S C)

theorem remainingCoordinates_card
    {n : ℕ} (C : Finset (Fin n)) :
    (Finset.univ \ C).card = n - C.card := by
  simp [Finset.card_sdiff_of_subset (Finset.subset_univ C)]

theorem repeatedStrategy_exists_conditioning
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    {η : ℝ} {q : ℕ}
    (hwin : 0 < S.winProbability)
    (hη : 0 < η) (hη_one : η ≤ 1)
    (hq : q ≤ n)
    (hterminal : (1 - η) ^ q < S.winProbability) :
    ∃ C : Finset (Fin n),
      C.card < q ∧
      S.winProbability ≤ repeatedPostselectionMass G n S C ∧
      0 < repeatedPostselectionMass G n S C ∧
      0 < (Finset.univ \ C).card ∧
      uniformRemainingFailure
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) C < η := by
  obtain ⟨C, hC, hmass, hfailure⟩ :=
    repeatedStrategy_exists_greedy_conditioning G n S
      hwin hη hη_one hq (le_refl _) hterminal
  have hremaining : 0 < (Finset.univ \ C).card := by
    rw [remainingCoordinates_card]
    omega
  have hp : 0 < repeatedPostselectionMass G n S C :=
    repeatedPostselectionMass_pos G n S C hwin
  refine ⟨C, hC, ?_, hp, hremaining, ?_⟩
  · simpa [repeatedPostselectionMass, postselectionMass] using hmass
  · apply uniformRemainingFailure_lt_of_failure_sum
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) C
      (by simpa [repeatedPostselectionMass] using hp)
      hremaining
    simpa [postselectionMass] using hfailure

end ActualRepeatedStrategy

end

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

theorem source_equation_nineteen_alice
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (hFcomplement : (1 - F).PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (hGcomplement : (1 - G).PosSemidef) :
    -bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G ≤
      Real.negMulLog (bornTracePairing ρ.matrix F G) :=
  matrixLogEntropy_born_lower_bound_left
    ρ F hF hFcomplement G hG hGcomplement

theorem source_equation_nineteen_bob
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (hFcomplement : (1 - F).PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (hGcomplement : (1 - G).PosSemidef) :
    -bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) ≤
      Real.negMulLog (bornTracePairing ρ.matrix F G) :=
  matrixLogEntropy_born_lower_bound_right
    ρ F hF hFcomplement G hG hGcomplement

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

section ActualFilters

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def postselectionLogCost
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  Real.log (1 / repeatedPostselectionMass G n S D)

def answerLogCost
    {A B : Type*} [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) : ℝ :=
  (D.card : ℝ) *
    Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))

def martingaleRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  (postselectionLogCost G n S D +
      answerLogCost (A := A) (B := B) D) /
    ((Finset.univ \ D).card : ℝ)

theorem answerCount_pos_of_postselection
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hp : 0 < repeatedPostselectionMass G n S D) :
    0 < fullHistoryAnswerCount (A := A) (B := B) D := by
  classical
  have hmass := fullHistoryAtomBornMass_sum G n S D ∅
    (Finset.empty_subset _)
  have hfirst :
      (∑ z : FullHistoryEntropyAtom X Y A B n D ∅,
        fullHistoryAtomCountingWeight G D ∅ z *
          fullHistoryAtomBornMass G n S D ∅ z) ≤
        ∑ z : FullHistoryEntropyAtom X Y A B n D ∅,
          fullHistoryAtomCountingWeight G D ∅ z := by
    apply Finset.sum_le_sum
    intro z _
    exact mul_le_of_le_one_right
      (fullHistoryAtomCountingWeight_nonneg G D ∅ z)
      (fullHistoryAtomBornMass_le_one G n S D ∅ z)
  have hsecond := fullHistoryAtomCountingWeight_sum_le G D ∅
  change 0 <
    (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) at hp
  linarith

theorem martingale_log_cost_eq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hp : 0 < repeatedPostselectionMass G n S D) :
    Real.log
        (fullHistoryAnswerCount (A := A) (B := B) D /
          repeatedPostselectionMass G n S D) =
      postselectionLogCost G n S D +
        answerLogCost (A := A) (B := B) D := by
  have hN := answerCount_pos_of_postselection G n S D hp
  calc
    Real.log
        (fullHistoryAnswerCount (A := A) (B := B) D /
          repeatedPostselectionMass G n S D) =
        Real.log (fullHistoryAnswerCount (A := A) (B := B) D) -
          Real.log (repeatedPostselectionMass G n S D) :=
            Real.log_div hN.ne' hp.ne'
    _ = (D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) *
            (Fintype.card B : ℝ)) -
          Real.log (repeatedPostselectionMass G n S D) := by
            rw [fullHistoryAnswerCount_eq, ← mul_pow, Real.log_pow]
    _ = postselectionLogCost G n S D +
          answerLogCost (A := A) (B := B) D := by
            simp only [postselectionLogCost,
              answerLogCost, one_div, Real.log_inv]
            ring

theorem aliceMartingaleEntropyBudget
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    (hp : 0 < repeatedPostselectionMass G n S D) :
    sourceUniformPermutationAverage D
        (sourcePermutationAliceEntropyIncrement G n S D) ≤
      repeatedPostselectionMass G n S D *
        martingaleRate G n S D := by
  have hbudget := sourceUniformPermutationAliceEntropyBudget
    G n S D hm hp
  change sourceUniformPermutationAverage D
    (sourcePermutationAliceEntropyIncrement G n S D) ≤
    repeatedPostselectionMass G n S D *
      Real.log
        (fullHistoryAnswerCount (A := A) (B := B) D /
          repeatedPostselectionMass G n S D) /
        ((Finset.univ \ D).card : ℝ) at hbudget
  rw [martingale_log_cost_eq G n S D hp] at hbudget
  simpa [martingaleRate, mul_div_assoc] using hbudget

end ActualFilters

section ActualPurificationHistories

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem bornWeighted_normalized_distance
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (fallback u v : E) (hfallback : ‖fallback‖ = 1) :
    ‖u‖ ^ 2 *
      ‖normalizeOrDefault fallback u -
        normalizeOrDefault fallback v‖ ^ 2 ≤
      4 * ‖u - v‖ ^ 2 := by
  by_cases hu : u = 0
  · simp [hu]
  · have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hdist := normalizeOrDefault_sub_le fallback u v hfallback hu
    have hscaled :
        ‖normalizeOrDefault fallback u -
          normalizeOrDefault fallback v‖ * ‖u‖ ≤
          2 * ‖u - v‖ :=
      (le_div_iff₀ hu_pos).mp hdist
    have hsquare := mul_self_le_mul_self
      (mul_nonneg (norm_nonneg _) (norm_nonneg u)) hscaled
    nlinarith [sq_nonneg
      (‖normalizeOrDefault fallback u -
        normalizeOrDefault fallback v‖ * ‖u‖),
      sq_nonneg (‖u - v‖)]

end ActualPurificationHistories

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem fullCoordinateInsertedHistory_winIndicator_eq
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (α : {j : Fin n // j ∈ D} → A) (a : A)
    (β : {j : Fin n // j ∈ D} → B) (b : B) :
    fullHistoryWinIndicator G
      (fullCoordinateInsertedHistory D L i r x y)
      (fullCoordinateAnswerExtension D i α a)
      (fullCoordinateAnswerExtension D i β b) =
      fullCoordinateBaseWinIndicator G D L i r α β *
        (if G.predicate x y a b = true then 1 else 0) := by
  classical
  have hiff :
      (∀ j : {j : Fin n // j ∈ insert i D},
        G.predicate
          ((fullCoordinateInsertedHistory D L i r x y).aliceConditioned j)
          ((fullCoordinateInsertedHistory D L i r x y).bobConditioned j)
          (fullCoordinateAnswerExtension D i α a j)
          (fullCoordinateAnswerExtension D i β b j) = true) ↔
      ((∀ j : {j : Fin n // j ∈ D},
        G.predicate (r.aliceConditioned j) (r.bobConditioned j)
          (α j) (β j) = true) ∧ G.predicate x y a b = true) := by
    constructor
    · intro h
      constructor
      · intro j
        have hji : (j : Fin n) ≠ i := by
          intro he
          exact hiD (he ▸ j.property)
        simpa [fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension, hji] using
          h ⟨j, Finset.mem_insert_of_mem j.property⟩
      · simpa [fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension] using
          h ⟨i, Finset.mem_insert_self i D⟩
    · rintro ⟨hD, hi⟩ j
      by_cases hji : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i D⟩ :
              {j : Fin n // j ∈ insert i D}) := Subtype.ext hji
        subst j
        simpa [fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension] using hi
      · have hjD : (j : Fin n) ∈ D :=
          (Finset.mem_insert.mp j.property).resolve_left hji
        simpa [fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension, hji] using hD ⟨j, hjD⟩
  change
    (if ∀ j : {j : Fin n // j ∈ insert i D},
      G.predicate
        ((fullCoordinateInsertedHistory D L i r x y).aliceConditioned j)
        ((fullCoordinateInsertedHistory D L i r x y).bobConditioned j)
        (fullCoordinateAnswerExtension D i α a j)
        (fullCoordinateAnswerExtension D i β b j) = true
      then (1 : ℝ) else 0) =
      (if ∀ j : {j : Fin n // j ∈ D},
        G.predicate (r.aliceConditioned j) (r.bobConditioned j)
          (α j) (β j) = true then (1 : ℝ) else 0) *
      (if G.predicate x y a b = true then (1 : ℝ) else 0)
  split_ifs with hall hD hi <;> aesop

def fullCoordinateInsertedHiddenAliceEquiv
    {X : Type*} {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n) :
    ({j : Fin n // j ∈ fullHistoryRemaining n (insert i D) L} → X) ≃
      ({j : Fin n // j ∈ fullHistoryRemaining n D (insert i L)} → X) where
  toFun hidden j :=
    hidden ((fullHistoryRemainingInsertedEquiv D L i).symm j)
  invFun hidden j := hidden (fullHistoryRemainingInsertedEquiv D L i j)
  left_inv hidden := by
    funext j
    simp
  right_inv hidden := by
    funext j
    simp

theorem fullCoordinateInsertedAliceQuestion_eq
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    fullHistoryAliceQuestion
      (fullCoordinateInsertedHistory D L i r x y)
      ((fullCoordinateInsertedHiddenAliceEquiv (X := X) D L i).symm hidden) =
      fullHistoryAliceQuestion
        (fullCoordinateNewHistory D L i r x) hidden := by
  classical
  funext j
  by_cases hjD : j ∈ D
  · have hji : j ≠ i := by
      intro he
      exact hiD (he ▸ hjD)
    simp [fullHistoryAliceQuestion, fullCoordinateInsertedHistory,
      fullCoordinateAnswerExtension, fullCoordinateNewHistory,
      hjD, hji]
  · by_cases hji : j = i
    · subst j
      simp [fullHistoryAliceQuestion, fullCoordinateInsertedHistory,
        fullCoordinateAnswerExtension, fullCoordinateNewHistory,
        hiD, hiL]
    · by_cases hjL : j ∈ L
      · simp [fullHistoryAliceQuestion, fullCoordinateInsertedHistory,
          fullCoordinateNewHistory,
          hjD, hji, hjL]
      · simp [fullHistoryAliceQuestion,                     fullCoordinateInsertedHiddenAliceEquiv,
          fullHistoryRemainingInsertedEquiv, hjD, hji, hjL]
        congr 1

theorem fullCoordinateInsertedHiddenAliceWeight_eq
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    fullHistoryHiddenAliceWeight G
      (fullCoordinateInsertedHistory D L i r x y)
      ((fullCoordinateInsertedHiddenAliceEquiv (X := X) D L i).symm hidden) =
      fullHistoryHiddenAliceWeight G
        (fullCoordinateNewHistory D L i r x) hidden := by
  classical
  let e := fullHistoryRemainingInsertedEquiv D L i
  unfold fullHistoryHiddenAliceWeight
  calc
    (∏ j : {j : Fin n //
      j ∈ fullHistoryRemaining n (insert i D) L},
      G.conditionalXGivenY
        ((fullCoordinateInsertedHistory D L i r x y).bobRemaining j)
        (((fullCoordinateInsertedHiddenAliceEquiv
          (X := X) D L i).symm hidden) j)) =
      ∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n (insert i D) L},
        G.conditionalXGivenY (r.bobRemaining (e j)) (hidden (e j)) := by
          apply Finset.prod_congr rfl
          intro j _
          rfl
    _ = ∏ j : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)},
        G.conditionalXGivenY (r.bobRemaining j) (hidden j) :=
      e.prod_comp (fun j =>
        G.conditionalXGivenY (r.bobRemaining j) (hidden j))
    _ = _ := rfl

theorem fullCoordinateInsertedBobQuestion_eq
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n // j ∈ L} → Y) :
    fullHistoryBobQuestion
      (fullCoordinateInsertedHistory D L i r x y) hidden =
      fullHistoryBobQuestion
        (fullCoordinateOldHistory D L i r y) hidden := by
  classical
  funext j
  by_cases hjD : j ∈ D
  · have hji : j ≠ i := by
      intro he
      exact hiD (he ▸ hjD)
    simp [fullHistoryBobQuestion, fullCoordinateInsertedHistory,
      fullCoordinateAnswerExtension, fullCoordinateOldHistory,
      hjD, hji]
  · by_cases hji : j = i
    · subst j
      simp [fullHistoryBobQuestion, fullCoordinateInsertedHistory,
        fullCoordinateAnswerExtension, fullCoordinateOldHistory,
        hiD, hiL]
    · by_cases hjL : j ∈ L
      · simp [fullHistoryBobQuestion,                     hjD, hji, hjL]
      · simp [fullHistoryBobQuestion, fullCoordinateInsertedHistory,
          fullCoordinateOldHistory,
          hjD, hji, hjL]

theorem fullCoordinateInsertedHiddenBobWeight_eq
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n // j ∈ L} → Y) :
    fullHistoryHiddenBobWeight G
      (fullCoordinateInsertedHistory D L i r x y) hidden =
    fullHistoryHiddenBobWeight G
        (fullCoordinateOldHistory D L i r y) hidden := by
  rfl

theorem fullCoordinateInsertedHistory_aliceFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (α : {j : Fin n // j ∈ D} → A) (a : A) :
    fullHistoryAliceFilter G n S (insert i D) L
      (fullCoordinateInsertedHistory D L i r x y)
      (fullCoordinateAnswerExtension D i α a) =
      fullCoordinateAliceRefinementEffect G n S D L i r α x a := by
  classical
  change
    (∑ hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n (insert i D) L} → X,
      fullHistoryHiddenAliceWeight G
        (fullCoordinateInsertedHistory D L i r x y) hidden •
      conditionedAliceEffect G n S (insert i D)
        (fullCoordinateAnswerExtension D i α a)
        (fullHistoryAliceQuestion
          (fullCoordinateInsertedHistory D L i r x y) hidden)) =
      ∑ hidden : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} → X,
        fullHistoryHiddenAliceWeight G
          (fullCoordinateNewHistory D L i r x) hidden •
        conditionedAliceCoordinateEffect G n S D α
          (fullHistoryAliceQuestion
            (fullCoordinateNewHistory D L i r x) hidden) i a
  calc
    (∑ hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n (insert i D) L} → X,
      fullHistoryHiddenAliceWeight G
        (fullCoordinateInsertedHistory D L i r x y) hidden •
      conditionedAliceEffect G n S (insert i D)
        (fullCoordinateAnswerExtension D i α a)
        (fullHistoryAliceQuestion
          (fullCoordinateInsertedHistory D L i r x y) hidden)) =
      ∑ hidden : {j : Fin n //
        j ∈ fullHistoryRemaining n D (insert i L)} → X,
        fullHistoryHiddenAliceWeight G
          (fullCoordinateInsertedHistory D L i r x y)
          ((fullCoordinateInsertedHiddenAliceEquiv
            (X := X) D L i).symm hidden) •
        conditionedAliceEffect G n S (insert i D)
          (fullCoordinateAnswerExtension D i α a)
          (fullHistoryAliceQuestion
            (fullCoordinateInsertedHistory D L i r x y)
            ((fullCoordinateInsertedHiddenAliceEquiv
              (X := X) D L i).symm hidden)) := by
        exact ((fullCoordinateInsertedHiddenAliceEquiv
          (X := X) D L i).symm.sum_comp
          (fun hidden =>
            fullHistoryHiddenAliceWeight G
              (fullCoordinateInsertedHistory D L i r x y) hidden •
            conditionedAliceEffect G n S (insert i D)
              (fullCoordinateAnswerExtension D i α a)
              (fullHistoryAliceQuestion
                (fullCoordinateInsertedHistory D L i r x y)
                hidden))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro hidden _
      rw [fullCoordinateInsertedHiddenAliceWeight_eq
        G D L i r x y hidden]
      rw [fullCoordinateInsertedAliceQuestion_eq
        D L i hiD hiL r x y hidden]
      rw [conditionedAliceEffect_insert_eq_coordinate
        G n S D i hiD α a]

theorem fullCoordinateInsertedHistory_bobFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (β : {j : Fin n // j ∈ D} → B) (b : B) :
    fullHistoryBobFilter G n S (insert i D) L
      (fullCoordinateInsertedHistory D L i r x y)
      (fullCoordinateAnswerExtension D i β b) =
      fullCoordinateBobRefinementEffect G n S D L i r β y b := by
  classical
  change
    (∑ hidden : {j : Fin n // j ∈ L} → Y,
      fullHistoryHiddenBobWeight G
        (fullCoordinateInsertedHistory D L i r x y) hidden •
      conditionedBobEffect G n S (insert i D)
        (fullCoordinateAnswerExtension D i β b)
        (fullHistoryBobQuestion
          (fullCoordinateInsertedHistory D L i r x y) hidden)) =
      ∑ hidden : {j : Fin n // j ∈ L} → Y,
        fullHistoryHiddenBobWeight G
          (fullCoordinateOldHistory D L i r y) hidden •
        conditionedBobCoordinateEffect G n S D β
          (fullHistoryBobQuestion
            (fullCoordinateOldHistory D L i r y) hidden) i b
  apply Finset.sum_congr rfl
  intro hidden _
  rw [fullCoordinateInsertedHiddenBobWeight_eq G D L i r x y hidden]
  rw [fullCoordinateInsertedBobQuestion_eq D L i hiD hiL r x y hidden]
  rw [conditionedBobEffect_insert_eq_coordinate G n S D i hiD β b]

theorem fullCoordinateInsertedHistory_sum
    {T : Type*} [AddCommMonoid T]
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D)
    (f : FullSubsetHistory X Y n (insert i D) L → T) :
    (∑ h : FullSubsetHistory X Y n (insert i D) L, f h) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ x : X, ∑ y : Y,
        f (fullCoordinateInsertedHistory D L i r x y) := by
  classical
  simpa [fullCoordinateInsertedHistoryEquiv, Fintype.sum_prod_type]
    using ((fullCoordinateInsertedHistoryEquiv
      (X := X) (Y := Y) D L i hiD).sum_comp f).symm

theorem fullCoordinateAnswerExtension_sum
    {T R : Type*} [Fintype T] [AddCommMonoid R]
    {n : ℕ} (D : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D)
    (f : ({j : Fin n // j ∈ insert i D} → T) → R) :
    (∑ α : {j : Fin n // j ∈ insert i D} → T, f α) =
      ∑ α : {j : Fin n // j ∈ D} → T, ∑ a : T,
        f (fullCoordinateAnswerExtension D i α a) := by
  classical
  simpa [fullCoordinateAnswerExtensionEquiv, Fintype.sum_prod_type]
    using ((fullCoordinateAnswerExtensionEquiv
      (T := T) D i hiD).sum_comp f).symm

theorem fullCoordinateWeightedInsertedSum
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D)
    (value : (h : FullSubsetHistory X Y n (insert i D) L) →
      ({j : Fin n // j ∈ insert i D} → A) →
      ({j : Fin n // j ∈ insert i D} → B) → ℝ) :
    (∑ h : FullSubsetHistory X Y n (insert i D) L,
      ∑ α : {j : Fin n // j ∈ insert i D} → A,
      ∑ β : {j : Fin n // j ∈ insert i D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullCoordinateBaseWeight G D L i r *
          fullCoordinateBaseWinIndicator G D L i r α β *
          (∑ x : X, ∑ y : Y, G.questionWeight x y *
            (∑ a : A, ∑ b : B,
              (if G.predicate x y a b = true then 1 else 0) *
                value (fullCoordinateInsertedHistory D L i r x y)
                  (fullCoordinateAnswerExtension D i α a)
                  (fullCoordinateAnswerExtension D i β b))) := by
  classical
  calc
    (∑ h : FullSubsetHistory X Y n (insert i D) L,
      ∑ α : {j : Fin n // j ∈ insert i D} → A,
      ∑ β : {j : Fin n // j ∈ insert i D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ x : X, ∑ y : Y,
      ∑ α : {j : Fin n // j ∈ insert i D} → A,
      ∑ β : {j : Fin n // j ∈ insert i D} → B,
        fullHistoryWeight G
            (fullCoordinateInsertedHistory D L i r x y) *
          fullHistoryWinIndicator G
            (fullCoordinateInsertedHistory D L i r x y) α β *
          value (fullCoordinateInsertedHistory D L i r x y) α β :=
      fullCoordinateInsertedHistory_sum D L i hiD
        (fun h =>
          ∑ α : {j : Fin n // j ∈ insert i D} → A,
          ∑ β : {j : Fin n // j ∈ insert i D} → B,
            fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
              value h α β)
    _ =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ x : X, ∑ y : Y,
      ∑ α : {j : Fin n // j ∈ D} → A, ∑ a : A,
      ∑ β : {j : Fin n // j ∈ D} → B, ∑ b : B,
        fullHistoryWeight G
            (fullCoordinateInsertedHistory D L i r x y) *
          fullHistoryWinIndicator G
            (fullCoordinateInsertedHistory D L i r x y)
            (fullCoordinateAnswerExtension D i α a)
            (fullCoordinateAnswerExtension D i β b) *
          value (fullCoordinateInsertedHistory D L i r x y)
            (fullCoordinateAnswerExtension D i α a)
            (fullCoordinateAnswerExtension D i β b) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [fullCoordinateAnswerExtension_sum (T := A) D i hiD]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro a _
      rw [fullCoordinateAnswerExtension_sum (T := B) D i hiD]
    _ =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
      ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
        fullHistoryWeight G
            (fullCoordinateInsertedHistory D L i r x y) *
          fullHistoryWinIndicator G
            (fullCoordinateInsertedHistory D L i r x y)
            (fullCoordinateAnswerExtension D i α a)
            (fullCoordinateAnswerExtension D i β b) *
          value (fullCoordinateInsertedHistory D L i r x y)
            (fullCoordinateAnswerExtension D i α a)
            (fullCoordinateAnswerExtension D i β b) := by
      apply Finset.sum_congr rfl
      intro r _
      calc
        (∑ x : X, ∑ y : Y,
          ∑ α : {j : Fin n // j ∈ D} → A, ∑ a : A,
          ∑ β : {j : Fin n // j ∈ D} → B, ∑ b : B,
            fullHistoryWeight G
                (fullCoordinateInsertedHistory D L i r x y) *
              fullHistoryWinIndicator G
                (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b) *
              value (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b)) =
          ∑ x : X, ∑ y : Y,
          ∑ α : {j : Fin n // j ∈ D} → A,
          ∑ β : {j : Fin n // j ∈ D} → B,
          ∑ a : A, ∑ b : B,
            fullHistoryWeight G
                (fullCoordinateInsertedHistory D L i r x y) *
              fullHistoryWinIndicator G
                (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b) *
              value (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            apply Finset.sum_congr rfl
            intro α _
            rw [Finset.sum_comm]
        _ = _ := finite_sum_four_swap (fun x y α β =>
          ∑ a : A, ∑ b : B,
            fullHistoryWeight G
                (fullCoordinateInsertedHistory D L i r x y) *
              fullHistoryWinIndicator G
                (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b) *
              value (fullCoordinateInsertedHistory D L i r x y)
                (fullCoordinateAnswerExtension D i α a)
                (fullCoordinateAnswerExtension D i β b))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [fullCoordinateInsertedHistory_weight G D L i hiD r x y]
      rw [fullCoordinateInsertedHistory_winIndicator_eq
        G D L i hiD r x y α a β b]
      ring

def fullCoordinateAcceptedPostselectedMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n) : ℝ :=
  ∑ r : FullCoordinateRevealHistory X Y n D L i,
  ∑ α : {j : Fin n // j ∈ D} → A,
  ∑ β : {j : Fin n // j ∈ D} → B,
    fullCoordinateBaseWeight G D L i r *
      fullCoordinateBaseWinIndicator G D L i r α β *
      (∑ x : X, ∑ y : Y, G.questionWeight x y *
        (∑ a : A, ∑ b : B,
          (if G.predicate x y a b = true then 1 else 0) *
            bornTracePairing S.state.matrix
              (fullCoordinateAliceRefinementEffect
                G n S D L i r α x a)
              (fullCoordinateBobRefinementEffect
                G n S D L i r β y b)))

theorem fullCoordinateAcceptedPostselectedMass_eq
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L)
    (hL : L ⊆ Finset.univ \ D) :
    fullCoordinateAcceptedPostselectedMass G n S D L i =
      (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) (insert i D)) := by
  classical
  have hLinsert : L ⊆ Finset.univ \ insert i D := by
    intro j hj
    have hjD : j ∉ D := (Finset.mem_sdiff.mp (hL hj)).2
    have hji : j ≠ i := by
      intro he
      exact hiL (he ▸ hj)
    simp [hjD, hji]
  calc
    fullCoordinateAcceptedPostselectedMass G n S D L i =
      ∑ h : FullSubsetHistory X Y n (insert i D) L,
      ∑ α : {j : Fin n // j ∈ insert i D} → A,
      ∑ β : {j : Fin n // j ∈ insert i D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          bornTracePairing S.state.matrix
            (fullHistoryAliceFilter G n S (insert i D) L h α)
            (fullHistoryBobFilter G n S (insert i D) L h β) := by
      have hweighted := fullCoordinateWeightedInsertedSum
        G D L i hiD
        (fun h α β => bornTracePairing S.state.matrix
          (fullHistoryAliceFilter G n S (insert i D) L h α)
          (fullHistoryBobFilter G n S (insert i D) L h β))
      simp_rw [fullCoordinateInsertedHistory_aliceFilter
        G n S D L i hiD hiL,
        fullCoordinateInsertedHistory_bobFilter
          G n S D L i hiD hiL] at hweighted
      simpa [fullCoordinateAcceptedPostselectedMass] using hweighted.symm
    _ = _ := fullSubsetHistory_mass_eq_postselection
      G n S (insert i D) L hLinsert

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def sourceHistoryAcceptedQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (r : SourceHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ a : A, ∑ b : B,
    (if G.predicate x y a b = true then 1 else 0) *
      bornTracePairing S.state.matrix
        (fullCoordinateAliceRefinementEffect G n S D
          (sourceRemainingPermutationPrefix D
            r.permutation r.position.castSucc)
          (sourceRemainingPermutationCoordinate D
            r.permutation r.position)
          r.history r.aliceAnswer x a)
        (fullCoordinateBobRefinementEffect G n S D
          (sourceRemainingPermutationPrefix D
            r.permutation r.position.castSucc)
          (sourceRemainingPermutationCoordinate D
            r.permutation r.position)
          r.history r.bobAnswer y b)

def sourceHistoryAcceptedMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n)) : ℝ :=
  ∑ r : SourceHistoryFlag X Y A B D,
    sourceHistoryRaw G n D r *
      (∑ x : X, ∑ y : Y, G.questionWeight x y *
        sourceHistoryAcceptedQuestionMass G n S D r x y)

theorem sourceHistoryQuadraticExpectation_matrix_sum
    {I d : Type*} [Fintype I] [Fintype d] [DecidableEq d]
    (M : I → Matrix d d ℂ) (z : EuclideanSpace ℂ d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) (∑ i : I, M i)) z =
      ∑ i : I,
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) (M i)) z := by
  simp [quadraticExpectation]

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem sourceHistoryAcceptedMass_eq_uniform
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n)) :
    sourceHistoryAcceptedMass G n S D =
      sourceUniformPermutationAverage D
        (fun π k =>
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
              (insert (sourceRemainingPermutationCoordinate D π k) D))) := by
  classical
  have hlocal (π : SourceRemainingPermutation D)
      (k : Fin (Finset.univ \ D).card) :
      fullCoordinateAcceptedPostselectedMass G n S D
        (sourceRemainingPermutationPrefix D π k.castSucc)
        (sourceRemainingPermutationCoordinate D π k) =
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
            (insert (sourceRemainingPermutationCoordinate D π k) D)) := by
    apply fullCoordinateAcceptedPostselectedMass_eq
    · exact sourceRemainingPermutationCoordinate_not_mem D π k
    · exact sourceRemainingPermutationCoordinate_not_mem_prefix D π k
    · exact sourceRemainingPermutationPrefix_subset D π k.castSucc
  calc
    sourceHistoryAcceptedMass G n S D =
      ∑ π : SourceRemainingPermutation D,
      ∑ k : Fin (Finset.univ \ D).card,
        sourceHistoryPermutationPositionWeight D *
          fullCoordinateAcceptedPostselectedMass G n S D
            (sourceRemainingPermutationPrefix D π k.castSucc)
            (sourceRemainingPermutationCoordinate D π k) := by
      unfold sourceHistoryAcceptedMass
      rw [sourceHistoryFlag_sum]
      apply Finset.sum_congr rfl
      intro π _
      apply Finset.sum_congr rfl
      intro k _
      unfold fullCoordinateAcceptedPostselectedMass
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      simp only [sourceHistoryRaw, sourceHistoryAcceptedQuestionMass,
        Finset.mul_sum]
      ring_nf
    _ =
      ∑ π : SourceRemainingPermutation D,
      ∑ k : Fin (Finset.univ \ D).card,
        sourceHistoryPermutationPositionWeight D *
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
              (insert (sourceRemainingPermutationCoordinate D π k) D)) := by
      apply Finset.sum_congr rfl
      intro π _
      apply Finset.sum_congr rfl
      intro k _
      rw [hlocal π k]
    _ = _ := by
      unfold sourceHistoryPermutationPositionWeight
        sourceUniformPermutationAverage
      simp_rw [one_div, div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro π _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem sourceHistoryAcceptedMass_eq_remaining_average
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n)) :
    sourceHistoryAcceptedMass G n S D =
      (∑ i : SourceRemainingCoordinate D,
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
            (insert i.val D))) /
        ((Finset.univ \ D).card : ℝ) := by
  classical
  rw [sourceHistoryAcceptedMass_eq_uniform]
  have hperm := sourceRemainingPermutation_card_pos D
  unfold sourceUniformPermutationAverage
  simp_rw [sourceRemainingPermutationCoordinate_sum D _
    (fun i : Fin n =>
      (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
          (insert i D)))]
  have hsum :
      (∑ _π : SourceRemainingPermutation D,
        ∑ i : SourceRemainingCoordinate D,
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
              (insert i.val D))) =
      (Fintype.card (SourceRemainingPermutation D) : ℝ) *
        (∑ i : SourceRemainingCoordinate D,
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
              (insert i.val D))) := by simp
  rw [hsum]
  exact mul_div_mul_left _ _ hperm.ne'

theorem sourceHistoryAcceptedMass_gt_of_greedy
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    {η : ℝ}
    (hgreedy :
      (∑ i ∈ Finset.univ \ D,
        FiniteEventLaw.failureMass
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D i) <
        ((Finset.univ \ D).card : ℝ) *
          (η * (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent
              (repeatedCoordinateWin G n) D))) :
    (1 - η) *
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D) <
      sourceHistoryAcceptedMass G n S D := by
  classical
  let p : ℝ := (strategyEventLaw (G.repeat n) S).eventMass
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
  have hmreal : 0 < ((Finset.univ \ D).card : ℝ) := by
    exact_mod_cast hm
  have hsub := Finset.sum_subtype (F := inferInstance)
    (Finset.univ \ D)
    (fun i : Fin n => Iff.rfl)
    (fun i : Fin n => (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
        (insert i D)))
  have hfails :
      (∑ i ∈ Finset.univ \ D,
        FiniteEventLaw.failureMass
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D i) =
        ((Finset.univ \ D).card : ℝ) * p -
          (∑ i ∈ Finset.univ \ D,
            (strategyEventLaw (G.repeat n) S).eventMass
              (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
                (insert i D))) := by
    simp [FiniteEventLaw.failureMass, p, Finset.sum_sub_distrib]
  rw [sourceHistoryAcceptedMass_eq_remaining_average]
  rw [← hsub]
  apply (lt_div_iff₀ hmreal).mpr
  change (1 - η) * p * ((Finset.univ \ D).card : ℝ) < _
  change
    (∑ i ∈ Finset.univ \ D,
      FiniteEventLaw.failureMass
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D i) <
      ((Finset.univ \ D).card : ℝ) * (η * p) at hgreedy
  nlinarith [hgreedy, hfails]

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

section TaggedTensorBlocks

variable {R : Type*} [Fintype R]
variable {ι : R → Type*} [∀ r, Fintype (ι r)]

def taggedTensorVector
    (r : R) (z : EuclideanSpace ℂ (ι r × ι r)) :
    EuclideanSpace ℂ
      ((PUnit.{1} ⊕ (Σ r : R, ι r)) ×
        (PUnit.{1} ⊕ (Σ r : R, ι r))) := by
  classical
  exact toLp 2 fun q =>
    match q.1, q.2 with
    | .inr ⟨rA, a⟩, .inr ⟨rB, b⟩ =>
        if hA : rA = r then
          if hB : rB = r then
            z (hA ▸ a, hB ▸ b)
          else 0
        else 0
    | _, _ => 0

theorem taggedTensorVector_norm
    (r : R) (z : EuclideanSpace ℂ (ι r × ι r)) :
    ‖taggedTensorVector r z‖ = ‖z‖ := by
  classical
  have hsquare :
      ‖taggedTensorVector r z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, taggedTensorVector,
      Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_sigma]
    calc
      _ = ∑ a : ι r, ∑ rB : R, ∑ b : ι rB,
          ‖if hA : (r : R) = r then
              if hB : rB = r then z (hA ▸ a, hB ▸ b) else 0
            else 0‖ ^ 2 := by
        apply Fintype.sum_eq_single r
        intro rA hA
        simp [hA]
      _ = ∑ a : ι r, ∑ rB : R, ∑ b : ι rB,
          ‖if hB : rB = r then z (a, hB ▸ b) else 0‖ ^ 2 := by
        simp
      _ = ∑ a : ι r, ∑ b : ι r,
          ‖if hB : (r : R) = r then z (a, hB ▸ b) else 0‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        apply Fintype.sum_eq_single r
        intro rB hB
        simp [hB]
      _ = _ := by simp
  nlinarith [norm_nonneg (taggedTensorVector r z),
    norm_nonneg z]

omit [Fintype R] [∀ r, Fintype (ι r)] in

theorem taggedTensorVector_sub
    (r : R) (u v : EuclideanSpace ℂ (ι r × ι r)) :
    taggedTensorVector r (u - v) =
      taggedTensorVector r u - taggedTensorVector r v := by
  classical
  ext q
  rcases q with ⟨a, b⟩
  rcases a with a | ⟨rA, a⟩
  · rcases b with b | ⟨rB, b⟩ <;>
      simp [taggedTensorVector]
  · rcases b with b | ⟨rB, b⟩
    · simp [taggedTensorVector]
    · by_cases hA : rA = r
      · subst rA
        by_cases hB : rB = r
        · subst rB
          simp [taggedTensorVector]
        · simp [taggedTensorVector, hB]
      · simp [taggedTensorVector, hA]

end TaggedTensorBlocks

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem martingaleRate_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    (hp : 0 < repeatedPostselectionMass G n S D) :
    0 ≤ martingaleRate G n S D := by
  have hnonnegative := sourceUniformPermutationAverage_nonneg D
    (sourcePermutationAliceEntropyIncrement G n S D)
    (fun π k => sourcePermutationAliceEntropyIncrement_nonneg
      G n S D π k)
  have hbudget := aliceMartingaleEntropyBudget
    G n S D hm hp
  nlinarith

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem remainingCoordinate_card_pos
    {n : ℕ} (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card) :
    0 < Fintype.card (SourceRemainingCoordinate D) := by
  simpa using hm

theorem finiteTotalVariation_triangle
    {ι : Type*} [Fintype ι]
    (p q r : ι → ℝ) :
    finiteTotalVariation p r ≤
      finiteTotalVariation p q + finiteTotalVariation q r := by
  unfold finiteTotalVariation
  calc
    (∑ i, |p i - r i|) / 2 ≤
        ((∑ i, |p i - q i|) +
          (∑ i, |q i - r i|)) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      exact abs_sub_le (p i) (q i) (r i)
    _ = (∑ i, |p i - q i|) / 2 +
        (∑ i, |q i - r i|) / 2 := by ring

def weightedConditionalJoint
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (weight : κ → ℝ) (conditional : κ → ι → ℝ) :
    κ × ι → ℝ :=
  fun t => weight t.1 * conditional t.1 t.2

theorem weightedConditionalJoint_totalVariation
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (weight : κ → ℝ) (hweight : ∀ k, 0 ≤ weight k)
    (left right : κ → ι → ℝ) :
    finiteTotalVariation
        (weightedConditionalJoint weight left)
        (weightedConditionalJoint weight right) =
      ∑ k : κ, weight k *
        finiteTotalVariation (left k) (right k) := by
  unfold finiteTotalVariation weightedConditionalJoint
  rw [Fintype.sum_prod_type]
  calc
    (∑ k : κ, ∑ i : ι,
      |weight k * left k i - weight k * right k i|) / 2 =
      (∑ k : κ, weight k *
        (∑ i : ι, |left k i - right k i|)) / 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_sub, abs_mul, abs_of_nonneg (hweight k)]
    _ = ∑ k : κ,
        weight k * ((∑ i : ι, |left k i - right k i|) / 2) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem finiteTotalVariation_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (p q : κ → ℝ) :
    finiteTotalVariation (p ∘ e) (q ∘ e) =
      finiteTotalVariation p q := by
  unfold finiteTotalVariation
  congr 1
  exact e.sum_comp (fun i => |p i - q i|)

abbrev LocalQuestionContext
    (X Y : Type*) [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n)) :=
  SourceRemainingCoordinate D × (X × Y)

def localQuestionWeight
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (c : LocalQuestionContext X Y D) : ℝ :=
  G.questionWeight c.2.1 c.2.2 /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

theorem localQuestionWeight_nonneg
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (c : LocalQuestionContext X Y D) :
    0 ≤ localQuestionWeight G n D c := by
  exact div_nonneg (G.weight_nonneg c.2.1 c.2.2)
    (Nat.cast_nonneg _)

theorem localQuestionWeight_sum
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card) :
    (∑ c : LocalQuestionContext X Y D,
      localQuestionWeight G n D c) = 1 := by
  have hcard : (Fintype.card (SourceRemainingCoordinate D) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (remainingCoordinate_card_pos D hm))
  calc
    (∑ c : LocalQuestionContext X Y D,
      localQuestionWeight G n D c) =
      (∑ i : SourceRemainingCoordinate D,
        ∑ x : X, ∑ y : Y, G.questionWeight x y) /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) := by
      simp only [localQuestionWeight, Fintype.sum_prod_type]
      simp_rw [← Finset.sum_div]
    _ = 1 := by
      simp_rw [G.weight_normalized]
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      exact div_self hcard

def conditionedEventDistribution
    {Ω : Type*} [Fintype Ω]
    (law : FiniteEventLaw Ω) (event : Finset Ω) : Ω → ℝ :=
  fun ω => if ω ∈ event then law.weight ω / law.eventMass event else 0

theorem conditionedEventDistribution_nonneg
    {Ω : Type*} [Fintype Ω]
    (law : FiniteEventLaw Ω) (event : Finset Ω)
    (positive : 0 < law.eventMass event) (ω : Ω) :
    0 ≤ conditionedEventDistribution law event ω := by
  unfold conditionedEventDistribution
  split_ifs
  · exact div_nonneg (law.weight_nonneg ω) positive.le
  · exact le_rfl

theorem conditionedEventDistribution_sum
    {Ω : Type*} [Fintype Ω]
    (law : FiniteEventLaw Ω) (event : Finset Ω)
    (positive : 0 < law.eventMass event) :
    (∑ ω : Ω, conditionedEventDistribution law event ω) = 1 := by
  classical
  unfold conditionedEventDistribution
  calc
    (∑ ω : Ω,
      if ω ∈ event then law.weight ω / law.eventMass event else 0) =
      (∑ ω ∈ event, law.weight ω) / law.eventMass event := by
      rw [Finset.sum_div]
      simp
    _ = 1 := by
      change law.eventMass event / law.eventMass event = 1
      exact div_self positive.ne'

theorem conditionedEventDistribution_absolute_continuity
    {Ω : Type*} [Fintype Ω]
    (law : FiniteEventLaw Ω) (event : Finset Ω) (ω : Ω) :
    law.weight ω = 0 →
      conditionedEventDistribution law event ω = 0 := by
  intro hzero
  simp [conditionedEventDistribution, hzero]

theorem conditionedEventDistribution_relativeEntropy
    {Ω : Type*} [Fintype Ω]
    (law : FiniteEventLaw Ω) (event : Finset Ω)
    (positive : 0 < law.eventMass event) :
    finiteRelativeEntropy
        (conditionedEventDistribution law event)
        law.weight =
      Real.log (1 / law.eventMass event) := by
  rw [finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
    (conditionedEventDistribution law event)
    law.weight law.weight_nonneg
    (conditionedEventDistribution_absolute_continuity law event)
    (conditionedEventDistribution_sum law event positive)
    law.weight_sum]
  calc
    (∑ ω : Ω,
      conditionedEventDistribution law event ω *
        Real.log
          (conditionedEventDistribution law event ω /
            law.weight ω)) =
      ∑ ω : Ω,
        conditionedEventDistribution law event ω *
          Real.log (1 / law.eventMass event) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hmem : ω ∈ event
      · by_cases hweight : law.weight ω = 0
        · simp [conditionedEventDistribution, hmem, hweight]
        · have hratio :
              (law.weight ω / law.eventMass event) /
                  law.weight ω = 1 / law.eventMass event := by
                field_simp [hweight, positive.ne']
          simp only [conditionedEventDistribution,
            if_pos hmem, hratio]
      · simp [conditionedEventDistribution, hmem]
    _ = Real.log (1 / law.eventMass event) := by
      rw [← Finset.sum_mul,
        conditionedEventDistribution_sum law event positive]
      ring

theorem conditionedEventDistribution_projection_relativeEntropy_le
    {Ω κ : Type*} [Fintype Ω] [Fintype κ]
    (law : FiniteEventLaw Ω) (event : Finset Ω)
    (positive : 0 < law.eventMass event)
    (projection : Ω → κ) :
    finiteRelativeEntropy
        (groupedMass projection
          (conditionedEventDistribution law event))
        (groupedMass projection law.weight) ≤
      Real.log (1 / law.eventMass event) := by
  calc
    finiteRelativeEntropy
        (groupedMass projection
          (conditionedEventDistribution law event))
        (groupedMass projection law.weight) ≤
      finiteRelativeEntropy
        (conditionedEventDistribution law event)
        law.weight :=
      finite_relative_entropy_data_processing
        projection
        (conditionedEventDistribution law event)
        law.weight
        (conditionedEventDistribution_nonneg law event positive)
        law.weight_nonneg
        (conditionedEventDistribution_absolute_continuity
          law event)
    _ = Real.log (1 / law.eventMass event) :=
      conditionedEventDistribution_relativeEntropy
        law event positive

def repeatedConditionedOutcomeLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    StrategyOutcome
      (Fin n → X) (Fin n → Y)
      (Fin n → A) (Fin n → B) → ℝ :=
  conditionedEventDistribution
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)

theorem repeatedConditionedOutcomeLaw_relativeEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hp : 0 < repeatedPostselectionMass G n S D) :
    finiteRelativeEntropy
        (repeatedConditionedOutcomeLaw G n S D)
        (strategyEventLaw (G.repeat n) S).weight =
      postselectionLogCost G n S D := by
  exact conditionedEventDistribution_relativeEntropy
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) hp

end

noncomputable section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

def finiteUniformWeight (Z : Type*) [Fintype Z] : ℝ :=
  1 / (Fintype.card Z : ℝ)

theorem finiteUniformWeight_pos
    {Z : Type*} [Fintype Z]
    (positive : 0 < Fintype.card Z) :
    0 < finiteUniformWeight Z := by
  unfold finiteUniformWeight
  exact one_div_pos.mpr (by exact_mod_cast positive)

theorem finiteUniformWeight_sum
    {Z : Type*} [Fintype Z]
    (positive : 0 < Fintype.card Z) :
    (∑ _z : Z, finiteUniformWeight Z) = 1 := by
  have hcard : (Fintype.card Z : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  unfold finiteUniformWeight
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

theorem finiteProbability_le_one
    {Z : Type*} [Fintype Z]
    (p : Z → ℝ)
    (nonnegative : ∀ z, 0 ≤ p z)
    (normalized : (∑ z, p z) = 1)
    (z : Z) :
    p z ≤ 1 := by
  calc
    p z ≤ ∑ a : Z, p a :=
      Finset.single_le_sum
        (fun a _ => nonnegative a) (Finset.mem_univ z)
    _ = 1 := normalized

theorem finiteRelativeEntropy_uniform_le_log_card
    {Z : Type*} [Fintype Z]
    (p : Z → ℝ)
    (nonnegative : ∀ z, 0 ≤ p z)
    (normalized : (∑ z, p z) = 1)
    (positive : 0 < Fintype.card Z) :
    finiteRelativeEntropy p
        (fun _ : Z => finiteUniformWeight Z) ≤
      Real.log (Fintype.card Z : ℝ) := by
  have hcardpos : 0 < (Fintype.card Z : ℝ) := by
    exact_mod_cast positive
  have hcardne : (Fintype.card Z : ℝ) ≠ 0 := hcardpos.ne'
  rw [finiteRelativeEntropy_eq_log_sum p
    (fun _ : Z => finiteUniformWeight Z)
    (fun _ => finiteUniformWeight_pos positive)
    normalized (finiteUniformWeight_sum positive)]
  calc
    (∑ z : Z, p z *
      Real.log (p z / finiteUniformWeight Z)) ≤
      ∑ z : Z, p z * Real.log (Fintype.card Z : ℝ) := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hzero : p z = 0
      · simp [hzero]
      · have hp : 0 < p z :=
          lt_of_le_of_ne (nonnegative z) (Ne.symm hzero)
        have hpone : p z ≤ 1 :=
          finiteProbability_le_one p nonnegative normalized z
        have hratio :
            p z / finiteUniformWeight Z =
              p z * (Fintype.card Z : ℝ) := by
          unfold finiteUniformWeight
          field_simp [hcardne]
        rw [hratio]
        apply mul_le_mul_of_nonneg_left _ (nonnegative z)
        apply Real.log_le_log (mul_pos hp hcardpos)
        nlinarith
    _ = Real.log (Fintype.card Z : ℝ) := by
      rw [← Finset.sum_mul, normalized]
      ring

def uniformFlagReference
    {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    (prior : Ω → ℝ) : Ω × Z → ℝ :=
  fun t => prior t.1 * finiteUniformWeight Z

theorem uniformFlagReference_nonneg
    {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    (prior : Ω → ℝ)
    (nonnegative : ∀ ω, 0 ≤ prior ω)
    (positive : 0 < Fintype.card Z)
    (t : Ω × Z) :
    0 ≤ uniformFlagReference (Z := Z) prior t := by
  exact mul_nonneg (nonnegative t.1)
    (finiteUniformWeight_pos positive).le

theorem uniformFlagReference_sum
    {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    (prior : Ω → ℝ)
    (normalized : (∑ ω, prior ω) = 1)
    (positive : 0 < Fintype.card Z) :
    (∑ t : Ω × Z,
      uniformFlagReference (Z := Z) prior t) = 1 := by
  rw [Fintype.sum_prod_type]
  unfold uniformFlagReference
  simp_rw [← Finset.mul_sum,
    finiteUniformWeight_sum positive, mul_one]
  exact normalized

theorem uniformFlagReference_firstMarginal
    {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    (prior : Ω → ℝ)
    (positive : 0 < Fintype.card Z) :
    jointFirstMarginal
        (uniformFlagReference (Z := Z) prior) = prior := by
  funext ω
  change
    (∑ z : Z, prior ω * finiteUniformWeight Z) = prior ω
  rw [← Finset.mul_sum, finiteUniformWeight_sum positive]
  ring

theorem uniformFlagReference_conditional
    {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    (prior : Ω → ℝ)
    (positive : 0 < Fintype.card Z)
    (ω : Ω) (hprior : prior ω ≠ 0) :
    jointConditional
        (uniformFlagReference (Z := Z) prior) ω =
      fun _ : Z => finiteUniformWeight Z := by
  funext z
  unfold jointConditional
  rw [uniformFlagReference_firstMarginal prior positive]
  change
    prior ω * finiteUniformWeight Z / prior ω =
      finiteUniformWeight Z
  field_simp [hprior]

theorem uniformFlagReference_absolute_continuity
    {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    (joint : Ω × Z → ℝ)
    (prior : Ω → ℝ)
    (hjoint : ∀ t, 0 ≤ joint t)
    (absolute_continuity :
      ∀ ω, prior ω = 0 → jointFirstMarginal joint ω = 0)
    (positive : 0 < Fintype.card Z)
    (t : Ω × Z) :
    uniformFlagReference (Z := Z) prior t = 0 →
      joint t = 0 := by
  rcases t with ⟨ω, z⟩
  intro hzero
  change prior ω * finiteUniformWeight Z = 0 at hzero
  have hflag : finiteUniformWeight Z ≠ 0 :=
    (finiteUniformWeight_pos positive).ne'
  have hprior : prior ω = 0 :=
    (mul_eq_zero.mp hzero).resolve_right hflag
  have hmarginal := absolute_continuity ω hprior
  change (∑ a : Z, joint (ω, a)) = 0 at hmarginal
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ => hjoint (ω, a))).mp
      hmarginal z (Finset.mem_univ z)

theorem uniformFlagRelativeEntropy_le
    {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    (joint : Ω × Z → ℝ)
    (prior : Ω → ℝ)
    (hjoint : ∀ t, 0 ≤ joint t)
    (hprior : ∀ ω, 0 ≤ prior ω)
    (joint_normalized : (∑ t, joint t) = 1)
    (prior_normalized : (∑ ω, prior ω) = 1)
    (absolute_continuity :
      ∀ ω, prior ω = 0 → jointFirstMarginal joint ω = 0)
    (positive : 0 < Fintype.card Z) :
    finiteRelativeEntropy joint
        (uniformFlagReference (Z := Z) prior) ≤
      finiteRelativeEntropy (jointFirstMarginal joint) prior +
        Real.log (Fintype.card Z : ℝ) := by
  have hreference_nonneg :=
    uniformFlagReference_nonneg prior hprior positive
  have hreference_normalized :=
    uniformFlagReference_sum prior prior_normalized positive
  have hreference_absolute :=
    uniformFlagReference_absolute_continuity
      joint prior hjoint absolute_continuity positive
  have hmarginal_normalized :
      (∑ ω : Ω, jointFirstMarginal joint ω) = 1 :=
    (jointFirstMarginal_sum joint).trans joint_normalized
  have hmarginal_nonnegative :
      ∀ ω : Ω, 0 ≤ jointFirstMarginal joint ω :=
    jointFirstMarginal_nonneg joint hjoint
  rw [finite_relative_entropy_joint_chain_rule
    joint (uniformFlagReference (Z := Z) prior)
    hjoint hreference_nonneg hreference_absolute
    joint_normalized hreference_normalized,
    uniformFlagReference_firstMarginal prior positive]
  gcongr
  calc
    (∑ ω : Ω,
      jointFirstMarginal joint ω *
        finiteRelativeEntropy (jointConditional joint ω)
          (jointConditional
            (uniformFlagReference (Z := Z) prior) ω)) ≤
      ∑ ω : Ω,
        jointFirstMarginal joint ω *
          Real.log (Fintype.card Z : ℝ) := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases hmass : jointFirstMarginal joint ω = 0
      · simp [hmass]
      · have hprior_ne : prior ω ≠ 0 := by
          intro hzero
          exact hmass (absolute_continuity ω hzero)
        rw [uniformFlagReference_conditional
          prior positive ω hprior_ne]
        apply mul_le_mul_of_nonneg_left _
          (hmarginal_nonnegative ω)
        apply finiteRelativeEntropy_uniform_le_log_card
        · intro z
          exact div_nonneg (hjoint (ω, z))
            (hmarginal_nonnegative ω)
        · exact jointConditional_sum joint ω hmass
        · exact positive
    _ = Real.log (Fintype.card Z : ℝ) := by
      rw [← Finset.sum_mul, hmarginal_normalized]
      ring

theorem finiteRelativeEntropy_nonneg
    {Ω : Type*} [Fintype Ω]
    (p q : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω)
    (hq : ∀ ω, 0 ≤ q ω) :
    0 ≤ finiteRelativeEntropy p q := by
  unfold finiteRelativeEntropy
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (hq ω)
    (InformationTheory.klFun_nonneg (div_nonneg (hp ω) (hq ω)))

theorem groupedMass_nonneg
    {Ω κ : Type*} [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (f : Ω → κ) (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (a : κ) :
    0 ≤ groupedMass f p a := by
  unfold groupedMass
  exact Finset.sum_nonneg (fun ω _ => hp ω)

theorem groupedMass_absolute_continuity
    {Ω κ : Type*} [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (f : Ω → κ) (p q : Ω → ℝ)
    (hq : ∀ ω, 0 ≤ q ω)
    (absolute_continuity : ∀ ω, q ω = 0 → p ω = 0)
    (a : κ) :
    groupedMass f q a = 0 → groupedMass f p a = 0 := by
  intro hzero
  change
    (∑ ω ∈ (Finset.univ.filter fun ω => f ω = a), q ω) = 0 at hzero
  change
    (∑ ω ∈ (Finset.univ.filter fun ω => f ω = a), p ω) = 0
  apply Finset.sum_eq_zero
  intro ω hω
  have hqzero : q ω = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun ω _ => hq ω)).mp hzero ω hω
  exact absolute_continuity ω hqzero

theorem groupedMass_comp
    {Ω κ θ : Type*} [Fintype Ω] [Fintype κ] [Fintype θ]
    [DecidableEq κ] [DecidableEq θ]
    (f : Ω → κ) (g : κ → θ) (p : Ω → ℝ) :
    groupedMass g (groupedMass f p) =
      groupedMass (g ∘ f) p := by
  funext a
  unfold groupedMass
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Function.comp_apply] using
    (Finset.sum_fiberwise_eq_sum_filter
      (Finset.univ : Finset Ω)
      (Finset.univ.filter fun b : κ => g b = a)
      f p)

theorem groupedMass_id
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : Ω → ℝ) :
    groupedMass id p = p := by
  funext ω
  have hfilter :
      (Finset.univ.filter fun a : Ω => a = ω) = {ω} := by
    ext a
    simp
  unfold groupedMass
  change
    (∑ a ∈ (Finset.univ.filter fun a : Ω => a = ω), p a) = p ω
  rw [hfilter]
  simp

def finitePrefixMask
    {Ω Y : Type*} {h : ℕ} (base : Y)
    (k : Fin (h + 1)) :
    (Ω × (Fin h → Y)) → (Ω × (Fin h → Y)) :=
  fun t => (t.1, fun j => if j.val < k.val then t.2 j else base)

theorem finitePrefixMask_comp
    {Ω Y : Type*} {h : ℕ} (base : Y)
    (k : Fin h) :
    finitePrefixMask (Ω := Ω) base k.castSucc ∘
        finitePrefixMask (Ω := Ω) base k.succ =
      finitePrefixMask (Ω := Ω) base k.castSucc := by
  funext t
  rcases t with ⟨ω, values⟩
  apply Prod.ext
  · rfl
  · funext j
    by_cases hj : j.val < k.val
    · have hjfin : j < k := hj
      have hjle : j ≤ k := le_of_lt hjfin
      simp [finitePrefixMask, Function.comp_apply, hjfin, hjle]
    · have hjfin : ¬ j < k := hj
      simp [finitePrefixMask, Function.comp_apply, hjfin]

theorem finitePrefixMask_last
    {Ω Y : Type*} {h : ℕ} (base : Y) :
    finitePrefixMask (Ω := Ω) base (Fin.last h) = id := by
  funext t
  rcases t with ⟨ω, values⟩
  apply Prod.ext
  · rfl
  · funext j
    simp [finitePrefixMask]

def finitePrefixRelativeEntropy
    {Ω Y : Type*} [Fintype Ω] [Fintype Y] {h : ℕ}
    (joint prior : Ω × (Fin h → Y) → ℝ)
    (base : Y) (k : Fin (h + 1)) : ℝ :=
  finiteRelativeEntropy
    (groupedMass (finitePrefixMask base k) joint)
    (groupedMass (finitePrefixMask base k) prior)

theorem finitePrefixRelativeEntropy_telescope
    {Ω Y : Type*} [Fintype Ω] [Fintype Y] {h : ℕ}
    (joint prior : Ω × (Fin h → Y) → ℝ)
    (base : Y) :
    (∑ k : Fin h,
      (finitePrefixRelativeEntropy joint prior base k.succ -
        finitePrefixRelativeEntropy joint prior base k.castSucc)) =
      finiteRelativeEntropy joint prior -
        finitePrefixRelativeEntropy joint prior base 0 := by
  have hfirst := Fin.sum_univ_succ
    (fun k : Fin (h + 1) =>
      finitePrefixRelativeEntropy joint prior base k)
  have hlast := Fin.sum_univ_castSucc
    (fun k : Fin (h + 1) =>
      finitePrefixRelativeEntropy joint prior base k)
  have hendpoint :
      finitePrefixRelativeEntropy joint prior base
          (Fin.last h) =
        finiteRelativeEntropy joint prior := by
    simp only [finitePrefixRelativeEntropy,
      finitePrefixMask_last, groupedMass_id]
  rw [Finset.sum_sub_distrib]
  linarith

theorem finitePrefixRelativeEntropy_budget
    {Ω Y : Type*} [Fintype Ω] [Fintype Y] {h : ℕ}
    (joint prior : Ω × (Fin h → Y) → ℝ)
    (hjoint : ∀ t, 0 ≤ joint t)
    (hprior : ∀ t, 0 ≤ prior t)
    (base : Y) :
    (∑ k : Fin h,
      (finitePrefixRelativeEntropy joint prior base k.succ -
        finitePrefixRelativeEntropy joint prior base k.castSucc)) ≤
      finiteRelativeEntropy joint prior := by
  rw [finitePrefixRelativeEntropy_telescope]
  have hzero :
      0 ≤ finitePrefixRelativeEntropy joint prior base 0 :=
    finiteRelativeEntropy_nonneg
      (groupedMass (finitePrefixMask base 0) joint)
      (groupedMass (finitePrefixMask base 0) prior)
      (groupedMass_nonneg
        (finitePrefixMask base 0) joint hjoint)
      (groupedMass_nonneg
        (finitePrefixMask base 0) prior hprior)
  linarith

theorem reversePartition_relativeEntropy_budget
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (increment : (s : Finset M) → Fin s.card → ℝ)
    {cost : ℝ} (hcost : 0 ≤ cost)
    (hbudget : ∀ s : Finset M,
      (∑ k : Fin s.card, increment s k) ≤ cost) :
    (∑ s : Finset M,
      reversePartitionWeight s *
        ((∑ k : Fin s.card, increment s k) /
          (s.card : ℝ))) ≤
      2 * cost / (Fintype.card M : ℝ) := by
  have hcard : 0 < (Fintype.card M : ℝ) := by
    exact_mod_cast nonempty
  calc
    (∑ s : Finset M,
      reversePartitionWeight s *
        ((∑ k : Fin s.card, increment s k) /
          (s.card : ℝ))) ≤
      ∑ s : Finset M,
        fairPartitionWeight M *
          (2 * cost / (Fintype.card M : ℝ)) := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s.card = 0
      · have hempty : s = ∅ := Finset.card_eq_zero.mp hs
        subst s
        simp only [reversePartitionWeight_empty, zero_mul]
        exact mul_nonneg (fairPartitionWeight_nonneg (α := M))
          (div_nonneg (mul_nonneg (by norm_num) hcost) hcard.le)
      · have hsreal : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
        calc
          reversePartitionWeight s *
              ((∑ k : Fin s.card, increment s k) /
                (s.card : ℝ)) =
            (fairPartitionWeight M *
              (2 / (Fintype.card M : ℝ))) *
                (∑ k : Fin s.card, increment s k) := by
              unfold reversePartitionWeight
              field_simp [hsreal, hcard.ne']
          _ ≤ (fairPartitionWeight M *
              (2 / (Fintype.card M : ℝ))) * cost := by
            apply mul_le_mul_of_nonneg_left (hbudget s)
            exact mul_nonneg (fairPartitionWeight_nonneg (α := M))
              (div_nonneg (by norm_num) hcard.le)
          _ = fairPartitionWeight M *
              (2 * cost / (Fintype.card M : ℝ)) := by ring
    _ = 2 * cost / (Fintype.card M : ℝ) := by
      rw [← Finset.sum_mul, fairPartitionWeight_sum (α := M)]
      ring

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem groupedMass_sum
    {Ω κ : Type*} [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (projection : Ω → κ) (mass : Ω → ℝ) :
    (∑ a : κ, groupedMass projection mass a) =
      ∑ ω : Ω, mass ω := by
  unfold groupedMass
  exact Finset.sum_fiberwise Finset.univ projection mass

theorem groupedMass_first
    {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    [DecidableEq Ω]
    (joint : Ω × Z → ℝ) :
    groupedMass Prod.fst joint = jointFirstMarginal joint := by
  funext ω
  classical
  simp only [groupedMass, jointFirstMarginal,
    Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

abbrev ConditionedAnswerFlag
    (A B : Type*) [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) :=
  ({i : Fin n // i ∈ D} → A) ×
    ({i : Fin n // i ∈ D} → B)

def repeatedConditionedAnswerFlag
    (G : Game X Y A B) (n : ℕ) (_S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (ω : StrategyOutcome
      (Fin n → X) (Fin n → Y)
      (Fin n → A) (Fin n → B)) :
    ConditionedAnswerFlag A B D :=
  (fun i => ω.2.2.1 i, fun i => ω.2.2.2 i)

theorem conditionedAnswerFlag_card
    {n : ℕ} (D : Finset (Fin n)) :
    (Fintype.card (ConditionedAnswerFlag A B D) : ℝ) =
      fullHistoryAnswerCount (A := A) (B := B) D := by
  simp [fullHistoryAnswerCount]

theorem conditionedAnswerFlag_card_pos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hp : 0 < repeatedPostselectionMass G n S D) :
    0 < Fintype.card (ConditionedAnswerFlag A B D) := by
  have hreal :
      0 < (Fintype.card (ConditionedAnswerFlag A B D) : ℝ) := by
    rw [conditionedAnswerFlag_card]
    exact answerCount_pos_of_postselection G n S D hp
  exact_mod_cast hreal

theorem conditionedAnswerFlag_log_card
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hp : 0 < repeatedPostselectionMass G n S D) :
    Real.log (Fintype.card (ConditionedAnswerFlag A B D) : ℝ) =
      answerLogCost (A := A) (B := B) D := by
  rw [conditionedAnswerFlag_card]
  have hanswer := answerCount_pos_of_postselection G n S D hp
  have hcost := martingale_log_cost_eq G n S D hp
  have hsplit := Real.log_div hanswer.ne' hp.ne'
  have hpost :
      postselectionLogCost G n S D =
        -Real.log (repeatedPostselectionMass G n S D) := by
    simp [postselectionLogCost, one_div, Real.log_inv]
  linarith

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

abbrev ExactOutcome (X Y A B : Type*) (n : ℕ) :=
  StrategyOutcome (Fin n → X) (Fin n → Y)
    (Fin n → A) (Fin n → B)

abbrev ExactJointOutcome
    (X Y A B : Type*) {n : ℕ} (D : Finset (Fin n)) :=
  ExactRemainingSeed D × ExactOutcome X Y A B n

theorem exactRemainingSeedWeight_sum
    {n : ℕ} (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card) :
    (∑ seed : ExactRemainingSeed D,
      exactSeedWeight seed) = 1 := by
  apply exactSeedWeight_sum
  simpa using remaining

def exactPostselectedJointLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (q : ExactJointOutcome X Y A B D) : ℝ :=
  exactSeedWeight q.1 *
    repeatedConditionedOutcomeLaw G n S D q.2

theorem exactPostselectedJointLaw_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (q : ExactJointOutcome X Y A B D) :
    0 ≤ exactPostselectedJointLaw G n S D q := by
  apply mul_nonneg (exactSeedWeight_nonneg q.1)
  exact conditionedEventDistribution_nonneg
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
    positive q.2

theorem exactPostselectedJointLaw_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ q : ExactJointOutcome X Y A B D,
      exactPostselectedJointLaw G n S D q) = 1 := by
  have hconditional_sum :
      (∑ outcome : ExactOutcome X Y A B n,
        repeatedConditionedOutcomeLaw G n S D outcome) = 1 := by
    exact conditionedEventDistribution_sum
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive
  unfold exactPostselectedJointLaw
  rw [Fintype.sum_prod_type]
  calc
    (∑ seed : ExactRemainingSeed D,
      ∑ outcome : ExactOutcome X Y A B n,
        exactSeedWeight seed *
          repeatedConditionedOutcomeLaw G n S D outcome) =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          (∑ outcome : ExactOutcome X Y A B n,
            repeatedConditionedOutcomeLaw G n S D outcome) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed := by
          rw [hconditional_sum]
          simp
    _ = 1 := exactRemainingSeedWeight_sum D remaining

def exactSourcePushforward
    {K : Type*} [Fintype K]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : ExactJointOutcome X Y A B D → K) :
    K → ℝ :=
  groupedMass projection (exactPostselectedJointLaw G n S D)

theorem exactSourcePushforward_nonneg
    {K : Type*} [Fintype K]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : ExactJointOutcome X Y A B D → K)
    (k : K) :
    0 ≤ exactSourcePushforward G n S D projection k := by
  exact groupedMass_nonneg projection
    (exactPostselectedJointLaw G n S D)
    (exactPostselectedJointLaw_nonneg G n S D positive) k

theorem exactSourcePushforward_sum
    {K : Type*} [Fintype K]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : ExactJointOutcome X Y A B D → K) :
    (∑ k : K,
      exactSourcePushforward G n S D projection k) = 1 := by
  unfold exactSourcePushforward
  rw [groupedMass_sum]
  exact exactPostselectedJointLaw_sum
    G n S D remaining positive

end

end QuantumParallelRepetition

end
