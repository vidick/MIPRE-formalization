/-
Copyright (c) 2026 the openai/ten-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/openai/ten-proofs (commit 94bc0feb, 2026-08-01) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: QuantumParallelRepetition.lean
-/
import Mathlib
import MIPRE.Background.Repetition.TenProofs.QuantumParallelRepetition.Part07

-- Part 8 of 8 of upstream's single module `QuantumParallelRepetition.lean`: its lines
-- 62421-70992, cut between top-level `noncomputable section` blocks by
-- scripts/vendor-repetition.py (the Palomar registry caps a Lean file at 10,000 lines).
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset


noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactSourceHistoryFlag_nonempty_of_positive
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D) :
    Nonempty (ExactHistoryFlag X Y A B D) := by
  classical
  have nonzero :
      (∑ t : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D t) ≠ 0 := by
    rw [exactLocallySampleableLaw_sum
      G n S D remaining positive]
    exact one_ne_zero
  obtain ⟨t, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  exact ⟨t.2.2.2⟩

theorem exactSourceAnswerTypes_nonempty_of_remaining
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card) :
    Nonempty A ∧ Nonempty B := by
  classical
  let i : Fin n :=
    (Classical.choice (Fintype.card_pos_iff.mp
      (exactRemainingCoordinate_card_pos D remaining))).val
  let xs : Fin n → X :=
    fun _ => Classical.choice (gameQuestionX_nonempty G)
  let ys : Fin n → Y :=
    fun _ => Classical.choice (gameQuestionY_nonempty G)
  have normalized := S.outcomeProbability_normalized xs ys
  constructor
  · by_contra empty
    have zero :
        (∑ a : Fin n → A, ∑ b : Fin n → B,
          S.outcomeProbability xs ys a b) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      exact (empty ⟨a i⟩).elim
    rw [zero] at normalized
    norm_num at normalized
  · by_contra empty
    have zero :
        (∑ a : Fin n → A, ∑ b : Fin n → B,
          S.outcomeProbability xs ys a b) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      exact (empty ⟨b i⟩).elim
    rw [zero] at normalized
    norm_num at normalized

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

def physical8SelectedGlobalTargetWorkEquiv
    (P N d m : ℕ) :
    UnconditionalSelectedCopyLocalIndex P d N m ≃
      Fin d × (Fin P × Fin (N * m)) where
  toFun q := (q.1.2, (q.1.1, q.2))
  invFun q := ⟨(q.2.1, q.1), q.2.2⟩
  left_inv := by
    rintro ⟨⟨phase, atom⟩, work⟩
    rfl
  right_inv := by
    rintro ⟨atom, phase, work⟩
    rfl

def physical8OneScaleActualGlobalFiberEquiv
    {P N d L m : ℕ} {R : Type}
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (j : Fin L) :
    UnconditionalSourcePhysicalStoppingPhaseFiber 1 P N d L m ≃
      Fin d ×
        ((Fin P × Fin (N * m)) ×
          UnconditionalSourceFlagControlledRetainedIndex
            (N := N) (d := d) j R) :=
  (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      phaseSplit j).trans
    ((Equiv.prodCongr
        (physical8SelectedGlobalTargetWorkEquiv P N d m)
        (Equiv.refl
          (UnconditionalSourceFlagControlledRetainedIndex
            (N := N) (d := d) j R))).trans
      (Equiv.prodAssoc (Fin d) (Fin P × Fin (N * m))
        (UnconditionalSourceFlagControlledRetainedIndex
          (N := N) (d := d) j R)))

def physical8OneScaleOriginalFlagPOVM
    {C Z : Type*} [Fintype C] [DecidableEq C]
    {P N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (default : C) (sourcePOVM : Z → POVM C (Fin d)) :
    Fin (L + 1) → Z →
      POVM C
        (UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m) :=
  Fin.cases
    (fun _ => deterministicOutcomePOVM default)
    (fun j x =>
      directDSVActualReindexedRetainedPOVM
        (physical8OneScaleActualGlobalFiberEquiv
          (N := N) (d := d) (m := m) phaseSplit j)
        (sourcePOVM x))

def physical8OneScaleActualAliceStoppingUnitary
    {F Z : Type*} {P N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (Q : ℕ) (width : Fin 1 → ℝ)
    (schedule : Fin L → Fin 1)
    (target : F → Z → BipartiteUnitVector d)
    (cleanup : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    F → Z → Matrix.unitaryGroup
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m) ℂ :=
  fun flag x =>
    coherentSharedRandomControlledUnitary
        (unconditionalSourceFlagControlledFiniteStageDecoder
          phaseSplit Q width schedule (target flag x)
          (dSVUniformDensityAliceHistorySpectralCopy
            (N := N) (target flag x)) cleanup) *
      unconditionalSourcePhysicalCleanedTargetFirstUnitary
        1 P N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
          1 P N d L m width schedule (target flag x))

def physical8OneScaleActualBobStoppingUnitary
    {F Z : Type*} {P N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (Q : ℕ) (width : Fin 1 → ℝ)
    (schedule : Fin L → Fin 1)
    (target : F → Z → BipartiteUnitVector d)
    (cleanup : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    F → Z → Matrix.unitaryGroup
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m) ℂ :=
  fun flag y =>
    coherentSharedRandomControlledUnitary
        (unconditionalSourceFlagControlledFiniteStageDecoder
          phaseSplit Q width schedule (target flag y)
          ((dSVUniformDensityBobHistoryCopyBasis
            (N := N) (target flag y))⁻¹) cleanup) *
      unconditionalSourcePhysicalCleanedTargetFirstUnitary
        1 P N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
          1 P N d L m width schedule (target flag y))

def physical8OneScaleActualSourceFlaggedStrategy
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (w : ℝ) (N L P Q m : ℕ)
    (phases : 0 < P) (grid : 0 < N) (harmonic : 0 < m)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) : Strategy G := by
  classical
  let d : ℕ := Fintype.card
    (ExactGlobalHistoryLocalIndex G n S D)
  have dimension : 0 < d :=
    exactGlobalHistoryLocalIndex_card_pos G n S D
  let R : Type := Fin (Fintype.card (Fin (1 - 1) → Fin P))
  let phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R :=
    (unconditionalActualMultiscalePhaseIndexEquiv
      (B := P) (0 : Fin 1)).symm
  let width : Fin 1 → ℝ := fun _ => w
  let schedule : Fin L → Fin 1 := fun _ => 0
  let F : Type := ExactSourceSharedFlag X Y A B D denominator
  let ξ : F → X → BipartiteUnitVector d :=
    fun flag x => exactGlobalHistoryFinGamma G n S D
      (exactSourceAlicePermutationHistory
        D denominator numerator nonempty flag x) x
  let ζ : F → Y → BipartiteUnitVector d :=
    fun flag y => exactGlobalHistoryFinPhi G n S D
      (exactSourceBobPermutationHistory
        D denominator numerator nonempty flag y) y
  let a₀ : A := Classical.choice
    (exactSourceAnswerTypes_nonempty_of_remaining
      G n S D remaining).1
  let b₀ : B := Classical.choice
    (exactSourceAnswerTypes_nonempty_of_remaining
      G n S D remaining).2
  let globalAlice : X → POVM A (Fin d) := fun x =>
    reindexedPOVM (finCongr (Nat.mul_one d))
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystAlicePOVM G n S D 1 a₀ x))
  let globalBob : Y → POVM B (Fin d) := fun y =>
    reindexedPOVM (finCongr (Nat.mul_one d))
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystBobPOVM G n S D 1 b₀ y))
  let PA : F → Fin (L + 1) → X →
      POVM A
        (UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m) :=
    fun flag => physical8OneScaleOriginalFlagPOVM
      (N := N) (d := d) (m := m) phaseSplit a₀
      (fun x => unitaryConjugatePOVM
        (conjugateUnitary
          (dSVDensityRationalCanonicalAliceBasis (ξ flag x)))
        (globalAlice x))
  let PB : F → Fin (L + 1) → Y →
      POVM B
        (UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m) :=
    fun flag => physical8OneScaleOriginalFlagPOVM
      (N := N) (d := d) (m := m) phaseSplit b₀
      (fun y => unitaryConjugatePOVM
        (conjugateUnitary
          (dSVUniformDensityThresholdLeftBobBasis (ζ flag y)))
        (globalBob y))
  let U := physical8OneScaleActualAliceStoppingUnitary
    (P := P) (N := N) (d := d) (L := L) (m := m)
    phaseSplit Q width schedule ξ UA
  let V := physical8OneScaleActualBobStoppingUnitary
    (P := P) (N := N) (d := d) (L := L) (m := m)
    phaseSplit Q width schedule ζ UB
  let prepared : F → EuclideanSpace ℂ
      ((Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N d L m) ×
       (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N d L m)) :=
    fun _ => unconditionalSourcePhysicalCleanedStoppingFixedSource
      1 P N d L m
  have prepared_normalized : ∀ flag : F, ‖prepared flag‖ = 1 := by
    intro flag
    exact unconditionalSourcePhysicalCleanedStoppingFixedSource_norm
      phases grid dimension harmonic
  exact pureFlaggedStrategy G
    (exactSourceSharedFlagWeight D denominator)
    (exactSourceSharedFlagWeight_nonneg D denominator)
    (exactSourceSharedFlagWeight_sum D remaining denominator)
    prepared prepared_normalized
    (fun flag x => unitaryConjugatePOVM (U flag x)
      (dependentBlockPOVM (fun r => PA flag r x)))
    (fun flag y => unitaryConjugatePOVM (V flag y)
      (dependentBlockPOVM (fun r => PB flag r y)))

abbrev unconditionalOneScaleActualSourceFlaggedStrategy :=
  @physical8OneScaleActualSourceFlaggedStrategy

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

def unconditionalActualOneScaleFixedSourcePhaseSplit (P : ℕ) :
    DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
      Fin P × UnconditionalActualCanonicalRetainedPhaseIndex 1 P :=
  (unconditionalActualMultiscalePhaseIndexEquiv
    (B := P) (0 : Fin 1)).symm

theorem unconditionalActualOneScaleFlagControlledFiniteStageDecoder_eq
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
    unconditionalSourceFlagControlledFiniteStageDecoder
        phaseSplit Q width schedule ξ spectral A =
      unconditionalActualCleanedSelectedFiniteStageDecoder
        phaseSplit Q width schedule ξ spectral A := by
  rfl

def unconditionalActualOneScaleFixedSourceDecodedState
    {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    EuclideanSpace ℂ
      ((Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N d L m) ×
       (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N d L m)) :=
  dSVUniformDensityPhysicalAsyncSigmaContinuation
    (unconditionalSourceFlagControlledFiniteStageDecoder
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      Q width schedule ξ
      (dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ) A)
    (unconditionalSourceFlagControlledFiniteStageDecoder
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      Q width schedule ζ
      ((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ζ)⁻¹) C)
    (actualStoppingQuestionLocalAction
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        1 P N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
          1 P N d L m width schedule ξ))
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        1 P N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
          1 P N d L m width schedule ζ))
      (unconditionalSourcePhysicalCleanedStoppingFixedSource
        1 P N d L m))

theorem unconditionalActualOneScaleFixedSourcePhysicalQuestionAction
    {F X Y : Type} {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ : F → X → BipartiteUnitVector d)
    (ζ : F → Y → BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (flag : F) (x : X) (y : Y) :
    actualStoppingQuestionLocalAction
        (physical8OneScaleActualAliceStoppingUnitary
          (P := P) (N := N) (d := d) (L := L) (m := m)
          (unconditionalActualOneScaleFixedSourcePhaseSplit P)
          Q width schedule ξ A flag x)
        (physical8OneScaleActualBobStoppingUnitary
          (P := P) (N := N) (d := d) (L := L) (m := m)
          (unconditionalActualOneScaleFixedSourcePhaseSplit P)
          Q width schedule ζ C flag y)
        (unconditionalSourcePhysicalCleanedStoppingFixedSource
          1 P N d L m) =
      unconditionalActualOneScaleFixedSourceDecodedState
        Q width schedule (ξ flag x) (ζ flag y) A C := by
  classical
  unfold physical8OneScaleActualAliceStoppingUnitary
    physical8OneScaleActualBobStoppingUnitary
    unconditionalActualOneScaleFixedSourceDecodedState
    actualStoppingQuestionLocalAction
    dSVUniformDensityPhysicalAsyncSigmaContinuation
  simp only []
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul]
  rfl

theorem unconditionalActualOneScaleFixedSourceDecodedMatchedBranch
    {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L)
    (positive : 0 < width (schedule j)) (grid : 0 < N) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualOneScaleFixedSourcePhaseSplit P) j
        (actualStoppingBranchVector
          (unconditionalActualOneScaleFixedSourceDecodedState
            Q width schedule ξ ζ A C) j.succ j.succ) =
      unconditionalSelectedCopyCleanedMatchedBranch
        (N := N) (B := P) (m := m)
        Q width schedule ξ ζ A C j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := 1) (B := P) (N := N) (d := d) (L := L) j) := by
  have sameScale : schedule j = (0 : Fin 1) :=
    Subsingleton.elim _ _
  have samePhase :
      (unconditionalActualMultiscalePhaseIndexEquiv
        (B := P) (schedule j)).symm =
        unconditionalActualOneScaleFixedSourcePhaseSplit P := by
    simp only [unconditionalActualOneScaleFixedSourcePhaseSplit]
    rw [sameScale]
  have decoded :=
    unconditionalActualFixedSourceDecodedMatchedBranch
      (S := 1) (B := P) (N := N) (d := d) (L := L) (m := m)
      Q width schedule ξ ζ A C j positive grid
  rw [samePhase] at decoded
  simpa only [unconditionalActualOneScaleFixedSourceDecodedState,
    unconditionalActualOneScaleFlagControlledFiniteStageDecoder_eq]
    using decoded

theorem
    unconditionalActualOneScalePhysicalQuestionDecodedMatchedBranch
    {F X Y : Type} {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ : F → X → BipartiteUnitVector d)
    (ζ : F → Y → BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (grid : 0 < N)
    (flag : F) (x : X) (y : Y) (j : Fin L)
    (positive : 0 < width (schedule j)) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualOneScaleFixedSourcePhaseSplit P) j
        (actualStoppingBranchVector
          (actualStoppingQuestionLocalAction
            (physical8OneScaleActualAliceStoppingUnitary
              (P := P) (N := N) (d := d) (L := L) (m := m)
              (unconditionalActualOneScaleFixedSourcePhaseSplit P)
              Q width schedule ξ A flag x)
            (physical8OneScaleActualBobStoppingUnitary
              (P := P) (N := N) (d := d) (L := L) (m := m)
              (unconditionalActualOneScaleFixedSourcePhaseSplit P)
              Q width schedule ζ C flag y)
            (unconditionalSourcePhysicalCleanedStoppingFixedSource
              1 P N d L m)) j.succ j.succ) =
      unconditionalSelectedCopyCleanedMatchedBranch
        (N := N) (B := P) (m := m)
        Q width schedule (ξ flag x) (ζ flag y) A C j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := 1) (B := P) (N := N) (d := d) (L := L) j) := by
  rw [unconditionalActualOneScaleFixedSourcePhysicalQuestionAction]
  exact unconditionalActualOneScaleFixedSourceDecodedMatchedBranch
    Q width schedule (ξ flag x) (ζ flag y) A C j positive grid

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalConjugatePureVector_sub_norm
    {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℂ ι) :
    ‖unconditionalConjugatePureVector x -
      unconditionalConjugatePureVector y‖ = ‖x - y‖ := by
  have conjugate_sub :
      unconditionalConjugatePureVector x -
          unconditionalConjugatePureVector y =
        unconditionalConjugatePureVector (x - y) := by
    ext i
    simp [unconditionalConjugatePureVector, star_sub]
  rw [conjugate_sub, unconditionalConjugatePureVector_norm]

theorem unconditionalClippedConjugateUnitTarget_distance_sq_le
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d)
    (psi : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖unconditionalConjugatePureVector psi -
      unconditionalConjugatePureVector
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val‖ ^ 2 ≤
      2 * ‖psi - gamma.val‖ ^ 2 +
        8 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  rw [unconditionalConjugatePureVector_sub_norm]
  let accepted : BipartiteUnitVector d :=
    dSVDensityRationalCanonicalAcceptedUnitTarget
      width grid fine gamma
  have triangle : ‖psi - accepted.val‖ ≤
      ‖psi - gamma.val‖ + ‖gamma.val - accepted.val‖ := by
    calc
      ‖psi - accepted.val‖ =
          ‖(psi - gamma.val) + (gamma.val - accepted.val)‖ := by
            congr 1
            abel
      _ ≤ _ := norm_add_le _ _
  have clipping :=
    dSVDensityRationalCanonicalAcceptedUnitTarget_distance_le
      width grid fine gamma
  have clipping_nonnegative :
      0 ≤ 1 / w + (d : ℝ) * w / (N : ℝ) := by
    positivity
  have clipping_squared :
      ‖gamma.val - accepted.val‖ ^ 2 ≤
        4 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
    change
      ‖gamma.val -
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val‖ ^ 2 ≤ _
    nlinarith [
      norm_nonneg
        (gamma.val -
          (dSVDensityRationalCanonicalAcceptedUnitTarget
            width grid fine gamma).val),
      Real.sqrt_nonneg (1 / w + (d : ℝ) * w / (N : ℝ)),
      Real.sq_sqrt clipping_nonnegative]
  change ‖psi - accepted.val‖ ^ 2 ≤ _
  nlinarith [norm_nonneg (psi - accepted.val),
    norm_nonneg (psi - gamma.val),
    norm_nonneg (gamma.val - accepted.val),
    sq_nonneg (‖psi - gamma.val‖ - ‖gamma.val - accepted.val‖)]

theorem unconditionalMatchedVerifierTensor_sub_right
    {s t : Type*} [Fintype s] [Fintype t]
    (x y : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    unconditionalMatchedVerifierTensor x work -
      unconditionalMatchedVerifierTensor y work =
        unconditionalMatchedVerifierTensor (x - y) work := by
  ext q
  change x q.1 * work q.2 - y q.1 * work q.2 =
    (x q.1 - y q.1) * work q.2
  ring

theorem
    unconditionalWeightedClippedConjugateUnitSource_distance_sq_le
    {J : Type*} [Fintype J]
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (weight : J → ℝ)
    (weight_nonnegative : ∀ j, 0 ≤ weight j)
    (weight_normalized : (∑ j, weight j) = 1)
    (gamma : J → BipartiteUnitVector d)
    (psi : J → EuclideanSpace ℂ (Fin d × Fin d))
    (energy : ℝ)
    (energy_bound :
      (∑ j, weight j * ‖psi j - (gamma j).val‖ ^ 2) ≤ energy) :
    (∑ j, weight j *
      ‖unconditionalConjugatePureVector (psi j) -
        unconditionalConjugatePureVector
          (dSVDensityRationalCanonicalAcceptedUnitTarget
            width grid fine (gamma j)).val‖ ^ 2) ≤
      2 * energy + 8 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  classical
  let clip : ℝ := 1 / w + (d : ℝ) * w / (N : ℝ)
  calc
    _ ≤ ∑ j, weight j *
        (2 * ‖psi j - (gamma j).val‖ ^ 2 + 8 * clip) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (unconditionalClippedConjugateUnitTarget_distance_sq_le
          width grid fine (gamma j) (psi j))
        (weight_nonnegative j)
    _ = 2 * (∑ j, weight j * ‖psi j - (gamma j).val‖ ^ 2) +
        (8 * clip) * (∑ j, weight j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 2 * (∑ j, weight j * ‖psi j - (gamma j).val‖ ^ 2) +
        8 * clip := by
      rw [weight_normalized]
      ring
    _ ≤ 2 * energy + 8 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
      dsimp [clip]
      linarith

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def unconditionalExactFairGammaUnit
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (u : ExactLocallySampleableTuple X Y A B D) :
    BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  ⟨exactSourceTupleGamma G n S D u,
    exactSourceTupleGamma_norm G n S D u⟩

theorem unconditionalExactFairGammaUnit_eq_global
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (u : ExactLocallySampleableTuple X Y A B D) :
    unconditionalExactFairGammaUnit G n S D u =
      exactGlobalHistoryFinGamma
        G n S D u.2.2.2 u.2.1 := by
  apply Subtype.ext
  rfl

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalCoherentPhaseConstantWork_sub
    {H : Type*} [Fintype H] {B m : ℕ}
    (x y : EuclideanSpace ℂ (H × H))
    (work : EuclideanSpace ℂ (Fin m × Fin m)) :
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B x (fun _ _ _ => work) -
      dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B y (fun _ _ _ => work) =
      dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B (x - y) (fun _ _ _ => work) := by
  ext ⟨⟨⟨φ, i⟩, a⟩, ⟨⟨ψ, j⟩, b⟩⟩
  change
    (ePRState B (φ, ψ) * x (i, j)) * work (a, b) -
      (ePRState B (φ, ψ) * y (i, j)) * work (a, b) =
      (ePRState B (φ, ψ) *
        (x (i, j) - y (i, j))) * work (a, b)
  ring

theorem unconditionalStoppedPhaseHarmonic_distance_sq
    {H : Type*} [Fintype H] {B m : ℕ}
    (phases : 0 < B) (harmonic : 0 < m)
    (x y : EuclideanSpace ℂ (H × H)) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B x (fun _ _ _ => embezzlementState m) -
      dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B y (fun _ _ _ => embezzlementState m)‖ ^ 2 =
      ‖x - y‖ ^ 2 := by
  rw [unconditionalCoherentPhaseConstantWork_sub,
    unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
      phases,
    embezzlementState_norm m harmonic]
  ring

theorem unconditionalStoppedPhaseHarmonicDistance_sum_le
    {J K : Type*} [Fintype K]
    {d B m : ℕ}
    (phases : 0 < B) (harmonic : 0 < m)
    (x y : J → EuclideanSpace ℂ (Fin d × Fin d))
    {T : J × K → Type*} [∀ p, Fintype (T p)]
    (work : (p : J × K) → EuclideanSpace ℂ (T p))
    (work_row : ∀ j : J, (∑ k : K, ‖work (j, k)‖ ^ 2) ≤ 1)
    (j : J) :
    (∑ k : K,
      ‖unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B (x j) (fun _ _ _ => embezzlementState m))
          (work (j, k)) -
        unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B (y j) (fun _ _ _ => embezzlementState m))
          (work (j, k))‖ ^ 2) ≤
      ‖x j - y j‖ ^ 2 := by
  classical
  let sx := dSVDensityRationalPublicBucketCoherentPhaseSigmaState
    B (x j) (fun _ _ _ => embezzlementState m)
  let sy := dSVDensityRationalPublicBucketCoherentPhaseSigmaState
    B (y j) (fun _ _ _ => embezzlementState m)
  have stage : ‖sx - sy‖ ^ 2 = ‖x j - y j‖ ^ 2 :=
    unconditionalStoppedPhaseHarmonic_distance_sq
      phases harmonic (x j) (y j)
  change
    (∑ k : K,
      ‖unconditionalMatchedVerifierTensor sx (work (j, k)) -
        unconditionalMatchedVerifierTensor sy
          (work (j, k))‖ ^ 2) ≤ _
  calc
    _ = ∑ k : K, ‖sx - sy‖ ^ 2 * ‖work (j, k)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [unconditionalMatchedVerifierTensor_sub_right,
        unconditionalMatchedVerifierTensor_norm_sq]
    _ = ‖sx - sy‖ ^ 2 *
        (∑ k : K, ‖work (j, k)‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ ‖sx - sy‖ ^ 2 :=
      mul_le_of_le_one_right (sq_nonneg _) (work_row j)
    _ = _ := stage

theorem unconditionalWeightedStoppedPhaseHarmonicClippedUnit_le
    {J K : Type*} [Fintype J] [Fintype K]
    {d N B m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (phases : 0 < B) (harmonic : 0 < m)
    (weight : J → ℝ)
    (weight_nonnegative : ∀ j, 0 ≤ weight j)
    (weight_normalized : (∑ j, weight j) = 1)
    (gamma : J → BipartiteUnitVector d)
    (psi : J → EuclideanSpace ℂ (Fin d × Fin d))
    (energy : ℝ)
    (energy_bound :
      (∑ j, weight j * ‖psi j - (gamma j).val‖ ^ 2) ≤ energy)
    {T : J × K → Type*} [∀ p, Fintype (T p)]
    (work : (p : J × K) → EuclideanSpace ℂ (T p))
    (work_row : ∀ j : J, (∑ k : K, ‖work (j, k)‖ ^ 2) ≤ 1) :
    (∑ j : J, weight j * ∑ k : K,
      ‖unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B (unconditionalConjugatePureVector (psi j))
            (fun _ _ _ => embezzlementState m))
          (work (j, k)) -
        unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B
            (unconditionalConjugatePureVector
              (dSVDensityRationalCanonicalAcceptedUnitTarget
                width grid fine (gamma j)).val)
            (fun _ _ _ => embezzlementState m))
          (work (j, k))‖ ^ 2) ≤
      2 * energy + 8 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  classical
  calc
    _ ≤ ∑ j : J, weight j *
        ‖unconditionalConjugatePureVector (psi j) -
          unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              width grid fine (gamma j)).val‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (unconditionalStoppedPhaseHarmonicDistance_sum_le
          phases harmonic
          (fun i => unconditionalConjugatePureVector (psi i))
          (fun i => unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              width grid fine (gamma i)).val)
          work work_row j)
        (weight_nonnegative j)
    _ ≤ _ :=
      unconditionalWeightedClippedConjugateUnitSource_distance_sq_le
        width grid fine weight weight_nonnegative weight_normalized
        gamma psi energy energy_bound

theorem unconditionalExactFairStoppedPhaseHarmonicClippedUnit_le
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    {w : ℝ} {N P m : ℕ}
    (width : 0 < w) (grid : 0 < N)
    (fine :
      (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) : ℝ) /
        (N : ℝ) < 1 / (w + 1))
    (phases : 0 < P) (harmonic : 0 < m)
    {K : Type*} [Fintype K]
    {T : ExactLocallySampleableTuple X Y A B D × K → Type*}
    [∀ p, Fintype (T p)]
    (work :
      (p : ExactLocallySampleableTuple X Y A B D × K) →
        EuclideanSpace ℂ (T p))
    (work_row :
      ∀ u : ExactLocallySampleableTuple X Y A B D,
        (∑ k : K, ‖work (u, k)‖ ^ 2) ≤ 1) :
    (∑ u : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D u *
        ∑ k : K,
          ‖unconditionalMatchedVerifierTensor
              (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
                P
                (unconditionalConjugatePureVector
                  (exactSourceTuplePsi G n S D u))
                (fun _ _ _ => embezzlementState m))
              (work (u, k)) -
            unconditionalMatchedVerifierTensor
              (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
                P
                (unconditionalConjugatePureVector
                  (dSVDensityRationalCanonicalAcceptedUnitTarget
                    width grid fine
                    (unconditionalExactFairGammaUnit
                      G n S D u)).val)
                (fun _ _ _ => embezzlementState m))
              (work (u, k))‖ ^ 2) ≤
      16 * martingaleRate G n S D +
        8 * (1 / w +
          (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) : ℝ) *
            w / (N : ℝ)) := by
  classical
  have source :=
    (exactSourceStateDistanceBound_of_positive
      G n S D remaining positive).1
  have energy :
      (∑ u : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D u *
          ‖exactSourceTuplePsi G n S D u -
            (unconditionalExactFairGammaUnit
              G n S D u).val‖ ^ 2) ≤
        8 * martingaleRate G n S D := by
    simpa only [unconditionalExactFairGammaUnit, norm_sub_rev]
      using source
  have result :=
    unconditionalWeightedStoppedPhaseHarmonicClippedUnit_le
      width grid fine phases harmonic
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableLaw_nonneg G n S D positive)
      (exactLocallySampleableLaw_sum G n S D remaining positive)
      (unconditionalExactFairGammaUnit G n S D)
      (exactSourceTuplePsi G n S D)
      (8 * martingaleRate G n S D) energy work work_row
  convert result using 1
  ring

theorem unconditionalCanonicalRaw_eq_norm_smul_unit
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d) :
    dSVDensityRationalCanonicalAcceptedTarget w N gamma =
      ‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ •
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val := by
  exact (NormedSpace.norm_smul_normalize
    (dSVDensityRationalCanonicalAcceptedTarget
      w N gamma)).symm

theorem unconditionalConjugateCanonicalRaw_eq_norm_smul_unit
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d) :
    unconditionalConjugatePureVector
        (dSVDensityRationalCanonicalAcceptedTarget
          w N gamma) =
      ‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ •
        unconditionalConjugatePureVector
          (dSVDensityRationalCanonicalAcceptedUnitTarget
            width grid fine gamma).val := by
  have raw := unconditionalCanonicalRaw_eq_norm_smul_unit
    width grid fine gamma
  ext i
  have coefficient := congrArg
    (fun z : EuclideanSpace ℂ (Fin d × Fin d) => z i) raw
  change
    star (dSVDensityRationalCanonicalAcceptedTarget
      w N gamma i) =
      (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ : ℂ) *
        star
          ((dSVDensityRationalCanonicalAcceptedUnitTarget
            width grid fine gamma).val i)
  change
    dSVDensityRationalCanonicalAcceptedTarget
      w N gamma i =
      (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ : ℂ) *
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val i at coefficient
  rw [coefficient]
  simp

theorem unconditionalPhaseCanonicalRaw_eq_norm_smul_unit
    {d N B m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d) :
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B
        (unconditionalConjugatePureVector
          (dSVDensityRationalCanonicalAcceptedTarget
            w N gamma))
        (fun _ _ _ => embezzlementState m) =
      ‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ •
        dSVDensityRationalPublicBucketCoherentPhaseSigmaState
          B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              width grid fine gamma).val)
          (fun _ _ _ => embezzlementState m) := by
  have raw :=
    unconditionalConjugateCanonicalRaw_eq_norm_smul_unit
      width grid fine gamma
  ext ⟨⟨⟨φ, i⟩, a⟩, ⟨⟨ψ, j⟩, b⟩⟩
  have coefficient := congrArg
    (fun z : EuclideanSpace ℂ (Fin d × Fin d) => z (i, j)) raw
  change
    (ePRState B (φ, ψ) *
      star (dSVDensityRationalCanonicalAcceptedTarget
        w N gamma (i, j))) *
      embezzlementState m (a, b) =
    (‖dSVDensityRationalCanonicalAcceptedTarget
      w N gamma‖ : ℂ) *
      ((ePRState B (φ, ψ) *
        star ((dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val (i, j))) *
        embezzlementState m (a, b))
  change
    star (dSVDensityRationalCanonicalAcceptedTarget
      w N gamma (i, j)) =
      (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ : ℂ) *
        star ((dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val (i, j)) at coefficient
  rw [coefficient]
  ring

theorem unconditionalMatchedTensor_real_smul_work
    {s t : Type*} [Fintype s] [Fintype t]
    (c : ℝ)
    (stage : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    c • unconditionalMatchedVerifierTensor stage work =
      unconditionalMatchedVerifierTensor stage (c • work) := by
  ext q
  change (c : ℂ) * (stage q.1 * work q.2) =
    stage q.1 * ((c : ℂ) * work q.2)
  ring

theorem unconditionalPhaseCanonical_sourceScale_absorbed
    {d N B m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d)
    {T : Type*} [Fintype T]
    (work : EuclideanSpace ℂ T) :
    Real.sqrt (w * (d : ℝ)) •
      unconditionalMatchedVerifierTensor
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
          B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              width grid fine gamma).val)
          (fun _ _ _ => embezzlementState m))
        ((‖dSVDensityRationalCanonicalAcceptedTarget
            w N gamma‖ / Real.sqrt (w * (d : ℝ))) • work) =
      unconditionalMatchedVerifierTensor
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
          B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedTarget
              w N gamma))
          (fun _ _ _ => embezzlementState m))
        work := by
  let scale : ℝ := Real.sqrt (w * (d : ℝ))
  let mass : ℝ :=
    ‖dSVDensityRationalCanonicalAcceptedTarget w N gamma‖
  let stage :=
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState
      B
      (unconditionalConjugatePureVector
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val)
      (fun _ _ _ => embezzlementState m)
  have real_dimension : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  have scale_positive : 0 < scale := by
    dsimp [scale]
    positivity
  have scalar : scale * (mass / scale) = mass := by
    field_simp [ne_of_gt scale_positive]
  have factor :=
    unconditionalPhaseCanonicalRaw_eq_norm_smul_unit
      (B := B) (m := m) width grid fine gamma
  change
    scale •
        unconditionalMatchedVerifierTensor
          stage ((mass / scale) • work) = _
  calc
    scale •
        unconditionalMatchedVerifierTensor
          stage ((mass / scale) • work) =
        unconditionalMatchedVerifierTensor
          stage (scale • ((mass / scale) • work)) :=
      unconditionalMatchedTensor_real_smul_work
        scale stage ((mass / scale) • work)
    _ = unconditionalMatchedVerifierTensor
          stage (mass • work) := by
      rw [smul_smul, scalar]
    _ = mass •
          unconditionalMatchedVerifierTensor stage work :=
      (unconditionalMatchedTensor_real_smul_work
        mass stage work).symm
    _ = unconditionalMatchedVerifierTensor
          (mass • stage) work :=
      unconditionalMixedConjugateSelectedBranch_tensor_smul
        mass stage work
    _ = _ := by
      rw [factor]

theorem unconditionalCanonicalAcceptedScale_sq_eq_diagonalBorn
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (gamma : BipartiteUnitVector d) :
    (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ / Real.sqrt (w * (d : ℝ))) ^ 2 =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w gamma := by
  have dimension_real : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  rw [div_pow,
    dSVDensityRationalCanonicalAcceptedTarget_norm_sq
      width N gamma,
    Real.sq_sqrt (by positivity : 0 ≤ w * (d : ℝ)),
    dSVDensityRationalPhysicalDiagonalBornSuccess_eq]
  field_simp [ne_of_gt width, ne_of_gt dimension_real]

theorem unconditionalNormalizedCanonicalRetainedWork_norm_sq
    {S N d L B m : ℕ} {T : Type*} [Fintype T]
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (gamma phi : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ T)
    (rest_unit : ‖rest‖ = 1) :
    ‖(‖dSVDensityRationalCanonicalAcceptedTarget
          (width (schedule j)) N gamma‖ /
        Real.sqrt ((width (schedule j)) * (d : ℝ))) •
      unconditionalSelectedCopyRetainedWork
        (N := N) width schedule gamma phi j rest‖ ^ 2 =
      ‖unconditionalSelectedCopyIdealMatchedBranch
        (N := N) (B := B) (m := m)
        width schedule gamma phi j rest‖ ^ 2 := by
  have positive := width_positive (schedule j)
  have ratio_nonnegative :
      0 ≤ ‖dSVDensityRationalCanonicalAcceptedTarget
          (width (schedule j)) N gamma‖ /
        Real.sqrt ((width (schedule j)) * (d : ℝ)) := by
    exact div_nonneg (norm_nonneg _)
      (Real.sqrt_nonneg _)
  calc
    _ =
      (‖dSVDensityRationalCanonicalAcceptedTarget
          (width (schedule j)) N gamma‖ /
        Real.sqrt ((width (schedule j)) * (d : ℝ))) ^ 2 *
      ‖unconditionalSelectedCopyRetainedWork
        (N := N) width schedule gamma phi j rest‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ratio_nonnegative, mul_pow]
    _ =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule j)) gamma *
      (dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule gamma phi j.val * ‖rest‖ ^ 2) := by
      rw [unconditionalCanonicalAcceptedScale_sq_eq_diagonalBorn
        positive grid dimension gamma,
        unconditionalSelectedCopyRetainedWork_norm_sq]
    _ =
      dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule gamma phi j.val *
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule j)) gamma := by
      rw [rest_unit]
      ring
    _ = _ :=
      (unconditionalSelectedCopyIdealMatchedBranch_norm_sq
        phases grid dimension harmonic width width_positive schedule
        gamma phi j rest rest_unit).symm

theorem integratorActualCanonicalRetainedPhaseTail_norm
    {S B N d L : ℕ}
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d)
    (j : Fin L) :
    ‖unconditionalActualCanonicalRetainedPhaseTail
        (S := S) (B := B) (N := N) (d := d) (L := L) j‖ = 1 := by
  have residual : 0 < Fintype.card (Fin (S - 1) → Fin B) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun _ => ⟨0, phases⟩⟩
  change
    ‖unconditionalMatchedVerifierTensor
        (dSVUniformDensityIndependentSharedState
          (L - j.val) N d)
        (ePRState
          (Fintype.card (Fin (S - 1) → Fin B)))‖ = 1
  rw [unconditionalMatchedVerifierTensor_norm,
    dSVUniformDensityIndependentSharedState_norm
      (L - j.val) grid dimension,
    ePRState_norm _ residual]
  norm_num

abbrev IntegratorActualC485TailIndex
    (S B N d L : ℕ) (j : Fin L) :=
  (((Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d) ×
    (Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d)) ×
   (UnconditionalActualCanonicalRetainedPhaseIndex S B ×
    UnconditionalActualCanonicalRetainedPhaseIndex S B))

abbrev IntegratorActualC485RetainedIndex
    (S B N d L : ℕ) (j : Fin L) :=
  (Fin j.val →
    (DSVUniformDensityThresholdLocalIndex N d ×
     DSVUniformDensityThresholdLocalIndex N d)) ×
    IntegratorActualC485TailIndex S B N d L j

abbrev IntegratorActualC485BranchSpace
    (S B N d L m : ℕ) (j : Fin L) :=
  EuclideanSpace ℂ
    ((UnconditionalSelectedCopyLocalIndex B d N m ×
      UnconditionalSelectedCopyLocalIndex B d N m) ×
     IntegratorActualC485RetainedIndex S B N d L j)

def integratorActualC485OriginalRetainedWork
    {S B N d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    EuclideanSpace ℂ
      (IntegratorActualC485RetainedIndex S B N d L j) :=
  unconditionalSelectedCopyRetainedWork
    (N := N) width schedule ξ ζ j
    (unconditionalActualCanonicalRetainedPhaseTail
      (S := S) (B := B) (N := N) (d := d) (L := L) j)

def integratorActualC485NormalizedDiagonalWork
    {S B N d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    EuclideanSpace ℂ
      (IntegratorActualC485RetainedIndex S B N d L j) :=
  (‖dSVDensityRationalCanonicalAcceptedTarget
      (width (schedule j)) N ξ‖ /
    Real.sqrt (width (schedule j) * (d : ℝ))) •
      integratorActualC485OriginalRetainedWork
        (B := B) width schedule ξ ζ j

def integratorActualC485CleanedVector
    {S B N d L m : ℕ}
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    IntegratorActualC485BranchSpace S B N d L m j :=
  unconditionalMixedConjugateSelectedBranchLocalAction
    (unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) B
      (conjugateUnitary
        (dSVDensityRationalCanonicalAliceBasis ξ)))
    (unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) B
      (conjugateUnitary
        (dSVUniformDensityThresholdLeftBobBasis ζ)))
    (unconditionalSelectedCopyCleanedMatchedBranch
      (N := N) (B := B) (m := m)
      Q width schedule ξ ζ A C j
      (unconditionalActualCanonicalRetainedPhaseTail
        (S := S) (B := B) (N := N) (d := d) (L := L) j))

def integratorActualC485CanonicalVector
    {S B N d L m : ℕ}
    {width : Fin S → ℝ}
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L)
    (positive : 0 < width (schedule j))
    (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    IntegratorActualC485BranchSpace S B N d L m j :=
  unconditionalMatchedVerifierTensor
    (dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
      (unconditionalConjugatePureVector
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          positive grid fine ξ).val)
      (fun _ _ _ => embezzlementState (N * m)))
    (integratorActualC485NormalizedDiagonalWork
      (B := B) width schedule ξ ζ j)

def integratorActualC485SourceVector
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (j : Fin L) :
    IntegratorActualC485BranchSpace S B N d L m j :=
  unconditionalMatchedVerifierTensor
    (dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
      (unconditionalConjugatePureVector ψ)
      (fun _ _ _ => embezzlementState (N * m)))
    (integratorActualC485NormalizedDiagonalWork
      (B := B) width schedule ξ ζ j)

theorem unconditionalActualC485NormalizedDiagonalWork_mass_sum_le_one
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    (∑ j : Fin L,
      ‖integratorActualC485NormalizedDiagonalWork
          (S := S) (B := B) (N := N) (d := d) (L := L)
          width schedule ξ ζ j‖ ^ 2) ≤ 1 := by
  classical
  calc
    _ = ∑ j : Fin L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule j)) ξ := by
      apply Finset.sum_congr rfl
      intro j _
      unfold integratorActualC485NormalizedDiagonalWork
        integratorActualC485OriginalRetainedWork
      rw [unconditionalNormalizedCanonicalRetainedWork_norm_sq
        (B := B) (m := m) phases grid dimension harmonic
        width positive schedule ξ ζ j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := S) (B := B) (N := N) (d := d) (L := L) j)
        (integratorActualCanonicalRetainedPhaseTail_norm
          phases grid dimension j)]
      exact unconditionalSelectedCopyIdealMatchedBranch_norm_sq
        phases grid dimension harmonic width positive schedule ξ ζ j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := S) (B := B) (N := N) (d := d) (L := L) j)
        (integratorActualCanonicalRetainedPhaseTail_norm
          phases grid dimension j)
    _ ≤ 1 :=
      dSVDensityRationalHeterogeneousPhysicalDiagonalSurvival_budget
        grid dimension width schedule ξ ζ

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalActualSelectedBranchLocalAction_decidableEq_irrel
    {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ]
    (left right : DecidableEq τ)
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ ((ι × ι) × τ)) :
    @unconditionalMixedConjugateSelectedBranchLocalAction
      ι τ inferInstance inferInstance inferInstance left U V z =
    @unconditionalMixedConjugateSelectedBranchLocalAction
      ι τ inferInstance inferInstance inferInstance right U V z := by
  have same : left = right := Subsingleton.elim left right
  cases same
  rfl

theorem unconditionalActualC485CanonicalCorrectedIdeal_generic
    {S N d L B m : ℕ} {T : Type*}
    [Fintype T] [DecidableEq T]
    {width : Fin S → ℝ}
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (positive : 0 < width (schedule j))
    (grid : 0 < N) (dimension : 0 < d)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1))
    (rest : EuclideanSpace ℂ T) :
    unconditionalMatchedVerifierTensor
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              positive grid fine ξ).val)
          (fun _ _ _ => embezzlementState (N * m)))
        ((‖dSVDensityRationalCanonicalAcceptedTarget
              (width (schedule j)) N ξ‖ /
            Real.sqrt (width (schedule j) * (d : ℝ))) •
          unconditionalSelectedCopyRetainedWork
            (N := N) width schedule ξ ζ j rest) =
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
          width schedule ξ ζ j rest) := by
  have scale_positive : 0 < Real.sqrt (width (schedule j) * (d : ℝ)) := by
    positivity
  apply smul_right_injective _ scale_positive.ne'
  exact
    (unconditionalPhaseCanonical_sourceScale_absorbed
      (B := B) (m := N * m) positive grid dimension fine ξ
      (unconditionalSelectedCopyRetainedWork
        (N := N) width schedule ξ ζ j rest)).trans
      (unconditionalMixedConjugateSelectedBranchCovariance
        (B := B) (m := m) grid dimension width schedule ξ ζ j
        positive rest).symm

theorem unconditionalActualC485CanonicalVector_eq_correctedIdeal
    {S B N d L m : ℕ}
    {width : Fin S → ℝ}
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (positive : 0 < width (schedule j))
    (grid : 0 < N) (dimension : 0 < d)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    integratorActualC485CanonicalVector
        (B := B) (m := m) schedule ξ ζ j positive grid fine =
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
          width schedule ξ ζ j
          (unconditionalActualCanonicalRetainedPhaseTail
            (S := S) (B := B) (N := N) (d := d) (L := L) j)) := by
  change
    unconditionalMatchedVerifierTensor
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              positive grid fine ξ).val)
          (fun _ _ _ => embezzlementState (N * m)))
        ((‖dSVDensityRationalCanonicalAcceptedTarget
              (width (schedule j)) N ξ‖ /
            Real.sqrt (width (schedule j) * (d : ℝ))) •
          unconditionalSelectedCopyRetainedWork
            (N := N) width schedule ξ ζ j
            (unconditionalActualCanonicalRetainedPhaseTail
              (S := S) (B := B) (N := N) (d := d) (L := L) j)) = _
  convert
    (unconditionalActualC485CanonicalCorrectedIdeal_generic
      (B := B) (m := m)
      schedule ξ ζ j positive grid dimension fine
      (unconditionalActualCanonicalRetainedPhaseTail
        (S := S) (B := B) (N := N) (d := d) (L := L) j)) using 1
  exact unconditionalActualSelectedBranchLocalAction_decidableEq_irrel
    _ _ _ _ _

theorem unconditionalActualSelectedBranchLocalAction_norm
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ ((ι × ι) × τ)) :
    ‖unconditionalMixedConjugateSelectedBranchLocalAction U V z‖ =
      ‖z‖ := by
  classical
  let M : Matrix ((ι × ι) × τ) ((ι × ι) × τ) ℂ :=
    (unconditionalMixedConjugateSelectedBranchUnitary
      (τ := τ) U V : Matrix ((ι × ι) × τ) ((ι × ι) × τ) ℂ)
  have gram : M.conjTranspose * M = 1 := by
    simpa [M, Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp
        (unconditionalMixedConjugateSelectedBranchUnitary
          (τ := τ) U V).property)
  have squared : ‖toLp 2 (M.mulVec (ofLp z))‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [rectangular_matrix_mulVec_norm_sq, gram]
    simp [quadraticExpectation, ← Complex.ofReal_pow]
  change ‖toLp 2 (M.mulVec (ofLp z))‖ = ‖z‖
  nlinarith [norm_nonneg (toLp 2 (M.mulVec (ofLp z))), norm_nonneg z]

theorem unconditionalActualSelectedBranchLocalAction_sub
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (x y : EuclideanSpace ℂ ((ι × ι) × τ)) :
    unconditionalMixedConjugateSelectedBranchLocalAction U V x -
        unconditionalMixedConjugateSelectedBranchLocalAction U V y =
      unconditionalMixedConjugateSelectedBranchLocalAction
        U V (x - y) := by
  classical
  ext i
  simp [unconditionalMixedConjugateSelectedBranchLocalAction,
    Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, mul_sub]

theorem unconditionalActualC485CleanDeviation_sq
    {S B N d L m : ℕ}
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L)
    (positive : 0 < width (schedule j))
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    ‖integratorActualC485CleanedVector
          (B := B) (m := m) Q width schedule ξ ζ A C j -
        integratorActualC485CanonicalVector
          (B := B) (m := m) schedule ξ ζ j positive grid fine‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousCommonStopGaugeStageError
          Q (width (schedule j)) m ξ ζ A C := by
  classical
  rw [unconditionalActualC485CanonicalVector_eq_correctedIdeal
    schedule ξ ζ j positive grid dimension fine]
  unfold integratorActualC485CleanedVector
  rw [unconditionalActualSelectedBranchLocalAction_sub,
    unconditionalActualSelectedBranchLocalAction_norm]
  exact unconditionalSelectedCopyMatchedBranch_deviation_sq
    Q width schedule ξ ζ A C j
    (unconditionalActualCanonicalRetainedPhaseTail
      (S := S) (B := B) (N := N) (d := d) (L := L) j)
    (integratorActualCanonicalRetainedPhaseTail_norm
      phases grid dimension j)

theorem unconditionalActualC485CleanDeviation_eq_hazard
    {S B N d L m : ℕ}
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (positive : ∀ s, 0 < width s)
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d)
    (fine : ∀ s, (d : ℝ) / (N : ℝ) < 1 / (width s + 1)) :
    (∑ j : Fin L,
      ‖integratorActualC485CleanedVector
            (B := B) (m := m) Q width schedule ξ ζ A C j -
          integratorActualC485CanonicalVector
            (B := B) (m := m) schedule ξ ζ j
            (positive (schedule j)) grid (fine (schedule j))‖ ^ 2) =
      dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
        Q m width schedule ξ ζ A C := by
  classical
  simp_rw [unconditionalActualC485CleanDeviation_sq
    Q width schedule ξ ζ A C _ (positive _) phases grid dimension (fine _)]
  unfold dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
  simp_rw [
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_norm_sq]

theorem unconditionalActualC485WeightedCleanDeviation_eq_hazard
    {ι : Type*} [Fintype ι]
    {S B N d L m : ℕ}
    (law : ι → ℝ)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : ι → BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (positive : ∀ s, 0 < width s)
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d)
    (fine : ∀ s, (d : ℝ) / (N : ℝ) < 1 / (width s + 1)) :
    (∑ u : ι, law u *
      ∑ j : Fin L,
        ‖integratorActualC485CleanedVector
              (B := B) (m := m)
              Q width schedule (ξ u) (ζ u) A C j -
            integratorActualC485CanonicalVector
              (B := B) (m := m) schedule (ξ u) (ζ u) j
              (positive (schedule j)) grid (fine (schedule j))‖ ^ 2) =
      ∑ u : ι, law u *
        dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
          Q m width schedule (ξ u) (ζ u) A C := by
  classical
  apply Finset.sum_congr rfl
  intro u _
  rw [unconditionalActualC485CleanDeviation_eq_hazard
    Q width schedule (ξ u) (ζ u) A C positive phases grid dimension fine]

end

noncomputable section

open scoped BigOperators

open QuantumParallelRepetition.ClassicalSampling

theorem unconditionalFairMatchedFlag_history_eq
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matched :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true) :
    exactSourceAlicePermutationHistory
        D denominator numerator nonempty flag x =
      exactSourceBobPermutationHistory
        D denominator numerator nonempty flag y := by
  classical
  change
    decide
      (exactSourceAlicePermutationHistory
          D denominator numerator nonempty flag x =
        exactSourceBobPermutationHistory
          D denominator numerator nonempty flag y) = true at matched
  exact of_decide_eq_true matched

theorem unconditionalFairMatchedFlag_bobTarget_eq_aliceSample
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matched :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true) :
    exactGlobalHistoryFinPhi G n S D
        (exactSourceBobPermutationHistory
          D denominator numerator nonempty flag y) y =
      exactGlobalHistoryFinPhi G n S D
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))).2.2.2 y := by
  have same := unconditionalFairMatchedFlag_history_eq
    D denominator numerator nonempty flag x y matched
  simp only [exactSourceAliceSampleTuple]
  rw [same]

theorem unconditionalFairMatchedFlag_aliceTarget_eq_aliceSample
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y) :
    exactGlobalHistoryFinGamma G n S D
        (exactSourceAlicePermutationHistory
          D denominator numerator nonempty flag x) x =
      exactGlobalHistoryFinGamma G n S D
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))).2.2.2 x := by
  rfl

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalActualOneScaleDecodedMatchedCleanedVector
    {F X Y : Type} {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ : F → X → BipartiteUnitVector d)
    (ζ : F → Y → BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (grid : 0 < N)
    (flag : F) (x : X) (y : Y) (j : Fin L)
    (positive : 0 < width (schedule j)) :
    unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis (ξ flag x))))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis (ζ flag y))))
        (unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
          (unconditionalActualOneScaleFixedSourcePhaseSplit P) j
          (actualStoppingBranchVector
            (actualStoppingQuestionLocalAction
              (physical8OneScaleActualAliceStoppingUnitary
                (P := P) (N := N) (d := d) (L := L) (m := m)
                (unconditionalActualOneScaleFixedSourcePhaseSplit P)
                Q width schedule ξ A flag x)
              (physical8OneScaleActualBobStoppingUnitary
                (P := P) (N := N) (d := d) (L := L) (m := m)
                (unconditionalActualOneScaleFixedSourcePhaseSplit P)
                Q width schedule ζ C flag y)
              (unconditionalSourcePhysicalCleanedStoppingFixedSource
                1 P N d L m)) j.succ j.succ)) =
      integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N) (d := d) (L := L) (m := m)
        Q width schedule (ξ flag x) (ζ flag y) A C j := by
  classical
  have decoded :=
    unconditionalActualOneScalePhysicalQuestionDecodedMatchedBranch
      Q width schedule ξ ζ A C grid flag x y j positive
  change
    unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis (ξ flag x))))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis (ζ flag y))))
        _ =
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis (ξ flag x))))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis (ζ flag y))))
        _
  rw [decoded]

def integratorActualC485SourceAlicePOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (x : X) :
    POVM A
      (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))) := by
  classical
  exact
    reindexedPOVM
      (finCongr
        (Nat.mul_one
          (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))))
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystAlicePOVM G n S D 1 a₀ x))

def integratorActualC485SourceBobPOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (b₀ : B) (y : Y) :
    POVM B
      (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))) := by
  classical
  exact
    reindexedPOVM
      (finCongr
        (Nat.mul_one
          (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))))
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystBobPOVM G n S D 1 b₀ y))

def integratorActualC485SelectedAlicePOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A)
    (P N m : ℕ) (x : X) :
    POVM A
      (UnconditionalSelectedCopyLocalIndex
        P (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        N m) := by
  classical
  exact
    directDSVActualReindexedRetainedPOVM
      (physical8SelectedGlobalTargetWorkEquiv
        P N (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) m)
      (integratorActualC485SourceAlicePOVM G n S D a₀ x)

def integratorActualC485SelectedBobPOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (b₀ : B)
    (P N m : ℕ) (y : Y) :
    POVM B
      (UnconditionalSelectedCopyLocalIndex
        P (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        N m) := by
  classical
  exact
    directDSVActualReindexedRetainedPOVM
      (physical8SelectedGlobalTargetWorkEquiv
        P N (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) m)
      (integratorActualC485SourceBobPOVM G n S D b₀ y)

def integratorActualC485WinningEffect
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (j : Fin L) (x : X) (y : Y) :
    IntegratorActualC485BranchSpace
      1 P N
        (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        L m j →L[ℂ]
      IntegratorActualC485BranchSpace
        1 P N
          (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
          L m j := by
  classical
  let d : ℕ :=
    Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
  let selected : Type := UnconditionalSelectedCopyLocalIndex
    P d N m
  let retained : Type :=
    IntegratorActualC485RetainedIndex 1 P N d L j
  exact Matrix.toEuclideanCLM
    (n := (selected × selected) × retained) (𝕜 := ℂ)
    (directDSVActualLocalPOVMWinningEffect G
      (integratorActualC485SelectedAlicePOVM
        G n S D a₀ P N m x)
      (integratorActualC485SelectedBobPOVM
        G n S D b₀ P N m y) x y ⊗ₖ
      (1 : Matrix retained retained ℂ))

theorem unconditionalActualFairSourceEmbezzlementOne_apply :
    embezzlementState 1 (0, 0) = 1 := by
  simp [embezzlementState, rawEmbezzlementState,
    EuclideanSpace.norm_eq, Fintype.sum_prod_type]

theorem unconditionalActualFairSourceTensorEmbezzlementOne_reindex
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr
          (finCongr (Nat.mul_one d))
          (finCongr (Nat.mul_one d)))
        (tensorEmbezzlementTarget (n := 1) ξ) = ξ.val := by
  classical
  ext ⟨i, j⟩
  have first :
      (((finCongr (Nat.mul_one d)).symm i).divNat : Fin d) = i := by
    apply Fin.ext
    change i.val / 1 = i.val
    simp
  have second :
      (((finCongr (Nat.mul_one d)).symm j).divNat : Fin d) = j := by
    apply Fin.ext
    change j.val / 1 = j.val
    simp
  have first_work :
      (((finCongr (Nat.mul_one d)).symm i).modNat : Fin 1) = 0 :=
    Subsingleton.elim _ _
  have second_work :
      (((finCongr (Nat.mul_one d)).symm j).modNat : Fin 1) = 0 :=
    Subsingleton.elim _ _
  change
    ξ.val
        ((((finCongr (Nat.mul_one d)).symm i).divNat : Fin d),
         (((finCongr (Nat.mul_one d)).symm j).divNat : Fin d)) *
      embezzlementState 1
        ((((finCongr (Nat.mul_one d)).symm i).modNat : Fin 1),
         (((finCongr (Nat.mul_one d)).symm j).modNat : Fin 1)) =
      ξ.val (i, j)
  rw [first, second, first_work, second_work,
    unconditionalActualFairSourceEmbezzlementOne_apply, mul_one]

theorem
    unconditionalActualFairSourceConjugateTensorEmbezzlementOne_inverse_reindex
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr
          (finCongr (Nat.mul_one d)).symm
          (finCongr (Nat.mul_one d)).symm)
        (unconditionalConjugatePureVector ξ.val) =
      unconditionalConjugatePureVector
        (tensorEmbezzlementTarget (n := 1) ξ) := by
  classical
  ext ⟨i, j⟩
  change
    star (ξ.val
      ((finCongr (Nat.mul_one d)) i,
       (finCongr (Nat.mul_one d)) j)) =
      star (tensorEmbezzlementTarget (n := 1) ξ (i, j))
  congr 1
  have recovered := congrArg
    (fun z : EuclideanSpace ℂ (Fin d × Fin d) =>
      z ((finCongr (Nat.mul_one d)) i,
         (finCongr (Nat.mul_one d)) j))
    (unconditionalActualFairSourceTensorEmbezzlementOne_reindex ξ)
  simpa [LinearIsometryEquiv.piLpCongrLeft_apply] using recovered.symm

theorem unconditionalActualFairSourceWinningEffect_reindex
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [decA : DecidableEq A] [decB : DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    (x : X) (y : Y) :
    directDSVActualLocalPOVMWinningEffect G
        (integratorActualC485SourceAlicePOVM G n S D a₀ x)
        (integratorActualC485SourceBobPOVM G n S D b₀ y)
        x y =
      Matrix.reindex
        (Equiv.prodCongr
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D))))
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)))))
        (Equiv.prodCongr
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D))))
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)))))
        (unconditionalConjugateSourceGlobalCatalystWinningEffect
          G n S D 1 a₀ b₀ x y) := by
  classical
  have alice_instance : decA = Classical.decEq A :=
    Subsingleton.elim _ _
  have bob_instance : decB = Classical.decEq B :=
    Subsingleton.elim _ _
  cases alice_instance
  cases bob_instance
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [directDSVActualLocalPOVMWinningEffect,
    integratorActualC485SourceAlicePOVM,
    integratorActualC485SourceBobPOVM,
    unconditionalConjugateSourceGlobalCatalystWinningEffect,
    reindexedPOVM, Matrix.reindex_apply,
    Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map]

def unconditionalActualFairSourceBaseWinningCLM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    (x : X) (y : Y) :
    ExactSourceGlobalState G n S D →L[ℂ]
      ExactSourceGlobalState G n S D := by
  classical
  exact Matrix.toEuclideanCLM (𝕜 := ℂ)
    (directDSVActualLocalPOVMWinningEffect G
      (integratorActualC485SourceAlicePOVM G n S D a₀ x)
      (integratorActualC485SourceBobPOVM G n S D b₀ y)
      x y)

theorem unconditionalActualFairSourceEOneReindexedGlobalWinningBorn
    {d : ℕ}
    (winning :
      Matrix (Fin (d * 1) × Fin (d * 1))
        (Fin (d * 1) × Fin (d * 1)) ℂ)
    (ξ : BipartiteUnitVector d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := Fin d × Fin d) (𝕜 := ℂ)
        (Matrix.reindex
          (Equiv.prodCongr
            (finCongr (Nat.mul_one d))
            (finCongr (Nat.mul_one d)))
          (Equiv.prodCongr
            (finCongr (Nat.mul_one d))
            (finCongr (Nat.mul_one d))) winning))
      (unconditionalConjugatePureVector ξ.val) =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := Fin (d * 1) × Fin (d * 1)) (𝕜 := ℂ) winning)
      (unconditionalConjugatePureVector
        (tensorEmbezzlementTarget (n := 1) ξ)) := by
  classical
  let e : (Fin (d * 1) × Fin (d * 1)) ≃ (Fin d × Fin d) :=
    Equiv.prodCongr (finCongr (Nat.mul_one d))
      (finCongr (Nat.mul_one d))
  calc
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := Fin (d * 1) × Fin (d * 1)) (𝕜 := ℂ) winning)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm
          (unconditionalConjugatePureVector ξ.val)) := by
          exact directDSVActualReindexedWinningEffect_quadratic
            e.symm winning
            (unconditionalConjugatePureVector ξ.val)
    _ = _ := by
          congr 1
          exact
            unconditionalActualFairSourceConjugateTensorEmbezzlementOne_inverse_reindex
              ξ

theorem unconditionalActualFairSourceBaseSupportedBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (a₀ : A) (b₀ : B)
    (h : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D h ≠ 0) :
    quadraticExpectation
      (unconditionalActualFairSourceBaseWinningCLM
        G n S D a₀ b₀ h.2.1 h.2.2.1)
      (unconditionalConjugatePureVector
        (exactSourceTuplePsi G n S D h)) =
      exactSourceConditionalWinningProbability G n S D h := by
  classical
  unfold unconditionalActualFairSourceBaseWinningCLM
  calc
    _ = quadraticExpectation
          (Matrix.toEuclideanCLM
            (n :=
              Fin (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)) ×
              Fin (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)))
            (𝕜 := ℂ)
            (Matrix.reindex
              (Equiv.prodCongr
                (finCongr (Nat.mul_one
                  (Fintype.card
                    (ExactGlobalHistoryLocalIndex G n S D))))
                (finCongr (Nat.mul_one
                  (Fintype.card
                    (ExactGlobalHistoryLocalIndex G n S D)))))
              (Equiv.prodCongr
                (finCongr (Nat.mul_one
                  (Fintype.card
                    (ExactGlobalHistoryLocalIndex G n S D))))
                (finCongr (Nat.mul_one
                  (Fintype.card
                    (ExactGlobalHistoryLocalIndex G n S D)))))
              (unconditionalConjugateSourceGlobalCatalystWinningEffect
                G n S D 1 a₀ b₀ h.2.1 h.2.2.1)))
          (unconditionalConjugatePureVector
            (exactSourceTuplePsi G n S D h)) := by
              congr 2
              exact unconditionalActualFairSourceWinningEffect_reindex
                G n S D a₀ b₀ h.2.1 h.2.2.1
    _ = quadraticExpectation
          (Matrix.toEuclideanCLM
            (n :=
              Fin (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D) * 1) ×
              Fin (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D) * 1))
            (𝕜 := ℂ)
            (unconditionalConjugateSourceGlobalCatalystWinningEffect
              G n S D 1 a₀ b₀ h.2.1 h.2.2.1))
          (unconditionalConjugatePureVector
            (tensorEmbezzlementTarget (n := 1)
              (exactGlobalHistoryFinPsi
                G n S D h.2.2.2 h.2.1 h.2.2.1))) := by
              exact unconditionalActualFairSourceEOneReindexedGlobalWinningBorn
                (unconditionalConjugateSourceGlobalCatalystWinningEffect
                  G n S D 1 a₀ b₀ h.2.1 h.2.2.1)
                (exactGlobalHistoryFinPsi
                  G n S D h.2.2.2 h.2.1 h.2.2.1)
    _ = _ :=
      unconditionalConjugateSourceGlobalCatalystWinningEffect_law_supported
        G n S D positive 1 (by norm_num) a₀ b₀ h supported

def unconditionalActualFairSourcePhaseHarmonicWork
    (P k : ℕ) :
    EuclideanSpace ℂ
      ((Fin P × Fin k) × (Fin P × Fin k)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodProdProdComm
      (Fin P) (Fin P) (Fin k) (Fin k))
    (unconditionalMatchedVerifierTensor
      (ePRState P) (embezzlementState k))

theorem unconditionalActualFairSourcePhaseHarmonicWork_norm
    {P k : ℕ} (phases : 0 < P) (harmonic : 0 < k) :
    ‖unconditionalActualFairSourcePhaseHarmonicWork P k‖ = 1 := by
  unfold unconditionalActualFairSourcePhaseHarmonicWork
  rw [LinearIsometryEquiv.norm_map,
    unconditionalMatchedVerifierTensor_norm,
    ePRState_norm P phases,
    embezzlementState_norm k harmonic]
  norm_num

theorem unconditionalActualFairSourcePhaseHarmonicStage_sourceProduct
    {P N d m : ℕ}
    (ψ : EuclideanSpace ℂ (Fin d × Fin d)) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (directDSVActualBilateralRetainedIndexEquiv
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (physical8SelectedGlobalTargetWorkEquiv P N d m))
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState P
          (unconditionalConjugatePureVector ψ)
          (fun _ _ _ => embezzlementState (N * m))) =
      unconditionalMatchedVerifierTensor
        (unconditionalConjugatePureVector ψ)
        (unconditionalActualFairSourcePhaseHarmonicWork
          P (N * m)) := by
  classical
  ext ⟨⟨i, j⟩, ⟨⟨p, a⟩, ⟨q, b⟩⟩⟩
  simp [LinearIsometryEquiv.piLpCongrLeft_apply,
    directDSVActualBilateralRetainedIndexEquiv,
    physical8SelectedGlobalTargetWorkEquiv,
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual,
    dSVDensityRationalPublicBucketCoherentPhaseHistory,
    unconditionalMatchedVerifierTensor,
    unconditionalActualFairSourcePhaseHarmonicWork,
    mul_assoc, mul_left_comm, mul_comm]

theorem unconditionalActualFairSourceSelectedBorn_of_base
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N m : ℕ} (phases : 0 < P) (grid : 0 < N)
    (harmonic : 0 < m)
    (x : X) (y : Y)
    (ψ : EuclideanSpace ℂ
      (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) ×
       Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))))
    (value : ℝ)
    (base_born :
      quadraticExpectation
        (unconditionalActualFairSourceBaseWinningCLM
          G n S D a₀ b₀ x y)
        (unconditionalConjugatePureVector ψ) = value) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          UnconditionalSelectedCopyLocalIndex
            P (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D)) N m ×
          UnconditionalSelectedCopyLocalIndex
            P (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D)) N m)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (integratorActualC485SelectedAlicePOVM
            G n S D a₀ P N m x)
          (integratorActualC485SelectedBobPOVM
            G n S D b₀ P N m y) x y))
      (dSVDensityRationalPublicBucketCoherentPhaseSigmaState P
        (unconditionalConjugatePureVector ψ)
        (fun _ _ _ => embezzlementState (N * m))) = value := by
  classical
  let d : ℕ :=
    Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
  let e := physical8SelectedGlobalTargetWorkEquiv P N d m
  let stage := dSVDensityRationalPublicBucketCoherentPhaseSigmaState P
    (unconditionalConjugatePureVector ψ)
    (fun _ _ _ => embezzlementState (N * m))
  let work := unconditionalActualFairSourcePhaseHarmonicWork
    P (N * m)
  have work_unit : ‖work‖ = 1 :=
    unconditionalActualFairSourcePhaseHarmonicWork_norm
      phases (Nat.mul_pos grid harmonic)
  change
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          UnconditionalSelectedCopyLocalIndex P d N m ×
          UnconditionalSelectedCopyLocalIndex P d N m)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM e
            (integratorActualC485SourceAlicePOVM G n S D a₀ x))
          (directDSVActualReindexedRetainedPOVM e
            (integratorActualC485SourceBobPOVM G n S D b₀ y)) x y))
      stage = value
  rw [directDSVActualReindexedRetainedPOVMWinningEffect_tensor_quadratic
    G e e
    (integratorActualC485SourceAlicePOVM G n S D a₀ x)
    (integratorActualC485SourceBobPOVM G n S D b₀ y)
    x y stage (unconditionalConjugatePureVector ψ) work
    (unconditionalActualFairSourcePhaseHarmonicStage_sourceProduct ψ)]
  change
    ‖work‖ ^ 2 *
      quadraticExpectation
        (unconditionalActualFairSourceBaseWinningCLM
          G n S D a₀ b₀ x y)
        (unconditionalConjugatePureVector ψ) = value
  rw [work_unit, one_pow, one_mul, base_born]

theorem unconditionalActualFairSourceOuterBorn_of_base
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (phases : 0 < P) (grid : 0 < N)
    (harmonic : 0 < m)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ ζ : BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)))
    (ψ : EuclideanSpace ℂ
      (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) ×
       Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))))
    (ψ_unit : ‖ψ‖ = 1)
    (j : Fin L) (x : X) (y : Y) (value : ℝ)
    (base_born :
      quadraticExpectation
        (unconditionalActualFairSourceBaseWinningCLM
          G n S D a₀ b₀ x y)
        (unconditionalConjugatePureVector ψ) = value) :
    quadraticExpectation
      (integratorActualC485WinningEffect
        G n S D a₀ b₀ (P := P) (N := N) (m := m) j x y)
      (integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule ξ ζ ψ j) =
      ‖integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule ξ ζ ψ j‖ ^ 2 * value := by
  classical
  let d : ℕ :=
    Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
  let stage := dSVDensityRationalPublicBucketCoherentPhaseSigmaState P
    (unconditionalConjugatePureVector ψ)
    (fun _ _ _ => embezzlementState (N * m))
  let retained := integratorActualC485NormalizedDiagonalWork
    (B := P) (N := N) width schedule ξ ζ j
  have selected_born :
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            UnconditionalSelectedCopyLocalIndex P d N m ×
            UnconditionalSelectedCopyLocalIndex P d N m)
          (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            (integratorActualC485SelectedAlicePOVM
              G n S D a₀ P N m x)
            (integratorActualC485SelectedBobPOVM
              G n S D b₀ P N m y) x y))
        stage = value :=
    unconditionalActualFairSourceSelectedBorn_of_base
      G n S D a₀ b₀ phases grid harmonic x y ψ value base_born
  have stage_unit : ‖stage‖ = 1 := by
    calc
      ‖stage‖ =
          ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (physical8SelectedGlobalTargetWorkEquiv P N d m))
            stage‖ := by rw [LinearIsometryEquiv.norm_map]
      _ = ‖unconditionalMatchedVerifierTensor
            (unconditionalConjugatePureVector ψ)
            (unconditionalActualFairSourcePhaseHarmonicWork
              P (N * m))‖ := by
              rw [unconditionalActualFairSourcePhaseHarmonicStage_sourceProduct]
      _ = 1 := by
            rw [unconditionalMatchedVerifierTensor_norm,
              unconditionalConjugatePureVector_norm, ψ_unit,
              unconditionalActualFairSourcePhaseHarmonicWork_norm
                phases (Nat.mul_pos grid harmonic)]
            norm_num
  change
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          (UnconditionalSelectedCopyLocalIndex P d N m ×
           UnconditionalSelectedCopyLocalIndex P d N m) ×
          IntegratorActualC485RetainedIndex 1 P N d L j)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (integratorActualC485SelectedAlicePOVM
            G n S D a₀ P N m x)
          (integratorActualC485SelectedBobPOVM
            G n S D b₀ P N m y) x y ⊗ₖ
          (1 : Matrix
            (IntegratorActualC485RetainedIndex 1 P N d L j)
            (IntegratorActualC485RetainedIndex 1 P N d L j) ℂ)))
      (unconditionalMatchedVerifierTensor stage retained) =
        ‖unconditionalMatchedVerifierTensor stage retained‖ ^ 2 * value
  rw [unconditionalMatchedVerifierEffect_tensor_quadratic,
    selected_born, unconditionalMatchedVerifierTensor_norm_sq,
    stage_unit]
  ring

theorem unconditionalActualFairSourceSupportedBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (a₀ : A) (b₀ : B)
    (h : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D h ≠ 0)
    {P N L m : ℕ} (phases : 0 < P) (grid : 0 < N)
    (harmonic : 0 < m)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (j : Fin L) :
    quadraticExpectation
      (integratorActualC485WinningEffect
        G n S D a₀ b₀ (P := P) (N := N) (m := m)
        j h.2.1 h.2.2.1)
      (integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule
        (exactGlobalHistoryFinGamma G n S D h.2.2.2 h.2.1)
        (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
        (exactSourceTuplePsi G n S D h) j) =
      ‖integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule
        (exactGlobalHistoryFinGamma G n S D h.2.2.2 h.2.1)
        (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
        (exactSourceTuplePsi G n S D h) j‖ ^ 2 *
        exactSourceConditionalWinningProbability G n S D h := by
  classical
  exact
    unconditionalActualFairSourceOuterBorn_of_base
      G n S D a₀ b₀ phases grid harmonic width schedule
      (exactGlobalHistoryFinGamma G n S D h.2.2.2 h.2.1)
      (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
      (exactSourceTuplePsi G n S D h)
      (exactSourceTuplePsi_norm G n S D h)
      j h.2.1 h.2.2.1
      (exactSourceConditionalWinningProbability G n S D h)
      (unconditionalActualFairSourceBaseSupportedBorn
        G n S D positive a₀ b₀ h supported)

end

noncomputable section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

theorem unconditionalActualRetainedPOVM_ext
    {C ι : Type*} [Fintype C] [Fintype ι] [DecidableEq ι]
    (P Q : POVM C ι)
    (same : ∀ (a : C) (i j : ι), P.effect a i j = Q.effect a i j) :
    P = Q := by
  cases P with
  | mk pe pp pc =>
    cases Q with
    | mk qe qp qc =>
      have effect : pe = qe := by
        funext a
        apply Matrix.ext
        intro i j
        exact same a i j
      cases effect
      rfl

theorem unconditionalPhysicalOneScaleActualGlobalFiberPOVM_nested
    {C : Type*} [Fintype C]
    {P N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (j : Fin L)
    (source : POVM C (Fin d)) :
    directDSVActualReindexedRetainedPOVM
        (physical8OneScaleActualGlobalFiberEquiv
          (N := N) (d := d) (m := m) phaseSplit j) source =
      directDSVActualReindexedRetainedPOVM
        (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
          phaseSplit j)
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          source) := by
  classical
  apply unconditionalActualRetainedPOVM_ext
  intro a i k
  let outer :
      UnconditionalSourcePhysicalStoppingPhaseFiber
        1 P N d L m ≃
        UnconditionalSelectedCopyLocalIndex P d N m ×
          UnconditionalSourceFlagControlledRetainedIndex
            (N := N) (d := d) j R :=
    unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      phaseSplit j
  let inner :
      UnconditionalSelectedCopyLocalIndex P d N m ≃
        Fin d × (Fin P × Fin (N * m)) :=
    physical8SelectedGlobalTargetWorkEquiv P N d m
  by_cases selected :
      (inner (outer i).1).2 = (inner (outer k).1).2
  · by_cases retained : (outer i).2 = (outer k).2
    · simp [directDSVActualReindexedRetainedPOVM_effect,
        physical8OneScaleActualGlobalFiberEquiv,
        Equiv.prodAssoc_apply, outer, inner, selected, retained]
    · simp [directDSVActualReindexedRetainedPOVM_effect,
        physical8OneScaleActualGlobalFiberEquiv,
        Equiv.prodAssoc_apply, outer, inner, selected, retained]
  · by_cases retained : (outer i).2 = (outer k).2
    · simp [directDSVActualReindexedRetainedPOVM_effect,
        physical8OneScaleActualGlobalFiberEquiv,
        Equiv.prodAssoc_apply, outer, inner, selected, retained]
    · simp [directDSVActualReindexedRetainedPOVM_effect,
        physical8OneScaleActualGlobalFiberEquiv,
        Equiv.prodAssoc_apply, outer, inner, selected, retained]

theorem unconditionalPhysicalOneScaleOriginalFlagPOVM_succ_nested
    {C Z : Type*} [Fintype C] [DecidableEq C]
    {P N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (default : C)
    (source : Z → POVM C (Fin d))
    (j : Fin L) (x : Z) :
    physical8OneScaleOriginalFlagPOVM
        (N := N) (d := d) (m := m) phaseSplit default source
        j.succ x =
      directDSVActualReindexedRetainedPOVM
        (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
          phaseSplit j)
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (source x)) := by
  change
    directDSVActualReindexedRetainedPOVM
        (physical8OneScaleActualGlobalFiberEquiv
          (N := N) (d := d) (m := m) phaseSplit j) (source x) = _
  exact unconditionalPhysicalOneScaleActualGlobalFiberPOVM_nested
    phaseSplit j (source x)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

theorem unconditionalSelectedGaugeRetainedPOVMNaturality_effect
    {C : Type} [Fintype C]
    {P N d m : ℕ}
    (basis : Matrix.unitaryGroup (Fin d) ℂ)
    (source : POVM C (Fin d)) (a : C) :
    (directDSVActualReindexedRetainedPOVM
      (physical8SelectedGlobalTargetWorkEquiv P N d m)
      (unitaryConjugatePOVM basis source)).effect a =
    (unitaryConjugatePOVM
      (unconditionalMixedConjugateSigmaAtomLift
        (m := N * m) P basis)
      (directDSVActualReindexedRetainedPOVM
        (physical8SelectedGlobalTargetWorkEquiv P N d m)
        source)).effect a := by
  classical
  ext p q
  rcases p with ⟨⟨φ, i⟩, k⟩
  rcases q with ⟨⟨ψ, j⟩, l⟩
  by_cases phase : φ = ψ <;> by_cases work : k = l <;>
    simp [directDSVActualReindexedRetainedPOVM_effect,
      physical8SelectedGlobalTargetWorkEquiv,
      unitaryConjugatePOVM, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_sigma,
      Fintype.sum_prod_type,
      unconditionalMixedConjugateSigmaAtomLift_apply,
      mul_assoc, ite_and, phase, work, eq_comm]

theorem unconditionalSelectedGaugeRetainedPOVMNaturality
    {C : Type} [Fintype C]
    {P N d m : ℕ}
    (basis : Matrix.unitaryGroup (Fin d) ℂ)
    (source : POVM C (Fin d)) :
    directDSVActualReindexedRetainedPOVM
        (physical8SelectedGlobalTargetWorkEquiv P N d m)
        (unitaryConjugatePOVM basis source) =
      unitaryConjugatePOVM
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P basis)
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          source) := by
  classical
  apply unconditionalActualRetainedPOVM_ext
  intro a i j
  exact congrArg (fun M => M i j)
    (unconditionalSelectedGaugeRetainedPOVMNaturality_effect
      (P := P) (N := N) (m := m) basis source a)

end

noncomputable section

open WithLp Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

theorem unconditionalActualFairSourceSelectedRetainedWinningEffectGauge
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ}
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (x : X) (y : Y) :
    let e := physical8SelectedGlobalTargetWorkEquiv P N d m
    let U := unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) P alice
    let V := unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) P bob
    directDSVActualLocalPOVMWinningEffect G
      (directDSVActualReindexedRetainedPOVM e
        (unitaryConjugatePOVM alice PA))
      (directDSVActualReindexedRetainedPOVM e
        (unitaryConjugatePOVM bob PB)) x y =
      (((U : Matrix _ _ ℂ) ⊗ₖ (V : Matrix _ _ ℂ))ᴴ *
        directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM e PA)
          (directDSVActualReindexedRetainedPOVM e PB) x y *
        ((U : Matrix _ _ ℂ) ⊗ₖ (V : Matrix _ _ ℂ))) := by
  classical
  dsimp only
  rw [unconditionalSelectedGaugeRetainedPOVMNaturality,
    unconditionalSelectedGaugeRetainedPOVMNaturality]
  unfold directDSVActualLocalPOVMWinningEffect
  simp_rw [unitaryConjugatePOVM_jointEffect]
  simp [Finset.mul_sum, Finset.sum_mul]

theorem unconditionalActualFairSourceSelectedRetainedWinningBornGauge
    {X Y A B τ : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype τ] [DecidableEq τ]
    {P N d m : ℕ}
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex P d N m ×
        UnconditionalSelectedCopyLocalIndex P d N m) × τ)) :
    let e := physical8SelectedGlobalTargetWorkEquiv P N d m
    let U := unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) P alice
    let V := unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) P bob
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (UnconditionalSelectedCopyLocalIndex P d N m ×
          UnconditionalSelectedCopyLocalIndex P d N m) × τ)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM e
            (unitaryConjugatePOVM alice PA))
          (directDSVActualReindexedRetainedPOVM e
            (unitaryConjugatePOVM bob PB)) x y ⊗ₖ
          (1 : Matrix τ τ ℂ))) z =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (UnconditionalSelectedCopyLocalIndex P d N m ×
          UnconditionalSelectedCopyLocalIndex P d N m) × τ)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM e PA)
          (directDSVActualReindexedRetainedPOVM e PB) x y ⊗ₖ
          (1 : Matrix τ τ ℂ)))
      (unconditionalMixedConjugateSelectedBranchLocalAction
        U V z) := by
  classical
  dsimp only
  rw [unconditionalActualFairSourceSelectedRetainedWinningEffectGauge]
  let UA := unconditionalMixedConjugateSigmaAtomLift
    (m := N * m) P alice
  let UB := unconditionalMixedConjugateSigmaAtomLift
    (m := N * m) P bob
  let e := physical8SelectedGlobalTargetWorkEquiv P N d m
  let selected : Type := UnconditionalSelectedCopyLocalIndex P d N m
  let E : Matrix (selected × selected) (selected × selected) ℂ :=
    directDSVActualLocalPOVMWinningEffect G
      (directDSVActualReindexedRetainedPOVM e PA)
      (directDSVActualReindexedRetainedPOVM e PB) x y
  let K : Matrix (selected × selected) (selected × selected) ℂ :=
    (UA : Matrix selected selected ℂ) ⊗ₖ
      (UB : Matrix selected selected ℂ)
  let W : Matrix ((selected × selected) × τ)
      ((selected × selected) × τ) ℂ :=
    K ⊗ₖ (1 : Matrix τ τ ℂ)
  have transport :
      (Kᴴ * E * K) ⊗ₖ (1 : Matrix τ τ ℂ) =
        Wᴴ * (E ⊗ₖ (1 : Matrix τ τ ℂ)) * W := by
    calc
      (Kᴴ * E * K) ⊗ₖ (1 : Matrix τ τ ℂ) =
          (Kᴴ ⊗ₖ (1 : Matrix τ τ ℂ)) *
            (E ⊗ₖ (1 : Matrix τ τ ℂ)) *
            (K ⊗ₖ (1 : Matrix τ τ ℂ)) := by
              rw [← Matrix.mul_kronecker_mul,
                ← Matrix.mul_kronecker_mul]
              simp
      _ = Wᴴ * (E ⊗ₖ (1 : Matrix τ τ ℂ)) * W := by
        simp [W, Matrix.conjTranspose_kronecker]
  change
    quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := (selected × selected) × τ) (𝕜 := ℂ)
          ((Kᴴ * E * K) ⊗ₖ (1 : Matrix τ τ ℂ))) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := (selected × selected) × τ) (𝕜 := ℂ)
          (E ⊗ₖ (1 : Matrix τ τ ℂ)))
        (unconditionalMixedConjugateSelectedBranchLocalAction
          UA UB z)
  rw [transport]
  exact (rectangular_matrix_quadratic_compression
    W (E ⊗ₖ (1 : Matrix τ τ ℂ)) z).symm

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

theorem unconditionalActualC485RetainedPureWorkReindexBorn
    {s t v : Type}
    [Fintype s] [DecidableEq s]
    [Fintype t] [DecidableEq t]
    [Fintype v] [DecidableEq v]
    (e : t ≃ v)
    (winning : Matrix s s ℂ)
    (z : EuclideanSpace ℂ (s × t)) :
    quadraticExpectation
        (Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
          (winning ⊗ₖ (1 : Matrix t t ℂ))) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := s × v) (𝕜 := ℂ)
          (winning ⊗ₖ (1 : Matrix v v ℂ)))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr (Equiv.refl s) e) z) := by
  classical
  let whole : s × t ≃ s × v :=
    Equiv.prodCongr (Equiv.refl s) e
  have actual_identity :
      Matrix.reindex whole.symm whole.symm
          (winning ⊗ₖ (1 : Matrix v v ℂ)) =
        winning ⊗ₖ (1 : Matrix t t ℂ) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases same : a = b
    · subst b
      simp [whole, Matrix.reindex_apply, Matrix.kroneckerMap_apply]
    · have different : e a ≠ e b := fun h => same (e.injective h)
      simp [whole, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
        same, different]
  rw [← actual_identity]
  exact directDSVActualReindexedWinningEffect_quadratic
    whole (winning ⊗ₖ (1 : Matrix v v ℂ)) z

def unconditionalActualC485RetainedHistoryPairEquiv
    {P N d L : ℕ} (j : Fin L) :
    (UnconditionalSourceFlagControlledRetainedIndex
        (N := N) (d := d) j
        (UnconditionalActualCanonicalRetainedPhaseIndex 1 P) ×
     UnconditionalSourceFlagControlledRetainedIndex
        (N := N) (d := d) j
        (UnconditionalActualCanonicalRetainedPhaseIndex 1 P)) ≃
      IntegratorActualC485RetainedIndex 1 P N d L j :=
  unconditionalActualFixedSourceRetainedHistoryPairEquiv
    (N := N) (d := d)
    (R := UnconditionalActualCanonicalRetainedPhaseIndex 1 P) j

theorem unconditionalActualC485FullBilateralWorkRegroup
    {P N d L m : ℕ}
    (j : Fin L)
    (z : EuclideanSpace ℂ
      (UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m ×
       UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m)) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr
          (Equiv.refl
            (UnconditionalSelectedCopyLocalIndex P d N m ×
             UnconditionalSelectedCopyLocalIndex P d N m))
          (unconditionalActualC485RetainedHistoryPairEquiv
            (P := P) (N := N) (d := d) j))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv
            (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
              (N := N) (d := d) (m := m)
              (unconditionalActualOneScaleFixedSourcePhaseSplit P) j)
            (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
              (N := N) (d := d) (m := m)
              (unconditionalActualOneScaleFixedSourcePhaseSplit P) j)) z) =
      unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualOneScaleFixedSourcePhaseSplit P) j z := by
  ext q
  rfl

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalWeightedClippedMatchedVerifierAndMassLoss
    {I K : Type*} [Fintype I] [Fintype K]
    (weight : I → ℝ)
    (weight_nonnegative : ∀ i, 0 ≤ weight i)
    (weight_normalized : (∑ i : I, weight i) = 1)
    (win : I → ℝ) (win_bounded : ∀ i, win i ≤ 1)
    {H : I × K → Type*}
    [∀ p, NormedAddCommGroup (H p)]
    [∀ p, InnerProductSpace ℂ (H p)]
    (effect : (p : I × K) → (H p →L[ℂ] H p))
    (contraction : ∀ p, ‖effect p‖ ≤ 1)
    (actual canonical source : (p : I × K) → H p)
    (actual_mass :
      (∑ i : I, weight i *
        ∑ k : K, ‖actual (i, k)‖ ^ 2) ≤ 1)
    (canonical_mass :
      (∑ i : I, weight i *
        ∑ k : K, ‖canonical (i, k)‖ ^ 2) ≤ 1)
    (canonical_row_mass : ∀ i : I,
      (∑ k : K, ‖canonical (i, k)‖ ^ 2) ≤ 1)
    (same_work_mass : ∀ (i : I) (k : K),
      ‖source (i, k)‖ = ‖canonical (i, k)‖)
    (supported_born : ∀ (i : I), weight i ≠ 0 →
      ∀ k : K,
        quadraticExpectation (effect (i, k)) (source (i, k)) =
          ‖source (i, k)‖ ^ 2 * win i)
    (Δclean Δclip bad : ℝ)
    (clean_deviation :
      (∑ i : I, weight i *
        ∑ k : K,
          ‖actual (i, k) - canonical (i, k)‖ ^ 2) ≤ Δclean)
    (clip_deviation :
      (∑ i : I, weight i *
        ∑ k : K,
          ‖canonical (i, k) - source (i, k)‖ ^ 2) ≤ Δclip)
    (actual_success :
      1 - bad ≤ ∑ i : I, weight i *
        ∑ k : K, ‖actual (i, k)‖ ^ 2) :
    (∑ i : I, weight i * win i) - bad -
        4 * Real.sqrt Δclean - 2 * Real.sqrt Δclip ≤
      ∑ i : I, weight i *
        ∑ k : K,
          quadraticExpectation (effect (i, k)) (actual (i, k)) := by
  classical
  let pairWeight : I × K → ℝ := fun p => weight p.1
  have pair_nonnegative (p : I × K) : 0 ≤ pairWeight p :=
    weight_nonnegative p.1
  have pair_actual_mass :
      (∑ p : I × K, pairWeight p * ‖actual p‖ ^ 2) ≤ 1 := by
    simpa [pairWeight, Fintype.sum_prod_type, Finset.mul_sum]
      using actual_mass
  have pair_canonical_mass :
      (∑ p : I × K, pairWeight p * ‖canonical p‖ ^ 2) ≤ 1 := by
    simpa [pairWeight, Fintype.sum_prod_type, Finset.mul_sum]
      using canonical_mass
  have source_mass :
      (∑ i : I, weight i *
        ∑ k : K, ‖source (i, k)‖ ^ 2) ≤ 1 := by
    simpa only [same_work_mass] using canonical_mass
  have pair_source_mass :
      (∑ p : I × K, pairWeight p * ‖source p‖ ^ 2) ≤ 1 := by
    simpa [pairWeight, Fintype.sum_prod_type, Finset.mul_sum]
      using source_mass
  have pair_clean_deviation :
      (∑ p : I × K,
        pairWeight p * ‖actual p - canonical p‖ ^ 2) ≤ Δclean := by
    simpa [pairWeight, Fintype.sum_prod_type, Finset.mul_sum]
      using clean_deviation
  have pair_clip_deviation :
      (∑ p : I × K,
        pairWeight p * ‖canonical p - source p‖ ^ 2) ≤ Δclip := by
    simpa [pairWeight, Fintype.sum_prod_type, Finset.mul_sum]
      using clip_deviation
  have clean_verifier_gap :
      |(∑ i : I, weight i *
          ∑ k : K,
            quadraticExpectation (effect (i, k)) (actual (i, k))) -
        (∑ i : I, weight i *
          ∑ k : K,
            quadraticExpectation (effect (i, k)) (canonical (i, k)))| ≤
        2 * Real.sqrt Δclean := by
    simpa [pairWeight, Fintype.sum_prod_type, Finset.mul_sum] using
      (unconditionalMatchedVerifierAggregate_dependent_le
        pairWeight pair_nonnegative effect contraction actual canonical
        pair_actual_mass pair_canonical_mass Δclean pair_clean_deviation)
  have clip_verifier_gap :
      |(∑ i : I, weight i *
          ∑ k : K,
            quadraticExpectation (effect (i, k)) (canonical (i, k))) -
        (∑ i : I, weight i *
          ∑ k : K,
            quadraticExpectation (effect (i, k)) (source (i, k)))| ≤
        2 * Real.sqrt Δclip := by
    simpa [pairWeight, Fintype.sum_prod_type, Finset.mul_sum] using
      (unconditionalMatchedVerifierAggregate_dependent_le
        pairWeight pair_nonnegative effect contraction canonical source
        pair_canonical_mass pair_source_mass Δclip pair_clip_deviation)
  have identity_expectation (p : I × K) (v : H p) :
      quadraticExpectation (ContinuousLinearMap.id ℂ (H p)) v =
        ‖v‖ ^ 2 := by
    unfold quadraticExpectation
    change (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  have clean_mass_gap :
      |(∑ i : I, weight i *
          ∑ k : K, ‖actual (i, k)‖ ^ 2) -
        (∑ i : I, weight i *
          ∑ k : K, ‖canonical (i, k)‖ ^ 2)| ≤
        2 * Real.sqrt Δclean := by
    have bounded :=
      unconditionalMatchedVerifierAggregate_dependent_le
        pairWeight pair_nonnegative
        (fun p => ContinuousLinearMap.id ℂ (H p))
        (fun _ => ContinuousLinearMap.norm_id_le)
        actual canonical pair_actual_mass pair_canonical_mass
        Δclean pair_clean_deviation
    simpa [pairWeight, Fintype.sum_prod_type, Finset.mul_sum,
      identity_expectation] using bounded
  have source_row_mass (i : I) :
      (∑ k : K, ‖source (i, k)‖ ^ 2) ≤ 1 := by
    simpa only [same_work_mass] using canonical_row_mass i
  have ideal_payoff :
      (∑ i : I, weight i * win i) -
          (1 - ∑ i : I, weight i *
            ∑ k : K, ‖source (i, k)‖ ^ 2) ≤
        ∑ i : I, weight i *
          ∑ k : K,
            quadraticExpectation (effect (i, k)) (source (i, k)) := by
    have born :
        (∑ i : I, weight i *
          ∑ k : K,
            quadraticExpectation (effect (i, k)) (source (i, k))) =
          ∑ i : I, weight i *
            ((∑ k : K, ‖source (i, k)‖ ^ 2) * win i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases zero : weight i = 0
      · simp [zero]
      · congr 1
        simp_rw [supported_born i zero]
        rw [Finset.sum_mul]
    rw [born]
    have lost_mass :
        (∑ i : I, weight i *
          (1 - ∑ k : K, ‖source (i, k)‖ ^ 2)) =
          1 - ∑ i : I, weight i *
            ∑ k : K, ‖source (i, k)‖ ^ 2 := by
      calc
        (∑ i : I, weight i *
          (1 - ∑ k : K, ‖source (i, k)‖ ^ 2)) =
            (∑ i : I, weight i) -
              ∑ i : I, weight i *
                ∑ k : K, ‖source (i, k)‖ ^ 2 := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [weight_normalized]
    calc
      (∑ i : I, weight i * win i) -
          (1 - ∑ i : I, weight i *
            ∑ k : K, ‖source (i, k)‖ ^ 2) =
          ∑ i : I, weight i *
            (win i - (1 - ∑ k : K, ‖source (i, k)‖ ^ 2)) := by
        rw [← lost_mass, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i : I, weight i *
            ((∑ k : K, ‖source (i, k)‖ ^ 2) * win i) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (weight_nonnegative i)
        have loss := mul_nonneg
          (sub_nonneg.mpr (source_row_mass i))
          (sub_nonneg.mpr (win_bounded i))
        nlinarith
  have clean_verifier_signed :
      (∑ i : I, weight i *
        ∑ k : K,
          quadraticExpectation (effect (i, k)) (canonical (i, k))) -
      (∑ i : I, weight i *
        ∑ k : K,
          quadraticExpectation (effect (i, k)) (actual (i, k))) ≤
        2 * Real.sqrt Δclean := by
    exact (le_abs_self _).trans (by
      simpa [abs_sub_comm] using clean_verifier_gap)
  have clip_verifier_signed :
      (∑ i : I, weight i *
        ∑ k : K,
          quadraticExpectation (effect (i, k)) (source (i, k))) -
      (∑ i : I, weight i *
        ∑ k : K,
          quadraticExpectation (effect (i, k)) (canonical (i, k))) ≤
        2 * Real.sqrt Δclip := by
    exact (le_abs_self _).trans (by
      simpa [abs_sub_comm] using clip_verifier_gap)
  have clean_mass_signed :
      (∑ i : I, weight i *
        ∑ k : K, ‖actual (i, k)‖ ^ 2) -
      (∑ i : I, weight i *
        ∑ k : K, ‖source (i, k)‖ ^ 2) ≤
        2 * Real.sqrt Δclean := by
    simpa only [same_work_mass] using
      ((le_abs_self _).trans clean_mass_gap)
  linarith

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

theorem unconditionalFairPhysicalFlaggedStoppingTransfer
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (rational_normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (support_preserving : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    {L : ℕ} {ι : Fin (L + 1) → Type}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (PA : ExactSourceSharedFlag X Y A B D denominator →
      (r : Fin (L + 1)) → X → POVM A (ι r))
    (PB : ExactSourceSharedFlag X Y A B D denominator →
      (r : Fin (L + 1)) → Y → POVM B (ι r))
    (U : ExactSourceSharedFlag X Y A B D denominator →
      X → Matrix.unitaryGroup (Σ r : Fin (L + 1), ι r) ℂ)
    (V : ExactSourceSharedFlag X Y A B D denominator →
      Y → Matrix.unitaryGroup (Σ r : Fin (L + 1), ι r) ℂ)
    (z : ExactSourceSharedFlag X Y A B D denominator →
      EuclideanSpace ℂ
        ((Σ r : Fin (L + 1), ι r) ×
          (Σ r : Fin (L + 1), ι r)))
    (z_normalized : ∀ flag, ‖z flag‖ = 1)
    (matched :
      ExactSourceSharedFlag X Y A B D denominator ×
        (X × Y) → Bool)
    {K : Type*} [Fintype K]
    {H : ExactLocallySampleableTuple X Y A B D × K → Type*}
    [∀ p, NormedAddCommGroup (H p)]
    [∀ p, InnerProductSpace ℂ (H p)]
    (effect : (p : ExactLocallySampleableTuple X Y A B D × K) →
      (H p →L[ℂ] H p))
    (contraction : ∀ p, ‖effect p‖ ≤ 1)
    (actual canonical source :
      (p : ExactLocallySampleableTuple X Y A B D × K) → H p)
    (actual_mass :
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D h *
          ∑ k : K, ‖actual (h, k)‖ ^ 2) ≤ 1)
    (canonical_mass :
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D h *
          ∑ k : K, ‖canonical (h, k)‖ ^ 2) ≤ 1)
    (canonical_row_mass : ∀ h : ExactLocallySampleableTuple X Y A B D,
      (∑ k : K, ‖canonical (h, k)‖ ^ 2) ≤ 1)
    (same_work_mass : ∀ (h : ExactLocallySampleableTuple X Y A B D)
      (k : K), ‖source (h, k)‖ = ‖canonical (h, k)‖)
    (supported_born : ∀ h : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D h ≠ 0 →
        ∀ k : K,
          quadraticExpectation (effect (h, k)) (source (h, k)) =
            ‖source (h, k)‖ ^ 2 *
              exactSourceConditionalWinningProbability G n S D h)
    (epsilon lam deviation clipping bad : ℝ)
    (clean_deviation :
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D h *
          ∑ k : K, ‖actual (h, k) - canonical (h, k)‖ ^ 2) ≤ deviation)
    (clip_deviation :
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D h *
          ∑ k : K, ‖canonical (h, k) - source (h, k)‖ ^ 2) ≤ clipping)
    (actual_success :
      1 - bad ≤
        ∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            ∑ k : K, ‖actual (h, k)‖ ^ 2)
    (history_born_nonnegative :
      ∀ h : ExactLocallySampleableTuple X Y A B D,
        0 ≤ ∑ k : K,
          quadraticExpectation (effect (h, k)) (actual (h, k)))
    (history_born_bounded :
      ∀ h : ExactLocallySampleableTuple X Y A B D,
        (∑ k : K,
          quadraticExpectation (effect (h, k)) (actual (h, k))) ≤ 1)
    (source_failure :
      uniformRemainingFailure
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D < epsilon / 2)
    (total_variation :
      QuantumParallelRepetition.Pinsker.finiteTotalVariation
        (flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator))
        (exactSourceAliceFlagCoupling
          G n S D denominator numerator nonempty) ≤ lam)
    (mismatch :
      (∑ outcome :
        ExactSourceSharedFlag X Y A B D denominator × (X × Y),
        flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator) outcome *
          if matched outcome then 0 else 1) ≤ 4 * lam)
    (matched_physical_branch :
      ∀ (flag : ExactSourceSharedFlag X Y A B D denominator)
        (x : X) (y : Y),
        matched (flag, (x, y)) = true →
          (∑ k : K,
            quadraticExpectation
              (effect
                (exactSourceAliceSampleTuple
                  D denominator numerator nonempty (flag, (x, y)), k))
              (actual
                (exactSourceAliceSampleTuple
                  D denominator numerator nonempty (flag, (x, y)), k))) ≤
            ∑ j : Fin L,
              quadraticExpectation
                (Matrix.toEuclideanCLM
                  (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
                  (actualStoppingBranchWinningEffect
                    G (PA flag) (PB flag) j.succ j.succ x y))
                (actualStoppingBranchVector
                  (actualStoppingQuestionLocalAction
                    (U flag x) (V flag y) (z flag))
                  j.succ j.succ)) :
    1 - epsilon / 2 - 5 * lam -
        (bad + 4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
      (pureFlaggedStrategy G
        (exactSourceSharedFlagWeight D denominator)
        (exactSourceSharedFlagWeight_nonneg D denominator)
        (exactSourceSharedFlagWeight_sum D remaining denominator)
        z z_normalized
        (fun flag x => unitaryConjugatePOVM
          (U flag x)
          (dependentBlockPOVM
            (fun r => PA flag r x)))
        (fun flag y => unitaryConjugatePOVM
          (V flag y)
          (dependentBlockPOVM
            (fun r => PB flag r y)))).winProbability := by
  classical
  let weight : ExactSourceSharedFlag X Y A B D denominator → ℝ :=
    exactSourceSharedFlagWeight D denominator
  let p :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y) → ℝ :=
    flaggedQuestionWeight G weight
  let q :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y) → ℝ :=
    exactSourceAliceFlagCoupling
      G n S D denominator numerator nonempty
  let history :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y) →
        ExactLocallySampleableTuple X Y A B D :=
    exactSourceAliceSampleTuple D denominator numerator nonempty
  let physical : ExactLocallySampleableTuple X Y A B D → ℝ :=
    fun h => ∑ k : K,
      quadraticExpectation (effect (h, k)) (actual (h, k))
  let flagPhysical :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y) → ℝ :=
    fun outcome => physical (history outcome)
  have weight_nonnegative : ∀ flag, 0 ≤ weight flag :=
    exactSourceSharedFlagWeight_nonneg D denominator
  have weight_normalized : (∑ flag, weight flag) = 1 :=
    exactSourceSharedFlagWeight_sum D remaining denominator
  have p_normalized : (∑ outcome, p outcome) = 1 :=
    flaggedQuestionWeight_sum G weight weight_normalized
  have q_normalized : (∑ outcome, q outcome) = 1 :=
    exactSourceAliceFlagCoupling_sum
      G n S D remaining positive base denominator denominator_positive
      numerator rational_normalized support_preserving nonempty
  have fair_verifier :=
    unconditionalWeightedClippedMatchedVerifierAndMassLoss
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableLaw_nonneg G n S D positive)
      (exactLocallySampleableLaw_sum G n S D remaining positive)
      (exactSourceConditionalWinningProbability G n S D)
      (fun h =>
        (exactSourceConditionalWinningProbability_bounds
          G n S D positive h).2)
      effect contraction actual canonical source
      actual_mass canonical_mass canonical_row_mass
      same_work_mass supported_born
      deviation clipping bad
      clean_deviation clip_deviation actual_success
  have fair_win :
      1 - epsilon / 2 ≤
        ∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            exactSourceConditionalWinningProbability
              G n S D h :=
    (exactSourceConditionalWinningProbability_gt_of_uniform_failure
      G n S D remaining positive source_failure).le
  have pushforward :
      (∑ outcome, q outcome * flagPhysical outcome) =
        ∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h * physical h := by
    simpa [q, flagPhysical, history] using
      (exactSourceAliceFlagCoupling_expectation
        G n S D remaining positive base denominator denominator_positive
        numerator rational_normalized support_preserving nonempty physical)
  have flagPhysical_nonnegative (outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y)) :
      0 ≤ flagPhysical outcome :=
    history_born_nonnegative (history outcome)
  have flagPhysical_bounded (outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y)) :
      flagPhysical outcome ≤ 1 :=
    history_born_bounded (history outcome)
  have variation : QuantumParallelRepetition.Pinsker.finiteTotalVariation p q ≤ lam := by
    simpa [p, q, weight] using total_variation
  have transferred := winning_expectation_transfer
    p q flagPhysical p_normalized q_normalized
    flagPhysical_nonnegative flagPhysical_bounded
  have p_nonnegative (outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y)) :
      0 ≤ p outcome :=
    flaggedQuestionWeight_nonneg
      G weight weight_nonnegative outcome
  have discarded := matched_payoff_discard_le
    p flagPhysical p_nonnegative flagPhysical_bounded matched
  have mismatch' :
      (∑ outcome, p outcome * if matched outcome then 0 else 1) ≤
        4 * lam := by
    simpa [p, weight] using mismatch
  have physical_transfer :
      1 - epsilon / 2 - 5 * lam -
          (bad + 4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
        ∑ outcome, p outcome *
          if matched outcome then flagPhysical outcome else 0 := by
    rw [← pushforward] at fair_verifier
    change
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D h *
          exactSourceConditionalWinningProbability G n S D h) -
          bad - 4 * Real.sqrt deviation - 2 * Real.sqrt clipping ≤
        ∑ outcome, q outcome * flagPhysical outcome at fair_verifier
    linarith
  let stop :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y) → ℝ :=
    fun outcome =>
      ∑ j : Fin L,
        quadraticExpectation
          (Matrix.toEuclideanCLM
            (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
            (actualStoppingBranchWinningEffect
              G (PA outcome.1) (PB outcome.1)
              j.succ j.succ outcome.2.1 outcome.2.2))
          (actualStoppingBranchVector
            (actualStoppingQuestionLocalAction
              (U outcome.1 outcome.2.1)
              (V outcome.1 outcome.2.2) (z outcome.1))
            j.succ j.succ)
  have stop_nonnegative (outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y)) :
      0 ≤ stop outcome := by
    unfold stop
    apply Finset.sum_nonneg
    intro j _
    exact actualStoppingBranchBorn_nonneg
      G (PA outcome.1) (PB outcome.1)
      (actualStoppingQuestionLocalAction
        (U outcome.1 outcome.2.1)
        (V outcome.1 outcome.2.2) (z outcome.1))
      j.succ j.succ outcome.2.1 outcome.2.2
  have matched_stop :
      (∑ outcome, p outcome *
        if matched outcome then flagPhysical outcome else 0) ≤
      ∑ outcome, p outcome * stop outcome := by
    apply Finset.sum_le_sum
    intro outcome _
    apply mul_le_mul_of_nonneg_left _ (p_nonnegative outcome)
    by_cases matching : matched outcome = true
    · simp only [matching, ite_true]
      rcases outcome with ⟨flag, x, y⟩
      exact matched_physical_branch flag x y matching
    · have false_match : matched outcome = false :=
        Bool.eq_false_of_not_eq_true matching
      simp only [false_match, Bool.false_eq]
      exact stop_nonnegative outcome
  have physical_stopping :=
    actualStoppingQuestionLocalFlaggedWinningProbability_ge_matched
      G weight weight_nonnegative weight_normalized
      PA PB U V z z_normalized
  have reindex :
      (∑ outcome, p outcome * stop outcome) =
        ∑ flag, weight flag *
          (∑ x : X, ∑ y : Y, G.questionWeight x y *
            ∑ j : Fin L,
              quadraticExpectation
                (Matrix.toEuclideanCLM
                  (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
                  (actualStoppingBranchWinningEffect
                    G (PA flag) (PB flag) j.succ j.succ x y))
                (actualStoppingBranchVector
                  (actualStoppingQuestionLocalAction
                    (U flag x) (V flag y) (z flag))
                  j.succ j.succ)) := by
    simp only [p, flaggedQuestionWeight, stop,
      Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro flag _
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring_nf
  change
    1 - epsilon / 2 - 5 * lam -
        (bad + 4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
      (pureFlaggedStrategy G weight weight_nonnegative weight_normalized
        z z_normalized
        (fun flag x => unitaryConjugatePOVM
          (U flag x)
          (dependentBlockPOVM
            (fun r => PA flag r x)))
        (fun flag y => unitaryConjugatePOVM
          (V flag y)
          (dependentBlockPOVM
            (fun r => PB flag r y)))).winProbability
  rw [reindex] at matched_stop
  exact physical_transfer.trans (matched_stop.trans physical_stopping)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

def unconditionalActualLocalPOVMLosingEffect
    {X Y A B s t : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    (G : Game X Y A B) (PA : POVM A s) (PB : POVM B t)
    (x : X) (y : Y) : Matrix (s × t) (s × t) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then 0
    else PA.effect a ⊗ₖ PB.effect b

theorem unconditionalActualLocalPOVMWinningEffect_posSemidef
    {X Y A B s t : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    (G : Game X Y A B) (PA : POVM A s) (PB : POVM B t)
    (x : X) (y : Y) :
    (directDSVActualLocalPOVMWinningEffect
      G PA PB x y).PosSemidef := by
  classical
  apply Matrix.nonneg_iff_posSemidef.mp
  unfold directDSVActualLocalPOVMWinningEffect
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split
  · exact ((PA.positive a).kronecker (PB.positive b)).nonneg
  · exact le_rfl

theorem unconditionalActualLocalPOVMLosingEffect_posSemidef
    {X Y A B s t : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    (G : Game X Y A B) (PA : POVM A s) (PB : POVM B t)
    (x : X) (y : Y) :
    (unconditionalActualLocalPOVMLosingEffect
      G PA PB x y).PosSemidef := by
  classical
  apply Matrix.nonneg_iff_posSemidef.mp
  unfold unconditionalActualLocalPOVMLosingEffect
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split
  · exact le_rfl
  · exact ((PA.positive a).kronecker (PB.positive b)).nonneg

theorem unconditionalActualLocalPOVMWinningEffect_add_losingEffect
    {X Y A B s t : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    (G : Game X Y A B) (PA : POVM A s) (PB : POVM B t)
    (x : X) (y : Y) :
    directDSVActualLocalPOVMWinningEffect G PA PB x y +
      unconditionalActualLocalPOVMLosingEffect G PA PB x y = 1 := by
  classical
  change
    (∑ a : A, ∑ b : B,
      if G.predicate x y a b = true
      then PA.effect a ⊗ₖ PB.effect b else 0) +
      (∑ a : A, ∑ b : B,
        if G.predicate x y a b = true
        then 0 else PA.effect a ⊗ₖ PB.effect b) = 1
  calc
    _ = ∑ a : A, ∑ b : B, PA.effect a ⊗ₖ PB.effect b := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      split <;> simp
    _ = (∑ a : A, PA.effect a) ⊗ₖ
          (∑ b : B, PB.effect b) := by
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = 1 := by
      rw [PA.complete, PB.complete]
      exact Matrix.one_kronecker_one

theorem unconditionalActualLocalPOVMWinningEffect_complement_posSemidef
    {X Y A B s t : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    (G : Game X Y A B) (PA : POVM A s) (PB : POVM B t)
    (x : X) (y : Y) :
    (1 - directDSVActualLocalPOVMWinningEffect
      G PA PB x y).PosSemidef := by
  have complete :=
    unconditionalActualLocalPOVMWinningEffect_add_losingEffect
      G PA PB x y
  have partition :
      1 - directDSVActualLocalPOVMWinningEffect
          G PA PB x y =
        unconditionalActualLocalPOVMLosingEffect
          G PA PB x y := by
    calc
      _ =
          (directDSVActualLocalPOVMWinningEffect
              G PA PB x y +
            unconditionalActualLocalPOVMLosingEffect
              G PA PB x y) -
            directDSVActualLocalPOVMWinningEffect
              G PA PB x y := by rw [complete]
      _ = _ := by abel
  rw [partition]
  exact unconditionalActualLocalPOVMLosingEffect_posSemidef
    G PA PB x y

theorem unconditionalActualFairSourceVerifier_isPositive
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (j : Fin L) (x : X) (y : Y) :
    (integratorActualC485WinningEffect
      (P := P) (N := N) (m := m)
      G n S D a₀ b₀ j x y).IsPositive := by
  classical
  unfold integratorActualC485WinningEffect
  apply matrixEffectCLM_isPositive
  apply unconditionalMatchedVerifierEffect_tensor_posSemidef
  exact unconditionalActualLocalPOVMWinningEffect_posSemidef
    G
    (integratorActualC485SelectedAlicePOVM
      G n S D a₀ P N m x)
    (integratorActualC485SelectedBobPOVM
      G n S D b₀ P N m y) x y

theorem unconditionalActualFairSourceVerifier_complement_isPositive
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (j : Fin L) (x : X) (y : Y) :
    (1 - integratorActualC485WinningEffect
      (P := P) (N := N) (m := m)
      G n S D a₀ b₀ j x y).IsPositive := by
  classical
  unfold integratorActualC485WinningEffect
  apply matrixEffectCLM_complement_isPositive
  apply unconditionalMatchedVerifierEffect_tensor_complement_posSemidef
  exact unconditionalActualLocalPOVMWinningEffect_complement_posSemidef
    G
    (integratorActualC485SelectedAlicePOVM
      G n S D a₀ P N m x)
    (integratorActualC485SelectedBobPOVM
      G n S D b₀ P N m y) x y

theorem unconditionalActualFairSourceVerifier_norm_le_one
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (j : Fin L) (x : X) (y : Y) :
    ‖integratorActualC485WinningEffect
      (P := P) (N := N) (m := m)
      G n S D a₀ b₀ j x y‖ ≤ 1 := by
  classical
  unfold integratorActualC485WinningEffect
  apply unconditionalMatchedVerifierEffect_tensor_norm_le_one
  · exact unconditionalActualLocalPOVMWinningEffect_posSemidef
      G
      (integratorActualC485SelectedAlicePOVM
        G n S D a₀ P N m x)
      (integratorActualC485SelectedBobPOVM
        G n S D b₀ P N m y) x y
  · exact unconditionalActualLocalPOVMWinningEffect_complement_posSemidef
      G
      (integratorActualC485SelectedAlicePOVM
        G n S D a₀ P N m x)
      (integratorActualC485SelectedBobPOVM
        G n S D b₀ P N m y) x y

theorem unconditionalActualFairSourceVerifier_born_nonnegative
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (j : Fin L) (x : X) (y : Y)
    (z : IntegratorActualC485BranchSpace
      1 P N
        (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        L m j) :
    0 ≤ quadraticExpectation
      (integratorActualC485WinningEffect
        (P := P) (N := N) (m := m)
        G n S D a₀ b₀ j x y) z :=
  positive_quadraticExpectation_nonneg _
    (unconditionalActualFairSourceVerifier_isPositive
      G n S D a₀ b₀ j x y) z

theorem unconditionalActualFairSourceVerifier_born_le_mass
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (j : Fin L) (x : X) (y : Y)
    (z : IntegratorActualC485BranchSpace
      1 P N
        (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        L m j) :
    quadraticExpectation
      (integratorActualC485WinningEffect
        (P := P) (N := N) (m := m)
        G n S D a₀ b₀ j x y) z ≤ ‖z‖ ^ 2 :=
  positive_complement_quadraticExpectation_le _
    (unconditionalActualFairSourceVerifier_complement_isPositive
      G n S D a₀ b₀ j x y) z

theorem unconditionalActualFairSourceVerifier_historyBorn_bounds
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ}
    (actual : (h : ExactLocallySampleableTuple X Y A B D) →
      (j : Fin L) →
      IntegratorActualC485BranchSpace
        1 P N
          (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
          L m j)
    (actual_row_mass :
      ∀ h : ExactLocallySampleableTuple X Y A B D,
        (∑ j : Fin L, ‖actual h j‖ ^ 2) ≤ 1)
    (h : ExactLocallySampleableTuple X Y A B D) :
    0 ≤
      (∑ j : Fin L,
        quadraticExpectation
          (integratorActualC485WinningEffect
            (P := P) (N := N) (m := m)
            G n S D a₀ b₀ j h.2.1 h.2.2.1)
          (actual h j)) ∧
      (∑ j : Fin L,
        quadraticExpectation
          (integratorActualC485WinningEffect
            (P := P) (N := N) (m := m)
            G n S D a₀ b₀ j h.2.1 h.2.2.1)
          (actual h j)) ≤ 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro j _
    exact unconditionalActualFairSourceVerifier_born_nonnegative
      G n S D a₀ b₀ j h.2.1 h.2.2.1 (actual h j)
  · calc
      _ ≤ ∑ j : Fin L, ‖actual h j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact unconditionalActualFairSourceVerifier_born_le_mass
          G n S D a₀ b₀ j h.2.1 h.2.2.1 (actual h j)
      _ ≤ 1 := actual_row_mass h

theorem unconditionalActualFairSourceVerifier_historyBorn_nonnegative
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ}
    (actual : (h : ExactLocallySampleableTuple X Y A B D) →
      (j : Fin L) →
      IntegratorActualC485BranchSpace
        1 P N
          (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
          L m j)
    (actual_row_mass :
      ∀ h : ExactLocallySampleableTuple X Y A B D,
        (∑ j : Fin L, ‖actual h j‖ ^ 2) ≤ 1)
    (h : ExactLocallySampleableTuple X Y A B D) :
    0 ≤
      (∑ j : Fin L,
        quadraticExpectation
          (integratorActualC485WinningEffect
            (P := P) (N := N) (m := m)
            G n S D a₀ b₀ j h.2.1 h.2.2.1)
          (actual h j)) :=
  (unconditionalActualFairSourceVerifier_historyBorn_bounds
    G n S D a₀ b₀ actual actual_row_mass h).1

theorem unconditionalActualFairSourceVerifier_historyBorn_bounded
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ}
    (actual : (h : ExactLocallySampleableTuple X Y A B D) →
      (j : Fin L) →
      IntegratorActualC485BranchSpace
        1 P N
          (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
          L m j)
    (actual_row_mass :
      ∀ h : ExactLocallySampleableTuple X Y A B D,
        (∑ j : Fin L, ‖actual h j‖ ^ 2) ≤ 1)
    (h : ExactLocallySampleableTuple X Y A B D) :
    (∑ j : Fin L,
      quadraticExpectation
        (integratorActualC485WinningEffect
          (P := P) (N := N) (m := m)
          G n S D a₀ b₀ j h.2.1 h.2.2.1)
        (actual h j)) ≤ 1 :=
  (unconditionalActualFairSourceVerifier_historyBorn_bounds
    G n S D a₀ b₀ actual actual_row_mass h).2

def unconditionalActualC485FairSourceDiagonalWork
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (w : ℝ) (N P : ℕ) {L : ℕ}
    (schedule : Fin L → Fin 1)
    (u : ExactLocallySampleableTuple X Y A B D)
    (j : Fin L) :
    EuclideanSpace ℂ
      (IntegratorActualC485RetainedIndex
        1 P N (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D)) L j) :=
  integratorActualC485NormalizedDiagonalWork
    (S := 1) (B := P) (N := N)
    (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
    (L := L)
    (fun _ : Fin 1 => w) schedule
    (unconditionalExactFairGammaUnit G n S D u)
    (exactGlobalHistoryFinPhi G n S D u.2.2.2 u.2.2.1) j

def unconditionalActualC485FairSourceClipEnergy
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    {w : ℝ} {N P L m : ℕ}
    (width : 0 < w) (grid : 0 < N)
    (fine :
      (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) : ℝ) /
        (N : ℝ) < 1 / (w + 1))
    (schedule : Fin L → Fin 1) : ℝ :=
  ∑ u : ExactLocallySampleableTuple X Y A B D,
    exactLocallySampleableLaw G n S D u *
      ∑ j : Fin L,
        ‖unconditionalMatchedVerifierTensor
            (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
              P
              (unconditionalConjugatePureVector
                (exactSourceTuplePsi G n S D u))
              (fun _ _ _ => embezzlementState (N * m)))
            (unconditionalActualC485FairSourceDiagonalWork
              G n S D w N P schedule u j) -
          unconditionalMatchedVerifierTensor
            (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
              P
              (unconditionalConjugatePureVector
                (dSVDensityRationalCanonicalAcceptedUnitTarget
                  width grid fine
                  (unconditionalExactFairGammaUnit
                    G n S D u)).val)
              (fun _ _ _ => embezzlementState (N * m)))
            (unconditionalActualC485FairSourceDiagonalWork
              G n S D w N P schedule u j)‖ ^ 2

theorem unconditionalActualC485FairSourceDiagonalWork_row
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    {w : ℝ} {N P L m : ℕ}
    (width : 0 < w) (grid : 0 < N)
    (dimension :
      0 < Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
    (phases : 0 < P) (harmonic : 0 < m)
    (schedule : Fin L → Fin 1)
    (u : ExactLocallySampleableTuple X Y A B D) :
    (∑ j : Fin L,
      ‖unconditionalActualC485FairSourceDiagonalWork
          G n S D w N P schedule u j‖ ^ 2) ≤ 1 := by
  exact unconditionalActualC485NormalizedDiagonalWork_mass_sum_le_one
    (S := 1) (B := P) (N := N)
    (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
    (L := L) (m := m)
    phases grid dimension harmonic (fun _ : Fin 1 => w)
    (fun _ => width) schedule
    (unconditionalExactFairGammaUnit G n S D u)
    (exactGlobalHistoryFinPhi G n S D u.2.2.2 u.2.2.1)

theorem unconditionalActualC485FairSourceClipEnergy_le
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (source_positive : 0 < repeatedPostselectionMass G n S D)
    {w : ℝ} {N P L m : ℕ}
    (width : 0 < w) (grid : 0 < N)
    (dimension :
      0 < Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
    (fine :
      (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) : ℝ) /
        (N : ℝ) < 1 / (w + 1))
    (phases : 0 < P) (harmonic : 0 < m)
    (schedule : Fin L → Fin 1) :
    unconditionalActualC485FairSourceClipEnergy
        (P := P) (m := m) G n S D width grid fine schedule ≤
      16 * martingaleRate G n S D +
        8 * (1 / w +
          (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) : ℝ) *
            w / (N : ℝ)) := by
  exact unconditionalExactFairStoppedPhaseHarmonicClippedUnit_le
    G n S D remaining source_positive width grid fine phases
    (Nat.mul_pos grid harmonic)
    (fun p => unconditionalActualC485FairSourceDiagonalWork
      G n S D w N P schedule p.1 p.2)
    (fun u => unconditionalActualC485FairSourceDiagonalWork_row
      (m := m) G n S D width grid dimension phases harmonic schedule u)

theorem unconditionalActualC485FairSourceClipEnergy_le_budget
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (source_positive : 0 < repeatedPostselectionMass G n S D)
    {w δ : ℝ} {N P L m : ℕ}
    (width : 0 < w) (grid : 0 < N)
    (dimension :
      0 < Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
    (fine :
      (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) : ℝ) /
        (N : ℝ) < 1 / (w + 1))
    (phases : 0 < P) (harmonic : 0 < m)
    (schedule : Fin L → Fin 1)
    (scalar :
      1 / w +
        (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D) : ℝ) *
          w / (N : ℝ) ≤ 3 * δ / 2) :
    unconditionalActualC485FairSourceClipEnergy
        (P := P) (m := m) G n S D width grid fine schedule ≤
      16 * martingaleRate G n S D + 8 * (3 * δ / 2) := by
  exact (unconditionalActualC485FairSourceClipEnergy_le
    (P := P) (m := m)
    G n S D remaining source_positive width grid dimension fine
    phases harmonic schedule).trans (by gcongr)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

theorem unconditionalActualFairSelectedLocalAction_norm_sq
    {ι τ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ ((ι × ι) × τ)) :
    ‖unconditionalMixedConjugateSelectedBranchLocalAction
        U V z‖ ^ 2 = ‖z‖ ^ 2 := by
  classical
  let M : Matrix ((ι × ι) × τ) ((ι × ι) × τ) ℂ :=
    (unconditionalMixedConjugateSelectedBranchUnitary
      (τ := τ) U V : Matrix _ _ ℂ)
  have gram : M.conjTranspose * M = 1 := by
    simpa [M, Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp
        (unconditionalMixedConjugateSelectedBranchUnitary
          (τ := τ) U V).property)
  change ‖toLp 2 (M.mulVec (ofLp z))‖ ^ 2 = ‖z‖ ^ 2
  rw [rectangular_matrix_mulVec_norm_sq, gram]
  simp [quadraticExpectation, ← Complex.ofReal_pow]

theorem unconditionalActualFairCleanedVector_norm_sq
    {S B N d L m : Nat}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    ‖integratorActualC485CleanedVector
        Q width schedule ξ ζ A C j‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ j.val := by
  letI : DecidableEq
      (IntegratorActualC485RetainedIndex S B N d L j) :=
    FinEnum.decEq
  unfold integratorActualC485CleanedVector
  rw [unconditionalActualFairSelectedLocalAction_norm_sq]
  exact unconditionalSelectedCopyCleanedMatchedBranch_norm_sq
    phases grid harmonic width width_positive schedule ξ ζ Q A C j
    (unconditionalActualCanonicalRetainedPhaseTail
      (S := S) (B := B) (N := N) (d := d) (L := L) j)
    (integratorActualCanonicalRetainedPhaseTail_norm
      phases grid dimension j)

theorem unconditionalActualFairCleanedRow_eq_stoppedSuccess
    {S B N d L m : Nat}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    (∑ j : Fin L,
      ‖integratorActualC485CleanedVector
        Q width schedule ξ ζ A C j‖ ^ 2) =
      dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
        N width schedule ξ ζ := by
  simp_rw [unconditionalActualFairCleanedVector_norm_sq
    phases grid dimension harmonic width width_positive schedule ξ ζ Q A C]
  unfold dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
  simpa using
    (Fin.sum_univ_eq_sum_range
      (fun k : Nat =>
        dSVDensityRationalHeterogeneousPhysicalSurvival
            N width schedule ξ ζ k *
          dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k) L)

theorem unconditionalActualFairCleanedRow_le_one
    {S B N d L m : Nat}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    (∑ j : Fin L,
      ‖integratorActualC485CleanedVector
        Q width schedule ξ ζ A C j‖ ^ 2) ≤ 1 := by
  rw [unconditionalActualFairCleanedRow_eq_stoppedSuccess
    phases grid dimension harmonic width width_positive schedule ξ ζ Q A C]
  have partition :=
    dSVDensityRationalHeterogeneousPhysicalStopped_mass_partition
      grid dimension width schedule ξ ζ
  have asynchronous :=
    dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_nonneg
      N width schedule ξ ζ
  have terminal :=
    dSVDensityRationalHeterogeneousPhysicalTerminalMass_nonneg
      N width schedule ξ ζ
  linarith

theorem unconditionalActualFairWeightedCleanedMass_le_one
    {I : Type} [Fintype I]
    {S B N d L m : Nat}
    (weight : I → ℝ)
    (weight_nonnegative : ∀ h, 0 ≤ weight h)
    (weight_normalized : (∑ h : I, weight h) = 1)
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : I → BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    (∑ h : I, weight h *
      ∑ j : Fin L,
        ‖integratorActualC485CleanedVector
          Q width schedule (ξ h) (ζ h) A C j‖ ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ h : I, weight h * 1 := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_left
        (unconditionalActualFairCleanedRow_le_one
          phases grid dimension harmonic width width_positive
          schedule (ξ h) (ζ h) Q A C)
        (weight_nonnegative h)
    _ = 1 := by simpa using weight_normalized

theorem unconditionalActualFairWeightedStoppedSuccess
    {I : Type} [Fintype I]
    {S B N d L m : Nat}
    (weight : I → ℝ)
    (weight_normalized : (∑ h : I, weight h) = 1)
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : I → BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (async terminal : ℝ)
    (asynchronous_bound :
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule (ξ h) (ζ h)) ≤ async)
    (terminal_bound :
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalTerminalMass
          N width schedule (ξ h) (ζ h)) ≤ terminal) :
    1 - (async + terminal) ≤
      ∑ h : I, weight h *
        ∑ j : Fin L,
          ‖integratorActualC485CleanedVector
            Q width schedule (ξ h) (ζ h) A C j‖ ^ 2 := by
  have partition :
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
          N width schedule (ξ h) (ζ h)) +
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule (ξ h) (ζ h)) +
      (∑ h : I, weight h *
        dSVDensityRationalHeterogeneousPhysicalTerminalMass
          N width schedule (ξ h) (ζ h)) = 1 := by
    calc
      _ = ∑ h : I, weight h *
        (dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
            N width schedule (ξ h) (ζ h) +
          dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
            N width schedule (ξ h) (ζ h) +
          dSVDensityRationalHeterogeneousPhysicalTerminalMass
            N width schedule (ξ h) (ζ h)) := by
            simp_rw [mul_add, Finset.sum_add_distrib]
      _ = ∑ h : I, weight h := by
        apply Finset.sum_congr rfl
        intro h _
        rw [dSVDensityRationalHeterogeneousPhysicalStopped_mass_partition
          grid dimension width schedule (ξ h) (ζ h)]
        ring
      _ = 1 := weight_normalized
  simp_rw [unconditionalActualFairCleanedRow_eq_stoppedSuccess
    phases grid dimension harmonic width width_positive
    schedule _ _ Q A C]
  linarith

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

theorem unconditionalActualFairCanonicalVector_norm_sq
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L)
    (positive : 0 < width (schedule j))
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    ‖integratorActualC485CanonicalVector
        (B := B) (m := m) schedule ξ ζ j positive grid fine‖ ^ 2 =
      ‖integratorActualC485NormalizedDiagonalWork
          (B := B) (N := N) width schedule ξ ζ j‖ ^ 2 := by
  unfold integratorActualC485CanonicalVector
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
      phases,
    unconditionalConjugatePureVector_norm_sq,
    (dSVDensityRationalCanonicalAcceptedUnitTarget
      positive grid fine ξ).property,
    embezzlementState_norm (N * m)
      (Nat.mul_pos grid harmonic)]
  ring

theorem unconditionalActualFairCanonicalRow_le_one
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (fine : ∀ s,
      (d : ℝ) / (N : ℝ) < 1 / (width s + 1)) :
    (∑ j : Fin L,
      ‖integratorActualC485CanonicalVector
        (B := B) (m := m) schedule ξ ζ j
        (width_positive (schedule j)) grid
        (fine (schedule j))‖ ^ 2) ≤ 1 := by
  calc
    _ = ∑ j : Fin L,
      ‖integratorActualC485NormalizedDiagonalWork
        (B := B) (N := N) width schedule ξ ζ j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact unconditionalActualFairCanonicalVector_norm_sq
        phases grid harmonic width schedule ξ ζ j
        (width_positive (schedule j)) (fine (schedule j))
    _ ≤ 1 :=
      unconditionalActualC485NormalizedDiagonalWork_mass_sum_le_one
        (m := m) phases grid dimension harmonic
        width width_positive schedule ξ ζ

theorem unconditionalActualFairWeightedCanonicalMass_le_one
    {I : Type} [Fintype I]
    {S B N d L m : ℕ}
    (weight : I → ℝ)
    (weight_nonnegative : ∀ h, 0 ≤ weight h)
    (weight_normalized : (∑ h : I, weight h) = 1)
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : I → BipartiteUnitVector d)
    (fine : ∀ s,
      (d : ℝ) / (N : ℝ) < 1 / (width s + 1)) :
    (∑ h : I, weight h *
      ∑ j : Fin L,
        ‖integratorActualC485CanonicalVector
          (B := B) (m := m) schedule (ξ h) (ζ h) j
          (width_positive (schedule j)) grid
          (fine (schedule j))‖ ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ h : I, weight h * 1 := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_left
        (unconditionalActualFairCanonicalRow_le_one
          phases grid dimension harmonic width width_positive
          schedule (ξ h) (ζ h) fine)
        (weight_nonnegative h)
    _ = 1 := by simpa using weight_normalized

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

theorem unconditionalActualFairSourceVector_norm_sq
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (unit : ‖ψ‖ = 1) (j : Fin L) :
    ‖integratorActualC485SourceVector
        (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
        width schedule ξ ζ ψ j‖ ^ 2 =
      ‖integratorActualC485NormalizedDiagonalWork
          (S := S) (B := B) (N := N) (d := d) (L := L)
          width schedule ξ ζ j‖ ^ 2 := by
  unfold integratorActualC485SourceVector
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
      phases,
    unconditionalConjugatePureVector_norm_sq,
    unit,
    embezzlementState_norm (N * m)
      (Nat.mul_pos grid harmonic)]
  ring

theorem unconditionalActualFairSourceCanonicalVector_norm_sq
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (unit : ‖ψ‖ = 1) (j : Fin L)
    (positive : 0 < width (schedule j))
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    ‖integratorActualC485SourceVector
        (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
        width schedule ξ ζ ψ j‖ ^ 2 =
      ‖integratorActualC485CanonicalVector
          (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
          (width := width) schedule ξ ζ j positive grid fine‖ ^ 2 := by
  rw [unconditionalActualFairSourceVector_norm_sq
    phases grid harmonic width schedule ξ ζ ψ unit j,
    unconditionalActualFairCanonicalVector_norm_sq
      phases grid harmonic width schedule ξ ζ j positive fine]

theorem unconditionalActualFairSourceCanonicalVector_norm
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (unit : ‖ψ‖ = 1) (j : Fin L)
    (positive : 0 < width (schedule j))
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    ‖integratorActualC485SourceVector
        (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
        width schedule ξ ζ ψ j‖ =
      ‖integratorActualC485CanonicalVector
          (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
          (width := width) schedule ξ ζ j positive grid fine‖ := by
  have squared :=
    unconditionalActualFairSourceCanonicalVector_norm_sq
      phases grid harmonic width schedule ξ ζ ψ unit j positive fine
  nlinarith [
    norm_nonneg (integratorActualC485SourceVector
      (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
      width schedule ξ ζ ψ j),
    norm_nonneg (integratorActualC485CanonicalVector
      (S := S) (B := B) (N := N) (d := d) (L := L) (m := m)
      (width := width) schedule ξ ζ j positive grid fine)]

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.Pinsker

attribute [local instance] Classical.propDecidable

theorem unconditionalActualSourceSamplerBounds
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (gamma : ℝ) (gamma_positive : 0 < gamma) :
    ∃ (denominator : ℕ), 0 < denominator ∧
      ∃ numerator : ExactLocalSamplerIndex X Y D →
        ExactHistoryFlag X Y A B D → ℕ,
        (∀ index, (∑ history, numerator index history) = denominator) ∧
        (∀ index history,
          0 < exactLocalConditionalFamily D base
              (exactLocallySampleableLaw G n S D)
              index history →
            0 < numerator index history) ∧
        ∃ nonempty : ∀ index,
            (rationalMarked denominator (numerator index)).Nonempty,
          QuantumParallelRepetition.Pinsker.finiteTotalVariation
              (flaggedQuestionWeight G
                (exactSourceSharedFlagWeight D denominator))
              (exactSourceAliceFlagCoupling
                G n S D denominator numerator nonempty) ≤
            exactSourcePinskerRate G n S D + gamma ∧
          (∑ outcome :
            ExactSourceSharedFlag X Y A B D denominator ×
              (X × Y),
            flaggedQuestionWeight G
              (exactSourceSharedFlagWeight D denominator) outcome *
              if exactSourcePermutationMatched
                  D denominator numerator nonempty outcome
                then 0 else 1) ≤
            4 * (exactSourcePinskerRate G n S D + gamma) := by
  classical
  obtain ⟨denominator, denominator_positive, numerator,
      numerator_normalized, _approximation, preserves, nonempty,
      rounded_alice, _rounded_bob, sampler_mismatch⟩ :=
    exact_source_equation_twenty_seven_support_preserving_unconditional
      G n S D remaining positive base gamma_positive
  refine ⟨denominator, denominator_positive, numerator,
    numerator_normalized, preserves, nonempty, ?_, ?_⟩
  · rw [exactSourceAliceFlagCoupling_totalVariation
      G n S D remaining positive base denominator denominator_positive
      numerator numerator_normalized preserves nonempty,
      finiteTotalVariation_comm]
    exact rounded_alice
  · exact exactSourceSharedFlag_mismatch_le
      G n D denominator numerator nonempty sampler_mismatch

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalSourcePhysicalSameGridWeightedStoppingLedger
    {d N : ℕ} (dimension : 0 < d) (grid : 0 < N)
    (w δ : ℝ) (large : 1 ≤ w)
    (precision : 0 < δ) (bounded : δ ≤ 1)
    (grid_budget : 2 * (w + 1) * ((d : ℝ) / N) ≤ δ)
    (t : ℝ) (t_positive : 0 < t) (t_bounded : t ≤ 1)
    (rho : ℝ) (rho_positive : 0 < rho)
    {ι : Type} [Fintype ι]
    (weight : ι → ℝ)
    (weight_nonnegative : ∀ i, 0 ≤ weight i)
    (weight_normalized : (∑ i, weight i) = 1)
    (ξ ζ : ι → BipartiteUnitVector d)
    (eta : ℝ)
    (source_energy :
      (∑ i, weight i * ‖(ξ i).val - (ζ i).val‖ ^ 2) ≤ 32 * eta) :
    ∃ L B Q m : ℕ,
      0 < L ∧ 0 < B ∧ 0 < Q ∧ 0 < m ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * m)) ℂ,
        let width : Fin 1 → ℝ := fun _ => w
        let schedule : Fin L → Fin 1 := fun _ => 0
        (∀ i,
          dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
              N width schedule (ξ i) (ζ i) ≤
            8 * Real.sqrt 2 * ‖(ξ i).val - (ζ i).val‖ + δ) ∧
        (∀ i,
          dSVDensityRationalHeterogeneousPhysicalTerminalMass
              N width schedule (ξ i) (ζ i) ≤ δ ^ 2) ∧
        ((∑ i, weight i *
          dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
            N width schedule (ξ i) (ζ i)) ≤
              64 * Real.sqrt eta + δ) ∧
        ((∑ i, weight i *
          dSVDensityRationalHeterogeneousPhysicalTerminalMass
            N width schedule (ξ i) (ζ i)) ≤ δ ^ 2) ∧
        ((∑ i, weight i *
          dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
            Q m width schedule (ξ i) (ζ i) A C) ≤
          (34 / t) * (64 * Real.sqrt eta + δ) +
            4 * rho ^ 2 +
              (16 * (Real.exp 1 - 1) + 4) * t) := by
  classical
  have w_nonnegative : 0 ≤ w := by linarith
  obtain ⟨L, horizon_positive, tail⟩ :=
    dSVDensityRationalHeterogeneousPhysical_exists_positive_horizon
      dimension w_nonnegative precision
  obtain ⟨B, Q, m, phases, resolution, harmonic, A, C, selected⟩ :=
    exists_proofUnconditionalStoppedCommonPrefixBalancedHazard
      grid dimension t t_positive t_bounded rho rho_positive
  refine ⟨L, B, Q, m, horizon_positive, phases, resolution,
    harmonic, A, C, ?_⟩
  let width : Fin 1 → ℝ := fun _ => w
  let schedule : Fin L → Fin 1 := fun _ => 0
  have width_large : ∀ s : Fin 1, 1 ≤ width s := by
    intro s
    exact large
  have upper : ∀ s : Fin 1, width s ≤ w := by
    intro s
    exact le_rfl
  have fine : ∀ s : Fin 1,
      (d : ℝ) / N ≤ 1 / (2 * (width s + 1)) := by
    intro s
    have denominator : 0 < 2 * (width s + 1) := by
      dsimp [width]
      linarith
    apply (le_div_iff₀ denominator).mpr
    dsimp [width]
    nlinarith [grid_budget, bounded]
  have asynchronous (i : ι) :
      dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule (ξ i) (ζ i) ≤
        8 * Real.sqrt 2 * ‖(ξ i).val - (ζ i).val‖ + δ := by
    calc
      _ ≤ 8 * Real.sqrt 2 * ‖(ξ i).val - (ζ i).val‖ +
          2 * (w + 1) * ((d : ℝ) / N) :=
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_le_targetDistance
          grid dimension width width_large fine upper w_nonnegative
          schedule (ξ i) (ζ i)
      _ ≤ _ := by linarith
  have terminal (i : ι) :
      dSVDensityRationalHeterogeneousPhysicalTerminalMass
          N width schedule (ξ i) (ζ i) ≤ δ ^ 2 :=
    dSVDensityRationalHeterogeneousPhysicalTerminalMass_le_horizon
      grid dimension width width_large fine w_nonnegative upper tail
      schedule (ξ i) (ζ i)
  have mean_asynchronous :
      (∑ i, weight i *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule (ξ i) (ζ i)) ≤
        64 * Real.sqrt eta + δ :=
    unconditionalLiterature_weightedAsynchronous_le
      weight (fun i => ‖(ξ i).val - (ζ i).val‖)
      (fun i =>
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule (ξ i) (ζ i))
      weight_nonnegative weight_normalized (fun _ => norm_nonneg _)
      eta δ source_energy asynchronous
  have mean_terminal :
      (∑ i, weight i *
        dSVDensityRationalHeterogeneousPhysicalTerminalMass
          N width schedule (ξ i) (ζ i)) ≤ δ ^ 2 := by
    calc
      _ ≤ ∑ i, weight i * δ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (terminal i)
          (weight_nonnegative i)
      _ = (∑ i, weight i) * δ ^ 2 := by
        rw [Finset.sum_mul]
      _ = δ ^ 2 := by rw [weight_normalized, one_mul]
  have pointwise (i : ι) :
      dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
          Q m width schedule (ξ i) (ζ i) A C ≤
        (34 / t) *
            dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
              N width schedule (ξ i) (ζ i) +
          (4 * rho ^ 2 +
            (16 * (Real.exp 1 - 1) + 4) * t) := by
    have actual := selected width schedule (ξ i) (ζ i)
    rw [dSVDensityRationalHeterogeneousActualAsynchronousFlagMass_eq_stoppedAsynchronousMass
      grid dimension width schedule (ξ i) (ζ i)] at actual
    linarith
  have mean_hazard :=
    unconditionalSelectedCopy_weightedAffine
      weight
      (fun i =>
        dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
          Q m width schedule (ξ i) (ζ i) A C)
      (fun i =>
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule (ξ i) (ζ i))
      weight_nonnegative weight_normalized
      (34 / t)
      (4 * rho ^ 2 + (16 * (Real.exp 1 - 1) + 4) * t)
      pointwise
  dsimp only
  refine ⟨asynchronous, terminal, mean_asynchronous, mean_terminal, ?_⟩
  have scaled := mul_le_mul_of_nonneg_left mean_asynchronous
    (show 0 ≤ (34 : ℝ) / t by positivity)
  linarith

end

noncomputable section

private theorem unconditionalSmallSource_eta_le_one
    (eta alpha : ℝ)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (small : 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1) :
    eta ≤ 1 := by
  have delta_nonnegative : 0 ≤ alpha ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg alpha_positive.le _
  have root_nonnegative := Real.sqrt_nonneg eta
  have root_square := Real.sq_sqrt eta_nonnegative
  nlinarith

private theorem unconditionalSmallSource_eta_scaled_root
    (eta : ℝ) (eta_nonnegative : 0 ≤ eta) :
    eta ^ (1 / 12 : ℝ) ≤ (32 * eta) ^ (1 / 12 : ℝ) := by
  apply Real.rpow_le_rpow eta_nonnegative
  · nlinarith
  · norm_num

private theorem unconditionalSmallSource_root_estimates
    (eta alpha : ℝ)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small : 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1) :
    let δ := alpha ^ (1 / 3 : ℝ)
    let R := alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)
    0 ≤ R ∧ Real.sqrt eta ≤ R ∧ δ ≤ R ∧ δ ^ 2 ≤ R ∧
      Real.sqrt δ ≤ R := by
  dsimp only
  let δ : ℝ := alpha ^ (1 / 3 : ℝ)
  let R : ℝ :=
    alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)
  have delta_nonnegative : 0 ≤ δ :=
    Real.rpow_nonneg alpha_positive.le _
  have delta_bounded : δ ≤ 1 :=
    Real.rpow_le_one alpha_positive.le alpha_bounded (by norm_num)
  have alpha_root_nonnegative : 0 ≤ alpha ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg alpha_positive.le _
  have scaled_nonnegative : 0 ≤ (32 * eta) ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have root_nonnegative : 0 ≤ R :=
    add_nonneg alpha_root_nonnegative scaled_nonnegative
  have eta_bounded :=
    unconditionalSmallSource_eta_le_one
      eta alpha eta_nonnegative alpha_positive small
  have eta_scaled :=
    unconditionalSmallSource_eta_scaled_root eta eta_nonnegative
  have eta_root : Real.sqrt eta ≤ eta ^ (1 / 12 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge'
      eta_nonnegative eta_bounded
      (by norm_num : (0 : ℝ) ≤ 1 / 12)
      (by norm_num : (1 / 12 : ℝ) ≤ 1 / 2)
  have eta_bound : Real.sqrt eta ≤ R := by
    dsimp [R]
    linarith
  have delta_root : δ ≤ alpha ^ (1 / 12 : ℝ) := by
    dsimp [δ]
    exact Real.rpow_le_rpow_of_exponent_ge'
      alpha_positive.le alpha_bounded
      (by norm_num : (0 : ℝ) ≤ 1 / 12)
      (by norm_num : (1 / 12 : ℝ) ≤ 1 / 3)
  have delta_bound : δ ≤ R := by
    dsimp [R]
    linarith
  have delta_sq_bound : δ ^ 2 ≤ R := by
    nlinarith [mul_nonneg delta_nonnegative
      (sub_nonneg.mpr delta_bounded)]
  have delta_sqrt_eq : Real.sqrt δ = alpha ^ (1 / 6 : ℝ) := by
    dsimp [δ]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul alpha_positive.le]
    norm_num
  have delta_sqrt_bound : Real.sqrt δ ≤ R := by
    rw [delta_sqrt_eq]
    have root_compare :
        alpha ^ (1 / 6 : ℝ) ≤ alpha ^ (1 / 12 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge'
        alpha_positive.le alpha_bounded
        (by norm_num : (0 : ℝ) ≤ 1 / 12)
        (by norm_num : (1 / 12 : ℝ) ≤ 1 / 6)
    dsimp [R]
    linarith
  exact ⟨root_nonnegative, eta_bound, delta_bound,
    delta_sq_bound, delta_sqrt_bound⟩

private theorem unconditionalSmallSource_clipping_sqrt_le
    (eta alpha clipping : ℝ)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small : 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1)
    (actual_clipping :
      clipping ≤ 16 * eta + 8 * (3 * alpha ^ (1 / 3 : ℝ) / 2)) :
    Real.sqrt clipping ≤
      8 * (alpha ^ (1 / 12 : ℝ) +
        (32 * eta) ^ (1 / 12 : ℝ)) := by
  let δ : ℝ := alpha ^ (1 / 3 : ℝ)
  let R : ℝ :=
    alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)
  have bounds := unconditionalSmallSource_root_estimates
    eta alpha eta_nonnegative alpha_positive alpha_bounded small
  change 0 ≤ R ∧ Real.sqrt eta ≤ R ∧ δ ≤ R ∧ δ ^ 2 ≤ R ∧
    Real.sqrt δ ≤ R at bounds
  have delta_nonnegative : 0 ≤ δ :=
    Real.rpow_nonneg alpha_positive.le _
  have clip_bound : clipping ≤ 16 * eta + 12 * δ := by
    change clipping ≤ 16 * eta + 8 * (3 * δ / 2)
      at actual_clipping
    nlinarith
  have clip_base_nonnegative : 0 ≤ 16 * eta + 12 * δ := by
    positivity
  have clip_sqrt_base :
      Real.sqrt (16 * eta + 12 * δ) ≤
        4 * Real.sqrt eta + 4 * Real.sqrt δ := by
    have eta_square := Real.sq_sqrt eta_nonnegative
    have delta_square := Real.sq_sqrt delta_nonnegative
    have clip_square := Real.sq_sqrt clip_base_nonnegative
    have cross :=
      mul_nonneg (Real.sqrt_nonneg eta) (Real.sqrt_nonneg δ)
    have clip_root_nonnegative := Real.sqrt_nonneg (16 * eta + 12 * δ)
    have eta_root_nonnegative := Real.sqrt_nonneg eta
    have delta_root_nonnegative := Real.sqrt_nonneg δ
    nlinarith
  change Real.sqrt clipping ≤ 8 * R
  calc
    Real.sqrt clipping ≤ Real.sqrt (16 * eta + 12 * δ) :=
      Real.sqrt_le_sqrt clip_bound
    _ ≤ 4 * Real.sqrt eta + 4 * Real.sqrt δ := clip_sqrt_base
    _ ≤ 8 * R := by linarith [bounds.2.1, bounds.2.2.2.2]

private theorem unconditionalSmallSource_deviation_sqrt_le
    (eta alpha deviation : ℝ)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (small : 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1)
    (actual_deviation :
      deviation ≤
        (34 / Real.sqrt
            (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) *
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) :
    Real.sqrt deviation ≤
      (4 * Real.sqrt
        (34 + unconditionalPrefactorBucketCoefficient) + 2) *
        (alpha ^ (1 / 12 : ℝ) +
          (32 * eta) ^ (1 / 12 : ℝ)) := by
  let k : ℝ :=
    4 * Real.sqrt (34 + unconditionalPrefactorBucketCoefficient) + 2
  let R : ℝ :=
    alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)
  have k_nonnegative : 0 ≤ k := by
    dsimp [k]
    positivity
  have scaled :=
    unconditionalSmallSource_eta_scaled_root eta eta_nonnegative
  have envelope := unconditionalPrefactor_smallHazard_twelfthRoot_le
    eta_nonnegative alpha_positive small
  change Real.sqrt deviation ≤ k * R
  calc
    Real.sqrt deviation ≤
        Real.sqrt
          ((34 / Real.sqrt
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) *
                (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) +
            4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
            unconditionalPrefactorBucketCoefficient *
              Real.sqrt
                (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) :=
      Real.sqrt_le_sqrt actual_deviation
    _ ≤ k * (eta ^ (1 / 12 : ℝ) +
        alpha ^ (1 / 12 : ℝ)) := by
      simpa [k] using envelope
    _ ≤ k * R := by
      apply mul_le_mul_of_nonneg_left _ k_nonnegative
      dsimp [R]
      linarith

theorem unconditionalSmallSourcePhysicalLoss
    (K eta alpha deviation clipping : ℝ)
    (constant :
      1024 + 8 *
          (4 * Real.sqrt
            (34 + unconditionalPrefactorBucketCoefficient) + 2) ≤ K)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small :
      64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1)
    (actual_deviation :
      deviation ≤
        (34 / Real.sqrt
            (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) *
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)))
    (actual_clipping :
      clipping ≤
        16 * eta + 8 * (3 * alpha ^ (1 / 3 : ℝ) / 2)) :
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) +
        (alpha ^ (1 / 3 : ℝ)) ^ 2) +
      4 * Real.sqrt deviation + 4 * Real.sqrt clipping ≤
        K * (alpha ^ (1 / 12 : ℝ) +
          (32 * eta) ^ (1 / 12 : ℝ)) := by
  let δ : ℝ := alpha ^ (1 / 3 : ℝ)
  let R : ℝ :=
    alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)
  let k : ℝ :=
    4 * Real.sqrt (34 + unconditionalPrefactorBucketCoefficient) + 2
  have bounds := unconditionalSmallSource_root_estimates
    eta alpha eta_nonnegative alpha_positive alpha_bounded small
  change 0 ≤ R ∧ Real.sqrt eta ≤ R ∧ δ ≤ R ∧ δ ^ 2 ≤ R ∧
    Real.sqrt δ ≤ R at bounds
  have R_nonnegative := bounds.1
  have eta_sqrt_le_R := bounds.2.1
  have delta_le_R := bounds.2.2.1
  have delta_sq_le_R := bounds.2.2.2.1
  have clip_sqrt_le :=
    unconditionalSmallSource_clipping_sqrt_le
      eta alpha clipping eta_nonnegative alpha_positive alpha_bounded
      small actual_clipping
  change Real.sqrt clipping ≤ 8 * R at clip_sqrt_le
  have k_nonnegative : 0 ≤ k := by
    dsimp [k]
    positivity
  have deviation_sqrt_le :=
    unconditionalSmallSource_deviation_sqrt_le
      eta alpha deviation eta_nonnegative alpha_positive small
      actual_deviation
  change Real.sqrt deviation ≤ k * R at deviation_sqrt_le
  have source_loss :
      64 * Real.sqrt eta + δ + δ ^ 2 ≤ 66 * R := by
    nlinarith
  change
    (64 * Real.sqrt eta + δ + δ ^ 2) +
      4 * Real.sqrt deviation + 4 * Real.sqrt clipping ≤ K * R
  calc
    (64 * Real.sqrt eta + δ + δ ^ 2) +
        4 * Real.sqrt deviation + 4 * Real.sqrt clipping ≤
      66 * R + 4 * (k * R) + 4 * (8 * R) := by
        linarith
    _ ≤ (1024 + 8 * k) * R := by
      nlinarith [mul_nonneg k_nonnegative R_nonnegative]
    _ ≤ K * R := by
      apply mul_le_mul_of_nonneg_right _ R_nonnegative
      simpa [k] using constant

theorem unconditionalSmallSourcePhysicalRoundedLower
    (K eta alpha deviation clipping epsilon lam actual : ℝ)
    (constant :
      1024 + 8 *
          (4 * Real.sqrt
            (34 + unconditionalPrefactorBucketCoefficient) + 2) ≤ K)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small :
      64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1)
    (actual_deviation :
      deviation ≤
        (34 / Real.sqrt
            (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) *
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)))
    (actual_clipping :
      clipping ≤
        16 * eta + 8 * (3 * alpha ^ (1 / 3 : ℝ) / 2))
    (lam_nonnegative : 0 ≤ lam)
    (actual_original_verifier :
      1 - epsilon / 2 - 5 * lam -
        ((64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) +
            (alpha ^ (1 / 3 : ℝ)) ^ 2) +
          4 * Real.sqrt deviation + 4 * Real.sqrt clipping +
          2 * Real.sqrt (8 * eta)) ≤ actual) :
    roundedWinningLowerBound epsilon K alpha eta lam ≤ actual := by
  let R : ℝ :=
    alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)
  have loss := unconditionalSmallSourcePhysicalLoss
    K eta alpha deviation clipping constant eta_nonnegative
    alpha_positive alpha_bounded small actual_deviation actual_clipping
  have K_nonnegative : 0 ≤ K := by
    have root_nonnegative :=
      Real.sqrt_nonneg (34 + unconditionalPrefactorBucketCoefficient)
    linarith
  have R_nonnegative : 0 ≤ R := by
    dsimp [R]
    exact add_nonneg
      (Real.rpow_nonneg alpha_positive.le _)
      (Real.rpow_nonneg (by positivity) _)
  have ceiling_nonnegative : 0 ≤ universalErrorCeiling K := by
    unfold universalErrorCeiling
    have root_nonnegative :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 / 6 : ℝ)
    nlinarith [mul_nonneg K_nonnegative
      (show 0 ≤ 1 + (2 : ℝ) ^ (1 / 6 : ℝ) by positivity)]
  have transfer_nonnegative : 0 ≤ universalErrorCeiling K * lam :=
    mul_nonneg ceiling_nonnegative lam_nonnegative
  have quantum_nonnegative : 0 ≤ K * R :=
    mul_nonneg K_nonnegative R_nonnegative
  change
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) +
        (alpha ^ (1 / 3 : ℝ)) ^ 2) +
      4 * Real.sqrt deviation + 4 * Real.sqrt clipping ≤ K * R
      at loss
  unfold roundedWinningLowerBound totalSamplingLoss
  change
    1 - epsilon / 2 -
      (5 * lam +
        2 * (K * R + Real.sqrt (8 * eta) +
          universalErrorCeiling K * lam)) ≤ actual
  nlinarith

end

noncomputable section

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem pdfGreedyCeilingHorizon_le
    (n : ℕ) (τ d : ℝ)
    (threshold : 0 < τ)
    (small : d ≤ τ / 2) :
    ⌈d * (n : ℝ) / τ⌉₊ ≤ n := by
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ threshold).mpr
  have actual := mul_le_mul_of_nonneg_right small
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

theorem pdfGreedyCeilingHorizon_pow_le_exp
    (n : ℕ) (τ d : ℝ)
    (threshold : 0 < τ)
    (at_most_one : τ ≤ 1) :
    (1 - τ) ^ ⌈d * (n : ℝ) / τ⌉₊ ≤
      Real.exp (-d * (n : ℝ)) := by
  let T : ℕ := ⌈d * (n : ℝ) / τ⌉₊
  have base_nonnegative : 0 ≤ 1 - τ := sub_nonneg.mpr at_most_one
  have base_le : 1 - τ ≤ Real.exp (-τ) := by
    have actual := Real.add_one_le_exp (-τ)
    linarith
  have ceiling : d * (n : ℝ) / τ ≤ (T : ℝ) := by
    exact Nat.le_ceil (d * (n : ℝ) / τ)
  have exponent : -τ * (T : ℝ) ≤ -d * (n : ℝ) := by
    have cleared := (div_le_iff₀ threshold).mp ceiling
    nlinarith
  change (1 - τ) ^ T ≤ Real.exp (-d * (n : ℝ))
  calc
    (1 - τ) ^ T ≤ Real.exp (-τ) ^ T := by
      exact pow_le_pow_left₀ base_nonnegative base_le T
    _ = Real.exp (-τ * (T : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-d * (n : ℝ)) := Real.exp_le_exp.mpr exponent

theorem pdfGreedyCard_lt_of_ceil
    (k n : ℕ) (τ d : ℝ)
    (below : k < ⌈d * (n : ℝ) / τ⌉₊) :
    (k : ℝ) < d * (n : ℝ) / τ :=
  Nat.lt_ceil.mp below

theorem pdfQuantitativeGreedyConditioning
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (τ d θ : ℝ)
    (_n_positive : 0 < n)
    (threshold : 0 < τ)
    (threshold_lt_one : τ < 1)
    (_rate_positive : 0 < d)
    (rate_small : d ≤ τ / 2)
    (above_exponential : Real.exp (-d * (n : ℝ)) < θ)
    (realized : θ ≤ S.winProbability) :
    ∃ D : Finset (Fin n),
      (D.card : ℝ) < d * (n : ℝ) / τ ∧
      (n : ℝ) / 2 < ((Finset.univ \ D).card : ℝ) ∧
      θ ≤ repeatedPostselectionMass G n S D ∧
      S.winProbability ≤ repeatedPostselectionMass G n S D ∧
      0 < repeatedPostselectionMass G n S D ∧
      0 < (Finset.univ \ D).card ∧
      uniformRemainingFailure
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D < τ := by
  let T : ℕ := ⌈d * (n : ℝ) / τ⌉₊
  have winning : 0 < S.winProbability :=
    lt_of_lt_of_le ((Real.exp_pos _).trans above_exponential) realized
  have legal : T ≤ n :=
    pdfGreedyCeilingHorizon_le n τ d threshold rate_small
  have terminal : (1 - τ) ^ T < S.winProbability :=
    lt_of_le_of_lt
      (pdfGreedyCeilingHorizon_pow_le_exp
        n τ d threshold threshold_lt_one.le)
      (above_exponential.trans_le realized)
  obtain ⟨D, selected, floor, positive, remaining, failure⟩ :=
    repeatedStrategy_exists_conditioning G n S
      winning threshold threshold_lt_one.le legal terminal
  have strict_card : (D.card : ℝ) < d * (n : ℝ) / τ :=
    pdfGreedyCard_lt_of_ceil D.card n τ d selected
  have half_rate : d * (n : ℝ) / τ ≤ (n : ℝ) / 2 := by
    apply (div_le_iff₀ threshold).mpr
    have actual := mul_le_mul_of_nonneg_right rate_small
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  have selected_le : D.card ≤ n := by
    have actual := Finset.card_le_card (Finset.subset_univ D)
    simpa using actual
  have remaining_real :
      ((Finset.univ \ D).card : ℝ) =
        (n : ℝ) - (D.card : ℝ) := by
    rw [remainingCoordinates_card, Nat.cast_sub selected_le]
  have more_than_half :
      (n : ℝ) / 2 < ((Finset.univ \ D).card : ℝ) := by
    rw [remaining_real]
    nlinarith
  exact ⟨D, strict_card, more_than_half,
    realized.trans floor, floor, positive, remaining, failure⟩

end

noncomputable section

def pdfUniversalRate (B : ℝ) : ℝ :=
  1 / (8 * (4 * B) ^ 12)

def pdfGapRate (B ε ell : ℝ) : ℝ :=
  pdfUniversalRate B * ε ^ 13 / (ε + ell)

def pdfConditioningTolerance (ε : ℝ) : ℝ :=
  ε / 4

def pdfCatalystAccuracy (K ε : ℝ) : ℝ :=
  (ε / (16 * K)) ^ 12

theorem pdfUniversalRate_pos
    {B : ℝ} (positive : 0 < B) :
    0 < pdfUniversalRate B := by
  unfold pdfUniversalRate
  positivity

theorem pdfGapRate_pos
    {B ε ell : ℝ}
    (constant : 0 < B) (gap : 0 < ε) (alphabet : 0 ≤ ell) :
    0 < pdfGapRate B ε ell := by
  unfold pdfGapRate
  have universal := pdfUniversalRate_pos constant
  positivity

theorem pdfGapRate_eq_scaled_twelfth_power
    {B ε ell : ℝ}
    (constant : 0 < B) (gap : 0 < ε) (alphabet : 0 ≤ ell) :
    pdfGapRate B ε ell =
      ε / (8 * (ε + ell)) * (ε / (4 * B)) ^ 12 := by
  have nonzero : B ≠ 0 := ne_of_gt constant
  have denominator : ε + ell ≠ 0 := ne_of_gt (by linarith)
  unfold pdfGapRate pdfUniversalRate
  field_simp

theorem pdfGapBase_le_gap
    {B ε : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) :
    0 < ε / (4 * B) ∧ ε / (4 * B) ≤ ε := by
  have denominator : 0 < 4 * B := by nlinarith
  constructor
  · exact div_pos gap denominator
  · apply (div_le_iff₀ denominator).2
    nlinarith

theorem pdfGapBase_twelfth_le_gap
    {B ε : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) (unit : ε ≤ 1) :
    (ε / (4 * B)) ^ 12 ≤ ε := by
  obtain ⟨nonnegative, bounded⟩ :=
    pdfGapBase_le_gap constant gap
  calc
    (ε / (4 * B)) ^ 12 ≤ ε ^ 12 :=
      pow_le_pow_left₀ nonnegative.le bounded 12
    _ = ε * ε ^ 11 := by ring
    _ ≤ ε * 1 :=
      mul_le_mul_of_nonneg_left
        (pow_le_one₀ gap.le unit) gap.le
    _ = ε := by ring

theorem pdfGapBase_twelfth_le_one
    {B ε : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) (unit : ε ≤ 1) :
    (ε / (4 * B)) ^ 12 ≤ 1 :=
  (pdfGapBase_twelfth_le_gap constant gap unit).trans unit

theorem pdfGapRate_le_gap_div_eight
    {B ε ell : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (unit : ε ≤ 1) (alphabet : 0 ≤ ell) :
    pdfGapRate B ε ell ≤ ε / 8 := by
  have Bpositive : 0 < B := lt_of_lt_of_le (by norm_num) constant
  have denominator : 0 < ε + ell := by linarith
  have fraction : ε / (ε + ell) ≤ 1 := by
    apply (div_le_iff₀ denominator).2
    linarith
  have root := pdfGapBase_twelfth_le_gap constant gap unit
  rw [pdfGapRate_eq_scaled_twelfth_power
    Bpositive gap alphabet]
  have nonnegative : 0 ≤ (ε / (4 * B)) ^ 12 := by positivity
  calc
    ε / (8 * (ε + ell)) * (ε / (4 * B)) ^ 12 =
        (ε / (ε + ell)) * (ε / (4 * B)) ^ 12 / 8 := by
          field_simp [ne_of_gt denominator, ne_of_gt Bpositive]
    _ ≤ 1 * ε / 8 := by
          gcongr
    _ = ε / 8 := by ring

theorem pdfConditioningTolerance_bounds
    {ε : ℝ} (gap : 0 < ε) (unit : ε ≤ 1) :
    0 < pdfConditioningTolerance ε ∧
      pdfConditioningTolerance ε ≤ 1 / 4 := by
  unfold pdfConditioningTolerance
  constructor <;> nlinarith

theorem pdfGapRate_le_half_conditioningTolerance
    {B ε ell : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (unit : ε ≤ 1) (alphabet : 0 ≤ ell) :
    pdfGapRate B ε ell ≤
      pdfConditioningTolerance ε / 2 := by
  have exact_rate := pdfGapRate_le_gap_div_eight
    constant gap unit alphabet
  calc
    pdfGapRate B ε ell ≤ ε / 8 := exact_rate
    _ = pdfConditioningTolerance ε / 2 := by
      unfold pdfConditioningTolerance
      ring

theorem pdfGapRate_entropy_factor
    {B ε ell : ℝ}
    (constant : 0 < B) (gap : 0 < ε) (alphabet : 0 ≤ ell) :
    2 * pdfGapRate B ε ell * (1 + 4 * ell / ε) =
      (ε / (4 * B)) ^ 12 *
        ((ε + 4 * ell) / (4 * (ε + ell))) := by
  have nonzero : B ≠ 0 := ne_of_gt constant
  have gap_nonzero : ε ≠ 0 := ne_of_gt gap
  have denominator : ε + ell ≠ 0 := ne_of_gt (by linarith)
  rw [pdfGapRate_eq_scaled_twelfth_power
    constant gap alphabet]
  field_simp
  ring

theorem pdfAlphabetEntropyFactor_le_one
    {ε ell : ℝ} (gap : 0 < ε) (alphabet : 0 ≤ ell) :
    (ε + 4 * ell) / (4 * (ε + ell)) ≤ 1 := by
  have denominator : 0 < 4 * (ε + ell) := by positivity
  apply (div_le_iff₀ denominator).2
  nlinarith

theorem pdfGapRate_entropy_le_twelfth_power
    {B ε ell : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) (alphabet : 0 ≤ ell) :
    2 * pdfGapRate B ε ell * (1 + 4 * ell / ε) ≤
      (ε / (4 * B)) ^ 12 := by
  have Bpositive : 0 < B := lt_of_lt_of_le (by norm_num) constant
  rw [pdfGapRate_entropy_factor Bpositive gap alphabet]
  have nonnegative : 0 ≤ (ε / (4 * B)) ^ 12 := by positivity
  calc
    (ε / (4 * B)) ^ 12 *
        ((ε + 4 * ell) / (4 * (ε + ell))) ≤
        (ε / (4 * B)) ^ 12 * 1 :=
          mul_le_mul_of_nonneg_left
            (pdfAlphabetEntropyFactor_le_one gap alphabet)
            nonnegative
    _ = _ := by ring

theorem pdfCatalystAccuracy_bounds
    {K ε : ℝ}
    (constant : 1 ≤ K) (gap : 0 < ε) (unit : ε ≤ 1) :
    0 < pdfCatalystAccuracy K ε ∧
      pdfCatalystAccuracy K ε ≤ 1 := by
  have denominator : 0 < 16 * K := by nlinarith
  have ratio : 0 < ε / (16 * K) := div_pos gap denominator
  have bounded : ε / (16 * K) ≤ 1 := by
    apply (div_le_iff₀ denominator).2
    nlinarith
  unfold pdfCatalystAccuracy
  exact ⟨pow_pos ratio 12, pow_le_one₀ ratio.le bounded⟩

theorem pdfQuantitativeEntropyRate_lt
    {n m k : ℕ} {t d τ ell : ℝ}
    (length : 0 < n) (rate : 0 < d) (tolerance : 0 < τ)
    (alphabet : 0 ≤ ell)
    (remaining : (n : ℝ) / 2 < (m : ℝ))
    (postselection : t < d * (n : ℝ))
    (conditioned : (k : ℝ) < d * (n : ℝ) / τ) :
    (t + (k : ℝ) * ell) / (m : ℝ) <
      2 * d * (1 + ell / τ) := by
  have length_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast length
  have mpositive : (0 : ℝ) < (m : ℝ) := by nlinarith
  have ratio_nonnegative : 0 ≤ ell / τ :=
    div_nonneg alphabet tolerance.le
  have factor : 0 < d * (1 + ell / τ) := by
    exact mul_pos rate (by linarith)
  have alphabet_bound :
      (k : ℝ) * ell ≤ (d * (n : ℝ) / τ) * ell :=
    mul_le_mul_of_nonneg_right (le_of_lt conditioned) alphabet
  have numerator :
      t + (k : ℝ) * ell < d * (n : ℝ) * (1 + ell / τ) := by
    calc
      t + (k : ℝ) * ell <
          d * (n : ℝ) + (d * (n : ℝ) / τ) * ell :=
        add_lt_add_of_lt_of_le postselection alphabet_bound
      _ = d * (n : ℝ) * (1 + ell / τ) := by ring
  apply (div_lt_iff₀ mpositive).2
  have horizon : (n : ℝ) < 2 * (m : ℝ) := by nlinarith
  have scaled := mul_lt_mul_of_pos_left horizon factor
  nlinarith

theorem pdfQuantitativeEntropyRate_lt_twelfth_power
    {B ε ell : ℝ} {n m k : ℕ} {t : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (unit : ε ≤ 1) (alphabet : 0 ≤ ell)
    (length : 0 < n)
    (remaining : (n : ℝ) / 2 < (m : ℝ))
    (postselection :
      t < pdfGapRate B ε ell * (n : ℝ))
    (conditioned :
      (k : ℝ) <
        pdfGapRate B ε ell * (n : ℝ) /
          pdfConditioningTolerance ε) :
    (t + (k : ℝ) * ell) / (m : ℝ) <
      (ε / (4 * B)) ^ 12 := by
  have Bpositive : 0 < B := lt_of_lt_of_le (by norm_num) constant
  have dpositive := pdfGapRate_pos Bpositive gap alphabet
  have taupositive : 0 < pdfConditioningTolerance ε :=
    (pdfConditioningTolerance_bounds gap unit).1
  have entropy := pdfQuantitativeEntropyRate_lt
    length dpositive taupositive alphabet remaining
    postselection conditioned
  have rewrite :
      2 * pdfGapRate B ε ell *
          (1 + ell / pdfConditioningTolerance ε) =
        2 * pdfGapRate B ε ell * (1 + 4 * ell / ε) := by
    unfold pdfConditioningTolerance
    have nonzero : ε ≠ 0 := ne_of_gt gap
    field_simp
  rw [rewrite] at entropy
  exact lt_of_lt_of_le entropy
    (pdfGapRate_entropy_le_twelfth_power
      constant gap alphabet)

theorem pdfCatalystAccuracy_twelfth_root
    {K ε : ℝ} (constant : 1 ≤ K) (gap : 0 < ε) :
    (pdfCatalystAccuracy K ε) ^ (1 / 12 : ℝ) =
      ε / (16 * K) := by
  have denominator : 0 < 16 * K := by nlinarith
  have base : 0 ≤ ε / (16 * K) := (div_pos gap denominator).le
  unfold pdfCatalystAccuracy
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast base (by norm_num : (12 : ℕ) ≠ 0))

theorem pdfGapBase_twelfth_root
    {B ε : ℝ} (constant : 1 ≤ B) (gap : 0 < ε) :
    ((ε / (4 * B)) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) =
      ε / (4 * B) := by
  have base : 0 ≤ ε / (4 * B) :=
    (pdfGapBase_le_gap constant gap).1.le
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast base (by norm_num : (12 : ℕ) ≠ 0))

theorem pdfEntropyRoot_lt_gapBase
    {B ε η : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (entropy : 0 ≤ η)
    (small : η < (ε / (4 * B)) ^ (12 : ℕ)) :
    η ^ (1 / 12 : ℝ) < ε / (4 * B) := by
  calc
    η ^ (1 / 12 : ℝ) <
        ((ε / (4 * B)) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) :=
      Real.rpow_lt_rpow entropy small (by norm_num)
    _ = ε / (4 * B) :=
      pdfGapBase_twelfth_root constant gap

theorem pdfEntropyRoundingLoss_lt_gapQuarter
    {B ε η : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (entropy : 0 ≤ η)
    (small : η < (ε / (4 * B)) ^ (12 : ℕ)) :
    B * η ^ (1 / 12 : ℝ) < ε / 4 := by
  have coefficient : 0 < B := by linarith
  calc
    B * η ^ (1 / 12 : ℝ) < B * (ε / (4 * B)) :=
      mul_lt_mul_of_pos_left
        (pdfEntropyRoot_lt_gapBase constant gap entropy small)
        coefficient
    _ = ε / 4 := by
      field_simp

theorem pdfCatalystAccuracy_samplingLoss
    {K ε : ℝ} (constant : 1 ≤ K) (gap : 0 < ε) :
    2 * K * (pdfCatalystAccuracy K ε) ^ (1 / 12 : ℝ) =
      ε / 8 := by
  have coefficient : 0 < K := by linarith
  rw [pdfCatalystAccuracy_twelfth_root constant gap]
  field_simp
  norm_num

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

def pdfRoundingCoefficient (K : ℝ) : ℝ :=
  (5 + 2 * universalErrorCeiling K) * Real.sqrt (3 / 2 : ℝ) +
    2 * K * (32 : ℝ) ^ (1 / 12 : ℝ) +
    2 * Real.sqrt 8

theorem pdfUniversalErrorCeiling_pos
    {K : ℝ} (constant : 1 ≤ K) :
    0 < universalErrorCeiling K := by
  have nonnegative : 0 ≤ K := by linarith
  unfold universalErrorCeiling
  positivity

theorem pdfRoundingCoefficient_two_le
    {K : ℝ} (constant : 1 ≤ K) :
    2 ≤ pdfRoundingCoefficient K := by
  have nonnegative : 0 ≤ K := by linarith
  have ceiling_nonnegative : 0 ≤ universalErrorCeiling K :=
    (pdfUniversalErrorCeiling_pos constant).le
  have first_nonnegative :
      0 ≤ (5 + 2 * universalErrorCeiling K) *
        Real.sqrt (3 / 2 : ℝ) := by positivity
  have quantum_nonnegative :
      0 ≤ 2 * K * (32 : ℝ) ^ (1 / 12 : ℝ) := by positivity
  have eight : 1 ≤ Real.sqrt (8 : ℝ) :=
    Real.one_le_sqrt.mpr (by norm_num)
  unfold pdfRoundingCoefficient
  nlinarith

theorem pdfRoundingCoefficient_one_le
    {K : ℝ} (constant : 1 ≤ K) :
    1 ≤ pdfRoundingCoefficient K := by
  have lower := pdfRoundingCoefficient_two_le constant
  linarith

end

noncomputable section

theorem pdfSqrt_le_twelfthRoot
    {eta : ℝ} (nonnegative : 0 ≤ eta) (bounded : eta ≤ 1) :
    Real.sqrt eta ≤ eta ^ (1 / 12 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge'
    nonnegative bounded (by norm_num) (by norm_num)

theorem pdfPinskerRoot_le_twelfthRoot
    {eta kappa : ℝ}
    (nonnegative : 0 ≤ eta)
    (bounded : eta ≤ 1)
    (pinsker : kappa ≤ Real.sqrt ((3 / 2 : ℝ) * eta)) :
    kappa ≤ Real.sqrt (3 / 2 : ℝ) * eta ^ (1 / 12 : ℝ) := by
  calc
    kappa ≤ Real.sqrt ((3 / 2 : ℝ) * eta) := pinsker
    _ = Real.sqrt (3 / 2 : ℝ) * Real.sqrt eta := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    _ ≤ Real.sqrt (3 / 2 : ℝ) * eta ^ (1 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (pdfSqrt_le_twelfthRoot nonnegative bounded)
        (Real.sqrt_nonneg _)

theorem pdfSqrtEight_le_twelfthRoot
    {eta : ℝ} (nonnegative : 0 ≤ eta) (bounded : eta ≤ 1) :
    Real.sqrt (8 * eta) ≤
      Real.sqrt (8 : ℝ) * eta ^ (1 / 12 : ℝ) := by
  calc
    Real.sqrt (8 * eta) =
        Real.sqrt (8 : ℝ) * Real.sqrt eta := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    _ ≤ Real.sqrt (8 : ℝ) * eta ^ (1 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (pdfSqrt_le_twelfthRoot nonnegative bounded)
        (Real.sqrt_nonneg _)

theorem pdfQuantitativeRoundingLoss
    {K alpha eta kappa gamma : ℝ}
    (constant : 0 ≤ K)
    (nonnegative : 0 ≤ eta)
    (bounded : eta ≤ 1)
    (pinsker : kappa ≤ Real.sqrt ((3 / 2 : ℝ) * eta)) :
    totalSamplingLoss K alpha eta (kappa + gamma) ≤
      2 * K * alpha ^ (1 / 12 : ℝ) +
        pdfRoundingCoefficient K * eta ^ (1 / 12 : ℝ) +
        (5 + 2 * universalErrorCeiling K) * gamma := by
  have ceiling : 0 ≤ universalErrorCeiling K := by
    unfold universalErrorCeiling
    positivity
  have classical_coefficient :
      0 ≤ 5 + 2 * universalErrorCeiling K := by
    nlinarith
  have pinsker_bound :=
    pdfPinskerRoot_le_twelfthRoot nonnegative bounded pinsker
  have weighted_pinsker :
      (5 + 2 * universalErrorCeiling K) * kappa ≤
        (5 + 2 * universalErrorCeiling K) *
          (Real.sqrt (3 / 2 : ℝ) * eta ^ (1 / 12 : ℝ)) :=
    mul_le_mul_of_nonneg_left pinsker_bound classical_coefficient
  have sqrt_bound :=
    pdfSqrtEight_le_twelfthRoot nonnegative bounded
  have weighted_sqrt :
      2 * Real.sqrt (8 * eta) ≤
        2 * (Real.sqrt (8 : ℝ) * eta ^ (1 / 12 : ℝ)) :=
    mul_le_mul_of_nonneg_left sqrt_bound (by norm_num)
  have source_bounds := add_le_add weighted_pinsker weighted_sqrt
  calc
    totalSamplingLoss K alpha eta (kappa + gamma) =
        2 * K * alpha ^ (1 / 12 : ℝ) +
          ((5 + 2 * universalErrorCeiling K) * kappa +
            2 * Real.sqrt (8 * eta)) +
          2 * K *
            ((32 : ℝ) ^ (1 / 12 : ℝ) * eta ^ (1 / 12 : ℝ)) +
          (5 + 2 * universalErrorCeiling K) * gamma := by
      unfold totalSamplingLoss
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) nonnegative]
      ring
    _ ≤ 2 * K * alpha ^ (1 / 12 : ℝ) +
          ((5 + 2 * universalErrorCeiling K) *
              (Real.sqrt (3 / 2 : ℝ) * eta ^ (1 / 12 : ℝ)) +
            2 * (Real.sqrt (8 : ℝ) * eta ^ (1 / 12 : ℝ))) +
          2 * K *
            ((32 : ℝ) ^ (1 / 12 : ℝ) * eta ^ (1 / 12 : ℝ)) +
          (5 + 2 * universalErrorCeiling K) * gamma := by
      gcongr
    _ = 2 * K * alpha ^ (1 / 12 : ℝ) +
          pdfRoundingCoefficient K * eta ^ (1 / 12 : ℝ) +
          (5 + 2 * universalErrorCeiling K) * gamma := by
      unfold pdfRoundingCoefficient
      ring

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem pdfExistsRepeatedStrategyAboveExponential
    (G : Game X Y A B) (n : ℕ) (d : ℝ)
    (failure : Real.exp (-d * (n : ℝ)) < repeatedEntangledValue G n) :
    ∃ S : Strategy (G.repeat n),
      Real.exp (-d * (n : ℝ)) < S.winProbability :=
  exists_repeatedStrategy_of_lt_entangledValue
    G (Real.exp_pos _) failure

theorem pdfFixedExponentialBound_of_sourceEquationTwentyNine
    (G : Game X Y A B) (n : ℕ) (d : ℝ)
    (construct :
      ∀ S : Strategy (G.repeat n),
        Real.exp (-d * (n : ℝ)) < S.winProbability →
          ∃ (rounded : Strategy G) (K₀ α η lam : ℝ),
            roundedWinningLowerBound (1 - entangledValue G)
                K₀ α η lam ≤ rounded.winProbability ∧
              totalSamplingLoss K₀ α η lam <
                (1 - entangledValue G) / 2) :
    repeatedEntangledValue G n ≤ Real.exp (-d * (n : ℝ)) := by
  by_contra not_bound
  have failure :
      Real.exp (-d * (n : ℝ)) < repeatedEntangledValue G n :=
    lt_of_not_ge not_bound
  obtain ⟨S, winning⟩ :=
    pdfExistsRepeatedStrategyAboveExponential G n d failure
  obtain ⟨rounded, K₀, α, η, lam, bound, error⟩ :=
    construct S winning
  exact source_equation_twenty_nine_contradiction
    G rounded K₀ α η lam bound error

end

noncomputable section

open scoped BigOperators

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem entangledValue_eq_zero_of_strategyWinProbability_eq_zero
    (G : Game X Y A B)
    (hzero : ∀ S : Strategy G, S.winProbability = 0) :
    entangledValue G = 0 := by
  apply le_antisymm _ (entangledValue_nonneg G)
  unfold entangledValue
  by_cases hnonempty :
      (Set.range (Strategy.winProbability (G := G))).Nonempty
  · apply csSup_le hnonempty
    rintro _ ⟨S, rfl⟩
    exact le_of_eq (hzero S)
  · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty,
      Real.sSup_empty]

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def pdfConstantDensity : DensityMatrix (PUnit × PUnit) where
  matrix := 1
  positive := Matrix.PosSemidef.one
  trace_one := by
    simp [Matrix.trace]

def pdfConstantPOVM
    {C : Type*} [Fintype C] (answer : C) : POVM C PUnit := by
  classical
  exact
    { effect := fun c => if c = answer then 1 else 0
      positive := by
        intro c
        split_ifs
        · exact Matrix.PosSemidef.one
        · exact Matrix.PosSemidef.zero
      complete := by simp }

def pdfConstantStrategy
    (G : Game X Y A B) (a : A) (b : B) : Strategy G := by
  classical
  exact
    { Alice := PUnit
      Bob := PUnit
      state := pdfConstantDensity
      aliceMeasurement := fun _ => pdfConstantPOVM a
      bobMeasurement := fun _ => pdfConstantPOVM b }

theorem pdfConstantStrategy_outcomeProbability
    (G : Game X Y A B) (a : A) (b : B)
    (x : X) (y : Y) (a' : A) (b' : B) :
    (pdfConstantStrategy G a b).outcomeProbability x y a' b' =
      if a' = a ∧ b' = b then 1 else 0 := by
  classical
  change
    (Matrix.trace
      ((1 : Matrix (PUnit × PUnit) (PUnit × PUnit) ℂ) *
        ((if a' = a then (1 : Matrix PUnit PUnit ℂ) else 0) ⊗ₖ
          (if b' = b then (1 : Matrix PUnit PUnit ℂ) else 0)))).re = _
  by_cases alice : a' = a <;> by_cases bob : b' = b <;>
    simp [alice, bob, Matrix.trace_one]

theorem pdfConstantStrategy_winProbability
    (G : Game X Y A B) (a : A) (b : B) :
    (pdfConstantStrategy G a b).winProbability =
      ∑ x : X, ∑ y : Y,
        if G.predicate x y a b = true then G.questionWeight x y else 0 := by
  classical
  have accepted_outcome (x : X) (y : Y) (a' : A) (b' : B) :
      (if G.predicate x y a' b' = true then
        (if a' = a ∧ b' = b then (1 : ℝ) else 0)
      else 0) =
        if a' = a then
          if b' = b then
            if G.predicate x y a b = true then 1 else 0
          else 0
        else 0 := by
    by_cases alice : a' = a <;> by_cases bob : b' = b <;>
      simp_all
  unfold Strategy.winProbability
  simp_rw [pdfConstantStrategy_outcomeProbability]
  simp_rw [accepted_outcome]
  simp [mul_ite]

theorem pdfQuestionWeight_le_constantStrategy
    (G : Game X Y A B)
    (x : X) (y : Y) (a : A) (b : B)
    (accepted : G.predicate x y a b = true) :
    G.questionWeight x y ≤
      (pdfConstantStrategy G a b).winProbability := by
  classical
  rw [pdfConstantStrategy_winProbability]
  calc
    G.questionWeight x y =
        if G.predicate x y a b = true then G.questionWeight x y else 0 := by
          simp [accepted]
    _ ≤ ∑ y' : Y,
        if G.predicate x y' a b = true then G.questionWeight x y' else 0 := by
          exact Finset.single_le_sum
            (f := fun y' : Y =>
              if G.predicate x y' a b = true then G.questionWeight x y' else 0)
            (fun y' _ => by split_ifs <;> simp [G.weight_nonneg])
            (Finset.mem_univ y)
    _ ≤ ∑ x' : X, ∑ y' : Y,
        if G.predicate x' y' a b = true then G.questionWeight x' y' else 0 := by
          exact Finset.single_le_sum
            (f := fun x' : X => ∑ y' : Y,
              if G.predicate x' y' a b = true then G.questionWeight x' y' else 0)
            (fun x' _ => Finset.sum_nonneg
              (fun y' _ => by split_ifs <;> simp [G.weight_nonneg]))
            (Finset.mem_univ x)

theorem pdfPredicate_not_accepted_of_entangledValue_eq_zero
    (G : Game X Y A B)
    (zero : entangledValue G = 0)
    (x : X) (y : Y) (a : A) (b : B)
    (supported : 0 < G.questionWeight x y) :
    G.predicate x y a b ≠ true := by
  intro accepted
  have lower := pdfQuestionWeight_le_constantStrategy
    G x y a b accepted
  have upper :
      (pdfConstantStrategy G a b).winProbability ≤
        entangledValue G := by
    unfold entangledValue
    exact le_csSup (winProbabilities_bddAbove G)
      ⟨pdfConstantStrategy G a b, rfl⟩
  linarith

theorem pdfRepeatedEntangledValue_eq_zero_of_entangledValue_eq_zero
    (G : Game X Y A B)
    (zero : entangledValue G = 0)
    {n : ℕ} (positive : 0 < n) :
    repeatedEntangledValue G n = 0 := by
  classical
  let i : Fin n := ⟨0, positive⟩
  apply entangledValue_eq_zero_of_strategyWinProbability_eq_zero (G.repeat n)
  intro S
  unfold Strategy.winProbability
  apply Finset.sum_eq_zero
  intro xs _
  apply Finset.sum_eq_zero
  intro ys _
  by_cases zero_weight : (G.repeat n).questionWeight xs ys = 0
  · change (G.repeat n).questionWeight xs ys * _ = 0
    rw [zero_weight, zero_mul]
  · have local_nonzero : G.questionWeight (xs i) (ys i) ≠ 0 := by
      intro local_zero
      apply zero_weight
      rw [Game.repeat_questionWeight]
      exact Finset.prod_eq_zero (Finset.mem_univ i) local_zero
    have supported : 0 < G.questionWeight (xs i) (ys i) :=
      lt_of_le_of_ne (G.weight_nonneg (xs i) (ys i)) local_nonzero.symm
    have never (as : Fin n → A) (bs : Fin n → B) :
        (G.repeat n).predicate xs ys as bs ≠ true := by
      intro accepted
      exact pdfPredicate_not_accepted_of_entangledValue_eq_zero
        G zero (xs i) (ys i) (as i) (bs i) supported
        ((Game.repeat_predicate_eq_true G n xs ys as bs).mp accepted i)
    simp [never]

end

noncomputable section

theorem pdfAlphabetEntropy_nonneg
    {A B : Type} [Fintype A] [Fintype B]
    (alice : Nonempty A) (bob : Nonempty B) :
    0 ≤ Real.log
      ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) := by
  have alice_card : 0 < Fintype.card A :=
    Fintype.card_pos_iff.mpr alice
  have bob_card : 0 < Fintype.card B :=
    Fintype.card_pos_iff.mpr bob
  have alice_real : (1 : ℝ) ≤ (Fintype.card A : ℝ) := by
    exact_mod_cast alice_card
  have bob_real : (1 : ℝ) ≤ (Fintype.card B : ℝ) := by
    exact_mod_cast bob_card
  apply Real.log_nonneg
  nlinarith [mul_nonneg (sub_nonneg.mpr alice_real)
    (sub_nonneg.mpr bob_real)]

theorem pdfGap_le_one
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) :
    1 - entangledValue G ≤ 1 := by
  have nonnegative := entangledValue_nonneg G
  linarith

theorem pdfPostselectionLogCost_lt_of_exponential
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (d : ℝ)
    (above : Real.exp (-d * (n : ℝ)) <
      repeatedPostselectionMass G n S D) :
    postselectionLogCost G n S D < d * (n : ℝ) := by
  have logarithm := Real.log_lt_log (Real.exp_pos (-d * (n : ℝ))) above
  rw [Real.log_exp] at logarithm
  unfold postselectionLogCost
  rw [one_div, Real.log_inv]
  linarith

theorem pdfPinskerRate_le_sqrt_martingaleRate
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    exactSourcePinskerRate G n S D ≤
      Real.sqrt ((3 / 2 : ℝ) * martingaleRate G n S D) := by
  unfold exactSourcePinskerRate
  apply Real.sqrt_le_sqrt
  have information :=
    exactSourceClassicalInformationRate_le_three_martingaleRate
      G n S D positive
  nlinarith

theorem pdfActualMartingaleRate_lt_twelfth_power
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (Bqs ε ell : ℝ)
    (constant : 1 ≤ Bqs)
    (gap : 0 < ε)
    (unit : ε ≤ 1)
    (alphabet : 0 ≤ ell)
    (alphabet_eq : ell =
      Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))
    (length : 0 < n)
    (remaining :
      (n : ℝ) / 2 < ((Finset.univ \ D).card : ℝ))
    (above :
      Real.exp
        (-pdfGapRate Bqs ε ell * (n : ℝ)) <
        repeatedPostselectionMass G n S D)
    (conditioned :
      (D.card : ℝ) <
        pdfGapRate Bqs ε ell * (n : ℝ) /
          pdfConditioningTolerance ε) :
    martingaleRate G n S D < (ε / (4 * Bqs)) ^ 12 := by
  have postselection :=
    pdfPostselectionLogCost_lt_of_exponential
      G n S D (pdfGapRate Bqs ε ell) above
  have actual := pdfQuantitativeEntropyRate_lt_twelfth_power
    constant gap unit alphabet length remaining postselection conditioned
  simpa [martingaleRate, answerLogCost, alphabet_eq]
    using actual

theorem pdfFullQuantitativeSamplingLoss
    {K ε eta kappa : ℝ}
    (constant : 1 ≤ K)
    (gap : 0 < ε)
    (unit : ε ≤ 1)
    (entropy : 0 ≤ eta)
    (small :
      eta <
        (ε / (4 * pdfRoundingCoefficient K)) ^ (12 : ℕ))
    (pinsker : kappa ≤ Real.sqrt ((3 / 2 : ℝ) * eta)) :
    totalSamplingLoss K (pdfCatalystAccuracy K ε) eta
      (kappa + ε / (16 * (5 + 2 * universalErrorCeiling K))) <
        ε / 2 := by
  have coefficient : 1 ≤ pdfRoundingCoefficient K :=
    pdfRoundingCoefficient_one_le constant
  have bounded : eta ≤ 1 :=
    small.le.trans
      (pdfGapBase_twelfth_le_one coefficient gap unit)
  have loss := pdfQuantitativeRoundingLoss
    (K := K) (alpha := pdfCatalystAccuracy K ε)
    (eta := eta) (kappa := kappa)
    (gamma := ε / (16 * (5 + 2 * universalErrorCeiling K)))
    (by linarith) entropy bounded pinsker
  have entropy_loss :
      pdfRoundingCoefficient K * eta ^ (1 / 12 : ℝ) <
        ε / 4 :=
    pdfEntropyRoundingLoss_lt_gapQuarter
      coefficient gap entropy small
  have catalyst_loss :
      2 * K *
        (pdfCatalystAccuracy K ε) ^ (1 / 12 : ℝ) =
        ε / 8 :=
    pdfCatalystAccuracy_samplingLoss constant gap
  have ceiling : 0 < universalErrorCeiling K :=
    pdfUniversalErrorCeiling_pos constant
  have gamma_loss :
      (5 + 2 * universalErrorCeiling K) *
          (ε / (16 * (5 + 2 * universalErrorCeiling K))) =
        ε / 16 := by
    field_simp
  linarith

theorem pdf_distributionUniformExponential_of_uniform_source_rounding
    (rounding :
      ∃ K : ℝ, 1 ≤ K ∧
        ∀ {X Y A B : Type}
          [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
          (G : Game X Y A B)
          (n : ℕ) (S : Strategy (G.repeat n))
          (D : Finset (Fin n)),
          0 < (Finset.univ \ D).card →
          0 < repeatedPostselectionMass G n S D →
          ∀ (alpha gamma : ℝ),
            0 < alpha → alpha ≤ 1 → 0 < gamma →
            uniformRemainingFailure
                (strategyEventLaw (G.repeat n) S)
                (repeatedCoordinateWin G n) D <
              (1 - entangledValue G) / 2 →
            ∃ rounded : Strategy G,
              roundedWinningLowerBound (1 - entangledValue G)
                  K alpha (martingaleRate G n S D)
                  (exactSourcePinskerRate G n S D + gamma) ≤
                rounded.winProbability) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B),
        Nonempty A → Nonempty B →
        0 < 1 - entangledValue G →
        ∀ n : ℕ, 0 < n →
          repeatedEntangledValue G n ≤
            Real.exp
              (-(c *
                ((1 - entangledValue G) ^ 13 /
                  ((1 - entangledValue G) +
                    Real.log
                      ((Fintype.card A : ℝ) *
                        (Fintype.card B : ℝ))))) * (n : ℝ)) := by
  obtain ⟨K, constant, round⟩ := rounding
  let Bqs : ℝ := pdfRoundingCoefficient K
  have coefficient : 1 ≤ Bqs :=
    pdfRoundingCoefficient_one_le constant
  refine ⟨pdfUniversalRate Bqs,
    pdfUniversalRate_pos (by linarith), ?_⟩
  intro X Y A B _ _ _ _ G alice bob game_gap n length
  by_cases zero : entangledValue G = 0
  · rw [pdfRepeatedEntangledValue_eq_zero_of_entangledValue_eq_zero
      G zero length]
    exact (Real.exp_pos _).le
  · let ε : ℝ := 1 - entangledValue G
    let ell : ℝ :=
      Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))
    let d : ℝ := pdfGapRate Bqs ε ell
    let τ : ℝ := pdfConditioningTolerance ε
    have gap : 0 < ε := by
      simpa [ε] using game_gap
    have unit : ε ≤ 1 := by
      simpa [ε] using pdfGap_le_one G
    have alphabet : 0 ≤ ell := by
      exact pdfAlphabetEntropy_nonneg alice bob
    have tolerance := pdfConditioningTolerance_bounds gap unit
    have tolerance_positive : 0 < τ := tolerance.1
    have tolerance_lt_one : τ < 1 := by
      have at_most := tolerance.2
      dsimp [τ]
      linarith
    have rate_positive : 0 < d :=
      pdfGapRate_pos (by linarith) gap alphabet
    have rate_small : d ≤ τ / 2 :=
      pdfGapRate_le_half_conditioningTolerance
        coefficient gap unit alphabet
    have exponential :
        repeatedEntangledValue G n ≤ Real.exp (-d * (n : ℝ)) := by
      apply pdfFixedExponentialBound_of_sourceEquationTwentyNine
        G n d
      intro S winning
      obtain ⟨D, selected, remaining_real, postselection_floor,
          _strategy_floor, positive, remaining, failure⟩ :=
        pdfQuantitativeGreedyConditioning
          G n S τ d S.winProbability length
          tolerance_positive tolerance_lt_one rate_positive rate_small
          winning (le_refl _)
      have above :
          Real.exp (-d * (n : ℝ)) <
            repeatedPostselectionMass G n S D :=
        winning.trans_le postselection_floor
      have small :
          martingaleRate G n S D <
            (ε / (4 * Bqs)) ^ (12 : ℕ) := by
        apply pdfActualMartingaleRate_lt_twelfth_power
          G n S D Bqs ε ell coefficient gap unit alphabet
          (by rfl) length remaining_real
        · exact above
        · exact selected
      have entropy : 0 ≤ martingaleRate G n S D :=
        martingaleRate_nonneg G n S D remaining positive
      have pinsker :
          exactSourcePinskerRate G n S D ≤
            Real.sqrt
              ((3 / 2 : ℝ) * martingaleRate G n S D) :=
        pdfPinskerRate_le_sqrt_martingaleRate
          G n S D positive
      let alpha : ℝ := pdfCatalystAccuracy K ε
      let gamma : ℝ :=
        ε / (16 * (5 + 2 * universalErrorCeiling K))
      have alpha_bounds :=
        pdfCatalystAccuracy_bounds constant gap unit
      have alpha_positive : 0 < alpha := alpha_bounds.1
      have alpha_at_most_one : alpha ≤ 1 := alpha_bounds.2
      have ceiling : 0 < universalErrorCeiling K :=
        pdfUniversalErrorCeiling_pos constant
      have gamma_positive : 0 < gamma := by
        dsimp [gamma]
        positivity
      have source_failure :
          uniformRemainingFailure
              (strategyEventLaw (G.repeat n) S)
              (repeatedCoordinateWin G n) D <
            (1 - entangledValue G) / 2 := by
        change
          uniformRemainingFailure
              (strategyEventLaw (G.repeat n) S)
              (repeatedCoordinateWin G n) D < ε / 2
        have actual :
            uniformRemainingFailure
                (strategyEventLaw (G.repeat n) S)
                (repeatedCoordinateWin G n) D < ε / 4 := by
          simpa [τ, pdfConditioningTolerance] using failure
        linarith
      obtain ⟨rounded, rounded_bound⟩ :=
        round G n S D remaining positive alpha gamma
          alpha_positive alpha_at_most_one gamma_positive source_failure
      refine ⟨rounded, K, alpha,
        martingaleRate G n S D,
        exactSourcePinskerRate G n S D + gamma,
        rounded_bound, ?_⟩
      have actual_loss := pdfFullQuantitativeSamplingLoss
        constant gap unit entropy
        (show martingaleRate G n S D <
          (ε / (4 * pdfRoundingCoefficient K)) ^ (12 : ℕ) by
            simpa [Bqs] using small)
        pinsker
      change totalSamplingLoss K alpha
          (martingaleRate G n S D)
          (exactSourcePinskerRate G n S D + gamma) <
        (1 - entangledValue G) / 2
      simpa [alpha, gamma, ε] using actual_loss
    simpa [d, pdfGapRate, ε, ell, div_eq_mul_inv,
      mul_assoc] using exponential

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

def unconditionalSourcePhysicalRoundingUniversalConstant : ℝ :=
  1024 + 8 *
    (4 * Real.sqrt
      (34 + unconditionalPrefactorBucketCoefficient) + 2)

theorem unconditionalSourcePhysicalRoundingUniversalConstant_ge :
    128 ≤ unconditionalSourcePhysicalRoundingUniversalConstant := by
  unfold unconditionalSourcePhysicalRoundingUniversalConstant
  nlinarith [Real.sqrt_nonneg
    (34 + unconditionalPrefactorBucketCoefficient)]

theorem unconditionalSourcePhysicalRounding_exists_sourceSampler
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (gamma : ℝ) (gamma_positive : 0 < gamma) :
    ∃ (base : ExactHistoryFlag X Y A B D)
      (denominator : ℕ),
      0 < denominator ∧
      ∃ numerator : ExactLocalSamplerIndex X Y D →
          ExactHistoryFlag X Y A B D → ℕ,
        (∀ index, (∑ history, numerator index history) = denominator) ∧
        (∀ index history,
          0 < exactLocalConditionalFamily D base
              (exactLocallySampleableLaw G n S D) index history →
            0 < numerator index history) ∧
        ∃ nonempty : ∀ index,
          (rationalMarked denominator (numerator index)).Nonempty,
          QuantumParallelRepetition.Pinsker.finiteTotalVariation
              (flaggedQuestionWeight G
                (exactSourceSharedFlagWeight D denominator))
              (exactSourceAliceFlagCoupling
                G n S D denominator numerator nonempty) ≤
            exactSourcePinskerRate G n S D + gamma ∧
          (∑ outcome :
            ExactSourceSharedFlag X Y A B D denominator × (X × Y),
            flaggedQuestionWeight G
                (exactSourceSharedFlagWeight D denominator) outcome *
              if exactSourcePermutationMatched
                D denominator numerator nonempty outcome
              then 0 else 1) ≤
            4 * (exactSourcePinskerRate G n S D + gamma) := by
  classical
  let base : ExactHistoryFlag X Y A B D :=
    Classical.choice
      (exactSourceHistoryFlag_nonempty_of_positive
        G n S D remaining positive)
  exact ⟨base,
    unconditionalActualSourceSamplerBounds
      G n S D remaining positive base gamma gamma_positive⟩

theorem unconditionalSourcePhysicalRounding_fairTargetEnergy
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ h : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D h *
        ‖(exactGlobalHistoryFinGamma
            G n S D h.2.2.2 h.2.1).val -
          (exactGlobalHistoryFinPhi
            G n S D h.2.2.2 h.2.2.1).val‖ ^ 2) ≤
      32 * martingaleRate G n S D := by
  have distance := exactSourceStateDistanceBound_of_positive
    G n S D remaining positive
  simpa [exactSourceTupleGamma, exactSourceTuplePhi] using
    (exactSourceEquationTwentyOne_of_fifteen
      G n S D positive (martingaleRate G n S D) distance)

theorem unconditionalSourcePhysicalRounding_exists_fairStoppingHazard
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha : ℝ)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1) :
    ∃ (w : ℝ) (N L B' Q m : ℕ),
      1 ≤ w ∧ 0 < N ∧ 0 < L ∧ 0 < B' ∧ 0 < Q ∧ 0 < m ∧
      2 * (w + 1) *
          ((Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) : ℝ) / N) ≤
        alpha ^ (1 / 3 : ℝ) ∧
      (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D) : ℝ) /
          (N : ℝ) < 1 / (w + 1) ∧
      (1 / w +
        (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D) : ℝ) *
          w / (N : ℝ) ≤ 3 * alpha ^ (1 / 3 : ℝ) / 2) ∧
      ∃ UA UB : Fin B' → Option ℕ →
          Matrix.unitaryGroup (Fin (N * m)) ℂ,
        let width : Fin 1 → ℝ := fun _ => w
        let schedule : Fin L → Fin 1 := fun _ => 0
        let eta : ℝ := martingaleRate G n S D
        let delta : ℝ := alpha ^ (1 / 3 : ℝ)
        let t : ℝ := Real.sqrt (64 * Real.sqrt eta + delta)
        let rho : ℝ := alpha ^ (1 / 12 : ℝ)
        (∀ ξ : BipartiteUnitVector
            (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)),
          ‖ξ.val - dSVDensityRationalCanonicalAcceptedTarget
              w N ξ‖ ^ 2 ≤ 3 * delta / 2) ∧
        ((∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
              N width schedule
              (exactGlobalHistoryFinGamma
                G n S D h.2.2.2 h.2.1)
              (exactGlobalHistoryFinPhi
                G n S D h.2.2.2 h.2.2.1)) ≤
            64 * Real.sqrt eta + delta) ∧
        ((∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            dSVDensityRationalHeterogeneousPhysicalTerminalMass
              N width schedule
              (exactGlobalHistoryFinGamma
                G n S D h.2.2.2 h.2.1)
              (exactGlobalHistoryFinPhi
                G n S D h.2.2.2 h.2.2.1)) ≤ delta ^ 2) ∧
        ((∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
              Q m width schedule
              (exactGlobalHistoryFinGamma
                G n S D h.2.2.2 h.2.1)
              (exactGlobalHistoryFinPhi
                G n S D h.2.2.2 h.2.2.1)
              UA UB) ≤
            (34 / t) * (64 * Real.sqrt eta + delta) +
              4 * rho ^ 2 +
                unconditionalPrefactorBucketCoefficient * t) := by
  classical
  let d : ℕ := Fintype.card
    (ExactGlobalHistoryLocalIndex G n S D)
  have dimension : 0 < d :=
    exactGlobalHistoryLocalIndex_card_pos G n S D
  let eta : ℝ := martingaleRate G n S D
  let delta : ℝ := alpha ^ (1 / 3 : ℝ)
  let t : ℝ := Real.sqrt (64 * Real.sqrt eta + delta)
  let rho : ℝ := alpha ^ (1 / 12 : ℝ)
  have eta_nonnegative : 0 ≤ eta :=
    martingaleRate_nonneg G n S D remaining positive
  have delta_positive : 0 < delta :=
    Real.rpow_pos_of_pos alpha_positive _
  have delta_bounded : delta ≤ 1 :=
    Real.rpow_le_one alpha_positive.le alpha_bounded (by norm_num)
  have t_positive : 0 < t := by
    dsimp [t]
    apply Real.sqrt_pos.2
    nlinarith [Real.sqrt_nonneg eta]
  have t_bounded : t ≤ 1 := by
    dsimp [t]
    have bound : 64 * Real.sqrt eta + delta ≤ 1 := by
      simpa [eta, delta] using small
    nlinarith [Real.sqrt_nonneg
      (64 * Real.sqrt eta + delta),
      Real.sq_sqrt (show 0 ≤ 64 * Real.sqrt eta + delta by positivity)]
  have rho_positive : 0 < rho :=
    Real.rpow_pos_of_pos alpha_positive _
  obtain ⟨w, N, width_large, grid, budget, scalar, canonical, _⟩ :=
    unconditionalExactSourceScalarClipping
      d dimension alpha alpha_positive alpha_bounded
  have precision_budget :
      2 * (w + 1) * ((d : ℝ) / N) ≤ delta := by
    simpa [delta] using budget
  have grid_fine :
      (d : ℝ) / (N : ℝ) < 1 / (w + 1) := by
    apply (lt_div_iff₀
      (show 0 < w + 1 by linarith only [width_large])).2
    nlinarith only [precision_budget, delta_bounded]
  let law : ExactLocallySampleableTuple X Y A B D → ℝ :=
    exactLocallySampleableLaw G n S D
  let gamma : ExactLocallySampleableTuple X Y A B D →
      BipartiteUnitVector d := fun h =>
    exactGlobalHistoryFinGamma G n S D h.2.2.2 h.2.1
  let phi : ExactLocallySampleableTuple X Y A B D →
      BipartiteUnitVector d := fun h =>
    exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1
  have energy :
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        law h * ‖(gamma h).val - (phi h).val‖ ^ 2) ≤ 32 * eta := by
    simpa [law, gamma, phi, eta] using
      unconditionalSourcePhysicalRounding_fairTargetEnergy
        G n S D remaining positive
  obtain ⟨L, B', Q, m, horizon, phases, resolution, harmonic,
      UA, UB, _pointwise, _tail, asynchronous, terminal, hazard⟩ :=
    unconditionalSourcePhysicalSameGridWeightedStoppingLedger
      dimension grid w delta width_large delta_positive delta_bounded
      (by simpa [delta] using budget)
      t t_positive t_bounded rho rho_positive
      law (exactLocallySampleableLaw_nonneg G n S D positive)
      (exactLocallySampleableLaw_sum G n S D remaining positive)
      gamma phi eta energy
  refine ⟨w, N, L, B', Q, m, width_large, grid, horizon,
    phases, resolution, harmonic, ?_, ?_, ?_, UA, UB, ?_⟩
  · exact budget
  · exact grid_fine
  · exact scalar
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact canonical
  · exact asynchronous
  · exact terminal
  · change
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        law h *
          dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
            Q m (fun _ : Fin 1 => w) (fun _ : Fin L => 0)
            (gamma h) (phi h) UA UB) ≤
        (34 / t) * (64 * Real.sqrt eta + delta) +
          4 * rho ^ 2 +
            unconditionalPrefactorBucketCoefficient * t
    simpa only [unconditionalPrefactorBucketCoefficient]
      using hazard

theorem unconditionalSourcePhysicalRounding_largeVerifierBound
    (K eta alpha lam epsilon : ℝ)
    (constant : 128 ≤ K)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (lam_nonnegative : 0 ≤ lam)
    (epsilon_nonnegative : 0 ≤ epsilon)
    (large : 1 < 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) :
    roundedWinningLowerBound epsilon K alpha eta lam ≤ 0 := by
  have eta_root_nonnegative : 0 ≤ eta ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg eta_nonnegative _
  have alpha_root_nonnegative : 0 ≤ alpha ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg alpha_positive.le _
  have scaled_nonnegative : 0 ≤ (32 * eta) ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have root_scaled : eta ^ (1 / 12 : ℝ) ≤
      (32 * eta) ^ (1 / 12 : ℝ) := by
    apply Real.rpow_le_rpow eta_nonnegative
    · nlinarith
    · norm_num
  have root_sum_nonnegative :
      0 ≤ eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ) :=
    add_nonneg eta_root_nonnegative alpha_root_nonnegative
  have constant_nonnegative : 0 ≤ K := by linarith
  have universal_nonnegative : 0 ≤ universalErrorCeiling K := by
    unfold universalErrorCeiling
    positivity
  have hazard :=
    unconditionalPrefactor_largeVerifier_twelfthRoot_le
      eta_nonnegative alpha_positive alpha_bounded large
  have quantum :
      2 ≤ K *
        (alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)) := by
    calc
      (2 : ℝ) ≤
          128 * (eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ)) :=
        hazard
      _ ≤ K *
          (alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)) := by
        apply mul_le_mul constant
        · linarith
        · exact root_sum_nonnegative
        · exact constant_nonnegative
  have lam_error : 0 ≤ universalErrorCeiling K * lam :=
    mul_nonneg universal_nonnegative lam_nonnegative
  have sqrt_error : 0 ≤ Real.sqrt (8 * eta) :=
    Real.sqrt_nonneg _
  unfold roundedWinningLowerBound totalSamplingLoss
  nlinarith

theorem unconditionalSourcePhysicalRounding_exists_large
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (K alpha gamma : ℝ)
    (constant : 128 ≤ K)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (gamma_positive : 0 < gamma)
    (large : 1 < 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ)) :
    ∃ rounded : Strategy G,
      roundedWinningLowerBound (1 - entangledValue G)
          K alpha (martingaleRate G n S D)
          (exactSourcePinskerRate G n S D + gamma) ≤
        rounded.winProbability := by
  classical
  obtain ⟨alice, bob⟩ :=
    exactSourceAnswerTypes_nonempty_of_remaining
      G n S D remaining
  let rounded : Strategy G := pdfConstantStrategy G
    (Classical.choice alice) (Classical.choice bob)
  refine ⟨rounded, ?_⟩
  have eta_nonnegative :=
    martingaleRate_nonneg G n S D remaining positive
  have epsilon_nonnegative : 0 ≤ 1 - entangledValue G := by
    linarith [entangledValue_le_one G]
  have pinsker_nonnegative :
      0 ≤ exactSourcePinskerRate G n S D := by
    unfold exactSourcePinskerRate
    positivity
  have source_bound :=
    unconditionalSourcePhysicalRounding_largeVerifierBound
      K (martingaleRate G n S D) alpha
      (exactSourcePinskerRate G n S D + gamma)
      (1 - entangledValue G)
      constant eta_nonnegative alpha_positive alpha_bounded
      (by linarith) epsilon_nonnegative large
  exact source_bound.trans rounded.winProbability_nonneg

theorem unconditionalSourcePhysicalRounding_smallRoundedLower
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha gamma deviation clipping : ℝ)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (gamma_positive : 0 < gamma)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1)
    (actual_deviation :
      deviation ≤
        (34 / Real.sqrt
            (64 * Real.sqrt (martingaleRate G n S D) +
              alpha ^ (1 / 3 : ℝ))) *
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ)))
    (actual_clipping :
      clipping ≤
        16 * martingaleRate G n S D +
          8 * (3 * alpha ^ (1 / 3 : ℝ) / 2))
    (rounded : Strategy G)
    (actual_original_verifier :
      1 - (1 - entangledValue G) / 2 -
          5 * (exactSourcePinskerRate G n S D + gamma) -
        ((64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ) +
            (alpha ^ (1 / 3 : ℝ)) ^ 2) +
          4 * Real.sqrt deviation + 4 * Real.sqrt clipping +
          2 * Real.sqrt (8 * martingaleRate G n S D)) ≤
        rounded.winProbability) :
    roundedWinningLowerBound (1 - entangledValue G)
        unconditionalSourcePhysicalRoundingUniversalConstant
        alpha (martingaleRate G n S D)
        (exactSourcePinskerRate G n S D + gamma) ≤
      rounded.winProbability := by
  apply unconditionalSmallSourcePhysicalRoundedLower
    unconditionalSourcePhysicalRoundingUniversalConstant
    (martingaleRate G n S D) alpha deviation clipping
    (1 - entangledValue G)
    (exactSourcePinskerRate G n S D + gamma)
    rounded.winProbability
  · unfold unconditionalSourcePhysicalRoundingUniversalConstant
    exact le_rfl
  · exact martingaleRate_nonneg G n S D remaining positive
  · exact alpha_positive
  · exact alpha_bounded
  · exact small
  · exact actual_deviation
  · exact actual_clipping
  · have pinsker_nonnegative :
        0 ≤ exactSourcePinskerRate G n S D := by
      unfold exactSourcePinskerRate
      positivity
    linarith
  · exact actual_original_verifier

theorem
    unconditionalSourcePhysicalRounding_smallRoundedLower_of_stoppedVerifier
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha gamma deviation clipping : ℝ)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (gamma_positive : 0 < gamma)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1)
    (actual_deviation :
      deviation ≤
        (34 / Real.sqrt
            (64 * Real.sqrt (martingaleRate G n S D) +
              alpha ^ (1 / 3 : ℝ))) *
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ)))
    (actual_clipping :
      clipping ≤
        16 * martingaleRate G n S D +
          8 * (3 * alpha ^ (1 / 3 : ℝ) / 2))
    (rounded : Strategy G)
    (stopped_verifier :
      1 - (1 - entangledValue G) / 2 -
          5 * (exactSourcePinskerRate G n S D + gamma) -
        ((64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ) +
            (alpha ^ (1 / 3 : ℝ)) ^ 2) +
          4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
        rounded.winProbability) :
    roundedWinningLowerBound (1 - entangledValue G)
        unconditionalSourcePhysicalRoundingUniversalConstant
        alpha (martingaleRate G n S D)
        (exactSourcePinskerRate G n S D + gamma) ≤
      rounded.winProbability := by
  apply unconditionalSourcePhysicalRounding_smallRoundedLower
    G n S D remaining positive alpha gamma deviation clipping
    alpha_positive alpha_bounded gamma_positive small
    actual_deviation actual_clipping rounded
  nlinarith [Real.sqrt_nonneg clipping,
    Real.sqrt_nonneg (8 * martingaleRate G n S D)]

theorem unconditionalSourceOneGameRounding_uniform_of_small
    (small_rounding :
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B)
        (n : ℕ) (S : Strategy (G.repeat n))
        (D : Finset (Fin n)),
        0 < (Finset.univ \ D).card →
        0 < repeatedPostselectionMass G n S D →
        ∀ (alpha gamma : ℝ),
          0 < alpha → alpha ≤ 1 → 0 < gamma →
          64 * Real.sqrt (martingaleRate G n S D) +
              alpha ^ (1 / 3 : ℝ) ≤ 1 →
          uniformRemainingFailure
              (strategyEventLaw (G.repeat n) S)
              (repeatedCoordinateWin G n) D <
            (1 - entangledValue G) / 2 →
          ∃ rounded : Strategy G,
            roundedWinningLowerBound (1 - entangledValue G)
                unconditionalSourcePhysicalRoundingUniversalConstant
                alpha (martingaleRate G n S D)
                (exactSourcePinskerRate G n S D + gamma) ≤
              rounded.winProbability) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B)
        (n : ℕ) (S : Strategy (G.repeat n))
        (D : Finset (Fin n)),
        0 < (Finset.univ \ D).card →
        0 < repeatedPostselectionMass G n S D →
        ∀ (alpha gamma : ℝ),
          0 < alpha → alpha ≤ 1 → 0 < gamma →
          uniformRemainingFailure
              (strategyEventLaw (G.repeat n) S)
              (repeatedCoordinateWin G n) D <
            (1 - entangledValue G) / 2 →
          ∃ rounded : Strategy G,
            roundedWinningLowerBound (1 - entangledValue G)
                K alpha (martingaleRate G n S D)
                (exactSourcePinskerRate G n S D + gamma) ≤
              rounded.winProbability := by
  refine ⟨unconditionalSourcePhysicalRoundingUniversalConstant,
    ?_, ?_⟩
  · linarith [unconditionalSourcePhysicalRoundingUniversalConstant_ge]
  intro X Y A B _ _ _ _ G n S D remaining positive
    alpha gamma alpha_positive alpha_bounded gamma_positive failure
  by_cases small :
      64 * Real.sqrt (martingaleRate G n S D) +
        alpha ^ (1 / 3 : ℝ) ≤ 1
  · exact small_rounding G n S D remaining positive alpha gamma
      alpha_positive alpha_bounded gamma_positive small failure
  · exact unconditionalSourcePhysicalRounding_exists_large
      G n S D remaining positive
      unconditionalSourcePhysicalRoundingUniversalConstant
      alpha gamma
      unconditionalSourcePhysicalRoundingUniversalConstant_ge
      alpha_positive alpha_bounded gamma_positive (lt_of_not_ge small)

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalActualC485GenericRetainedWinningBorn
    {X Y A B s t u v ι κ : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [Fintype u] [Fintype v]
    [Fintype ι] [Fintype κ]
    [DecidableEq s] [DecidableEq t] [DecidableEq u] [DecidableEq v]
    [DecidableEq ι] [DecidableEq κ]
    (G : Game X Y A B)
    (eA : ι ≃ s × t) (eB : κ ≃ u × v)
    (PA : POVM A s) (PB : POVM B u)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ)) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM eA PA)
          (directDSVActualReindexedRetainedPOVM eB PB) x y)) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := (s × u) × (t × v)) (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect
            G PA PB x y ⊗ₖ (1 : Matrix (t × v) (t × v) ℂ)))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv eA eB) z) := by
  rw [directDSVActualReindexedRetainedPOVMWinningEffect,
    directDSVActualReindexedWinningEffect_quadratic]

theorem unconditionalActualC485GenericSelectedWinningRegroupGauge
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ} {ι κ R T : Type}
    [Fintype ι] [Fintype κ] [Fintype R] [Fintype T]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq R] [DecidableEq T]
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (eA : ι ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (eB : κ ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (pair : R × R ≃ T)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ)) :
    let selected := UnconditionalSelectedCopyLocalIndex P d N m
    let stage := physical8SelectedGlobalTargetWorkEquiv P N d m
    let gaugedAlice := directDSVActualReindexedRetainedPOVM stage
      (unitaryConjugatePOVM alice PA)
    let gaugedBob := directDSVActualReindexedRetainedPOVM stage
      (unitaryConjugatePOVM bob PB)
    let plainAlice := directDSVActualReindexedRetainedPOVM stage PA
    let plainBob := directDSVActualReindexedRetainedPOVM stage PB
    let regrouped :=
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr (Equiv.refl (selected × selected)) pair)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv eA eB) z)
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM eA gaugedAlice)
          (directDSVActualReindexedRetainedPOVM eB gaugedBob)
          x y)) z =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (selected × selected) × T) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          plainAlice plainBob x y ⊗ₖ (1 : Matrix T T ℂ)))
      (unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P alice)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P bob)
        regrouped) := by
  dsimp only
  calc
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            (UnconditionalSelectedCopyLocalIndex P d N m ×
             UnconditionalSelectedCopyLocalIndex P d N m) ×
              (R × R))
          (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            (directDSVActualReindexedRetainedPOVM
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (unitaryConjugatePOVM alice PA))
            (directDSVActualReindexedRetainedPOVM
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (unitaryConjugatePOVM bob PB)) x y ⊗ₖ
            (1 : Matrix (R × R) (R × R) ℂ)))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv eA eB) z) :=
      unconditionalActualC485GenericRetainedWinningBorn
        G eA eB
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (unitaryConjugatePOVM alice PA))
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (unitaryConjugatePOVM bob PB)) x y z
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            (UnconditionalSelectedCopyLocalIndex P d N m ×
             UnconditionalSelectedCopyLocalIndex P d N m) × T)
          (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            (directDSVActualReindexedRetainedPOVM
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (unitaryConjugatePOVM alice PA))
            (directDSVActualReindexedRetainedPOVM
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (unitaryConjugatePOVM bob PB)) x y ⊗ₖ
            (1 : Matrix T T ℂ)))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv eA eB) z)) :=
      unconditionalActualC485RetainedPureWorkReindexBorn
        pair
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM alice PA))
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM bob PB)) x y)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv eA eB) z)
    _ = _ :=
      unconditionalActualFairSourceSelectedRetainedWinningBornGauge
        G alice bob PA PB x y
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv eA eB) z))

theorem unconditionalActualC485GenericDecodedWinningBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ} {ι κ R T : Type}
    [Fintype ι] [Fintype κ] [Fintype R] [Fintype T]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq R] [DecidableEq T]
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (eA : ι ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (eB : κ ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (pair : R × R ≃ T)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (actual : EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex P d N m ×
        UnconditionalSelectedCopyLocalIndex P d N m) × T))
    (decoded :
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P alice)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P bob)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv
              eA eB) z)) = actual) :
    let selected := UnconditionalSelectedCopyLocalIndex P d N m
    let stage := physical8SelectedGlobalTargetWorkEquiv P N d m
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (selected × selected) × T) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM stage PA)
          (directDSVActualReindexedRetainedPOVM stage PB)
          x y ⊗ₖ (1 : Matrix T T ℂ))) actual =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            (directDSVActualReindexedRetainedPOVM eA
              (directDSVActualReindexedRetainedPOVM stage
                (unitaryConjugatePOVM alice PA)))
            (directDSVActualReindexedRetainedPOVM eB
              (directDSVActualReindexedRetainedPOVM stage
                (unitaryConjugatePOVM bob PB))) x y)) z := by
  dsimp only
  have physical :=
    unconditionalActualC485GenericSelectedWinningRegroupGauge
      G alice bob PA PB eA eB pair x y z
  dsimp only at physical
  rw [decoded] at physical
  exact physical.symm

theorem unconditionalActualC485SourceSelectedDecodedWinningBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ} {ι κ R T : Type}
    [Fintype ι] [Fintype κ] [Fintype R] [Fintype T]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq R] [DecidableEq T]
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (selectedA :
      POVM A (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedB :
      POVM B (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedA_eq :
      selectedA =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PA)
    (selectedB_eq :
      selectedB =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PB)
    (eA : ι ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (eB : κ ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (pair : R × R ≃ T)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (actual : EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex P d N m ×
        UnconditionalSelectedCopyLocalIndex P d N m) × T))
    (decoded :
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P alice)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P bob)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv
              eA eB) z)) = actual) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          (UnconditionalSelectedCopyLocalIndex P d N m ×
           UnconditionalSelectedCopyLocalIndex P d N m) × T)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          selectedA selectedB x y ⊗ₖ (1 : Matrix T T ℂ))) actual =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            (directDSVActualReindexedRetainedPOVM eA
              (directDSVActualReindexedRetainedPOVM
                (physical8SelectedGlobalTargetWorkEquiv P N d m)
                (unitaryConjugatePOVM alice PA)))
            (directDSVActualReindexedRetainedPOVM eB
              (directDSVActualReindexedRetainedPOVM
                (physical8SelectedGlobalTargetWorkEquiv P N d m)
                (unitaryConjugatePOVM bob PB))) x y)) z := by
  subst selectedA
  subst selectedB
  exact
    unconditionalActualC485GenericDecodedWinningBorn
      G alice bob PA PB eA eB pair x y z actual decoded

theorem unconditionalActualC485CompleteDecodedPhysicalBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ} {ι κ R T : Type}
    [Fintype ι] [Fintype κ] [Fintype R] [Fintype T]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq R] [DecidableEq T]
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (selectedA :
      POVM A (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedB :
      POVM B (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedA_eq :
      selectedA =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PA)
    (selectedB_eq :
      selectedB =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PB)
    (eA : ι ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (eB : κ ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (pair : R × R ≃ T)
    (rawA : POVM A ι) (rawB : POVM B κ)
    (rawA_eq :
      rawA =
        directDSVActualReindexedRetainedPOVM eA
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM alice PA)))
    (rawB_eq :
      rawB =
        directDSVActualReindexedRetainedPOVM eB
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM bob PB)))
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (source cleaned : EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex P d N m ×
        UnconditionalSelectedCopyLocalIndex P d N m) × T))
    (source_eq : source = cleaned)
    (decoded :
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P alice)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P bob)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv
              eA eB) z)) = cleaned) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          (UnconditionalSelectedCopyLocalIndex P d N m ×
           UnconditionalSelectedCopyLocalIndex P d N m) × T)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          selectedA selectedB x y ⊗ₖ (1 : Matrix T T ℂ))) source =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            rawA rawB x y)) z := by
  subst rawA
  subst rawB
  calc
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            (UnconditionalSelectedCopyLocalIndex P d N m ×
             UnconditionalSelectedCopyLocalIndex P d N m) × T)
          (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            selectedA selectedB x y ⊗ₖ (1 : Matrix T T ℂ))) cleaned :=
      congrArg
        (fun v : EuclideanSpace ℂ
            ((UnconditionalSelectedCopyLocalIndex P d N m ×
              UnconditionalSelectedCopyLocalIndex P d N m) × T) =>
          quadraticExpectation
            (Matrix.toEuclideanCLM
              (n :=
                (UnconditionalSelectedCopyLocalIndex P d N m ×
                 UnconditionalSelectedCopyLocalIndex P d N m) × T)
              (𝕜 := ℂ)
              (directDSVActualLocalPOVMWinningEffect G
                selectedA selectedB x y ⊗ₖ (1 : Matrix T T ℂ))) v)
        source_eq
    _ = _ :=
      unconditionalActualC485SourceSelectedDecodedWinningBorn
        G alice bob PA PB selectedA selectedB selectedA_eq selectedB_eq
        eA eB pair x y z cleaned decoded

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

def unconditionalActualFairSourceAliceTarget
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty) :
    ExactSourceSharedFlag X Y A B D denominator → X →
      BipartiteUnitVector
        (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  fun flag x =>
    exactGlobalHistoryFinGamma G n S D
      (exactSourceAlicePermutationHistory
        D denominator numerator nonempty flag x) x

def unconditionalActualFairSourceBobTarget
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty) :
    ExactSourceSharedFlag X Y A B D denominator → Y →
      BipartiteUnitVector
        (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  fun flag y =>
    exactGlobalHistoryFinPhi G n S D
      (exactSourceBobPermutationHistory
        D denominator numerator nonempty flag y) y

def unconditionalActualFairSourceAliceFlagPOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) (P N L m : ℕ) :
    ExactSourceSharedFlag X Y A B D denominator →
      Fin (L + 1) → X →
        POVM A
          (UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N
            (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
            L m) := by
  classical
  intro flag
  exact
    physical8OneScaleOriginalFlagPOVM
      (N := N)
      (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P) a₀
      (fun x =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis
              (unconditionalActualFairSourceAliceTarget
                G n S D denominator numerator nonempty flag x)))
          (integratorActualC485SourceAlicePOVM
            G n S D a₀ x))

def unconditionalActualFairSourceBobFlagPOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (b₀ : B) (P N L m : ℕ) :
    ExactSourceSharedFlag X Y A B D denominator →
      Fin (L + 1) → Y →
        POVM B
          (UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N
            (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
            L m) := by
  classical
  intro flag
  exact
    physical8OneScaleOriginalFlagPOVM
      (N := N)
      (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P) b₀
      (fun y =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis
              (unconditionalActualFairSourceBobTarget
                G n S D denominator numerator nonempty flag y)))
          (integratorActualC485SourceBobPOVM
            G n S D b₀ y))

def unconditionalActualFairSourceAliceStoppingUnitary
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (cleanup : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    ExactSourceSharedFlag X Y A B D denominator → X →
      Matrix.unitaryGroup
        (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N
            (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
            L m) ℂ := by
  classical
  exact
    physical8OneScaleActualAliceStoppingUnitary
      (P := P) (N := N)
      (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
      (L := L) (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      Q width schedule
      (unconditionalActualFairSourceAliceTarget
        G n S D denominator numerator nonempty)
      cleanup

def unconditionalActualFairSourceBobStoppingUnitary
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (cleanup : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    ExactSourceSharedFlag X Y A B D denominator → Y →
      Matrix.unitaryGroup
        (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N
            (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
            L m) ℂ := by
  classical
  exact
    physical8OneScaleActualBobStoppingUnitary
      (P := P) (N := N)
      (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
      (L := L) (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      Q width schedule
      (unconditionalActualFairSourceBobTarget
        G n S D denominator numerator nonempty)
      cleanup

theorem unconditionalActualFairSourceAliceFlagPOVM_succ_nested
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [decA : DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) {P N L m : ℕ}
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (j : Fin L) (x : X) :
    unconditionalActualFairSourceAliceFlagPOVM
        G n S D denominator numerator nonempty a₀ P N L m
        flag j.succ x =
      directDSVActualReindexedRetainedPOVM
        (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
          (N := N)
          (d := Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D))
          (m := m)
          (unconditionalActualOneScaleFixedSourcePhaseSplit P) j)
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv
            P N
            (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D)) m)
          (unitaryConjugatePOVM
            (conjugateUnitary
              (dSVDensityRationalCanonicalAliceBasis
                (unconditionalActualFairSourceAliceTarget
                  G n S D denominator numerator nonempty flag x)))
            (integratorActualC485SourceAlicePOVM
              G n S D a₀ x))) := by
  classical
  have same_instance : decA = Classical.decEq A :=
    Subsingleton.elim _ _
  cases same_instance
  change
    physical8OneScaleOriginalFlagPOVM
      (N := N)
      (d := Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      a₀
      (fun q =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis
              (unconditionalActualFairSourceAliceTarget
                G n S D denominator numerator nonempty flag q)))
          (integratorActualC485SourceAlicePOVM
            G n S D a₀ q)) j.succ x = _
  exact
    unconditionalPhysicalOneScaleOriginalFlagPOVM_succ_nested
      (N := N)
      (d := Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      a₀
      (fun q =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis
              (unconditionalActualFairSourceAliceTarget
                G n S D denominator numerator nonempty flag q)))
          (integratorActualC485SourceAlicePOVM
            G n S D a₀ q)) j x

theorem unconditionalActualFairSourceBobFlagPOVM_succ_nested
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [decB : DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (b₀ : B) {P N L m : ℕ}
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (j : Fin L) (y : Y) :
    unconditionalActualFairSourceBobFlagPOVM
        G n S D denominator numerator nonempty b₀ P N L m
        flag j.succ y =
      directDSVActualReindexedRetainedPOVM
        (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
          (N := N)
          (d := Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D))
          (m := m)
          (unconditionalActualOneScaleFixedSourcePhaseSplit P) j)
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv
            P N
            (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D)) m)
          (unitaryConjugatePOVM
            (conjugateUnitary
              (dSVUniformDensityThresholdLeftBobBasis
                (unconditionalActualFairSourceBobTarget
                  G n S D denominator numerator nonempty flag y)))
            (integratorActualC485SourceBobPOVM
              G n S D b₀ y))) := by
  classical
  have same_instance : decB = Classical.decEq B :=
    Subsingleton.elim _ _
  cases same_instance
  change
    physical8OneScaleOriginalFlagPOVM
      (N := N)
      (d := Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      b₀
      (fun q =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis
              (unconditionalActualFairSourceBobTarget
                G n S D denominator numerator nonempty flag q)))
          (integratorActualC485SourceBobPOVM
            G n S D b₀ q)) j.succ y = _
  exact
    unconditionalPhysicalOneScaleOriginalFlagPOVM_succ_nested
      (N := N)
      (d := Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      b₀
      (fun q =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis
              (unconditionalActualFairSourceBobTarget
                G n S D denominator numerator nonempty flag q)))
          (integratorActualC485SourceBobPOVM
            G n S D b₀ q)) j y

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalActualPairedDecodedMatchedCleanedVector
    {F X Y : Type} {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ : F → X → BipartiteUnitVector d)
    (ζ : F → Y → BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (grid : 0 < N)
    (flag : F) (x : X) (y : Y) (j : Fin L)
    (positive : 0 < width (schedule j)) :
    let phase := unconditionalActualOneScaleFixedSourcePhaseSplit P
    let outer := unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      (N := N) (d := d) (m := m) phase j
    let pair := unconditionalActualC485RetainedHistoryPairEquiv
      (P := P) (N := N) (d := d) j
    let stopped := actualStoppingBranchVector
      (actualStoppingQuestionLocalAction
        (physical8OneScaleActualAliceStoppingUnitary
          (P := P) (N := N) (d := d) (L := L) (m := m)
          phase Q width schedule ξ A flag x)
        (physical8OneScaleActualBobStoppingUnitary
          (P := P) (N := N) (d := d) (L := L) (m := m)
          phase Q width schedule ζ C flag y)
        (unconditionalSourcePhysicalCleanedStoppingFixedSource
          1 P N d L m)) j.succ j.succ
    unconditionalMixedConjugateSelectedBranchLocalAction
      (unconditionalMixedConjugateSigmaAtomLift
        (m := N * m) P
        (conjugateUnitary
          (dSVDensityRationalCanonicalAliceBasis (ξ flag x))))
      (unconditionalMixedConjugateSigmaAtomLift
        (m := N * m) P
        (conjugateUnitary
          (dSVUniformDensityThresholdLeftBobBasis (ζ flag y))))
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr
          (Equiv.refl
            (UnconditionalSelectedCopyLocalIndex P d N m ×
             UnconditionalSelectedCopyLocalIndex P d N m)) pair)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv
            outer outer) stopped)) =
      integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N) (d := d) (L := L) (m := m)
        Q width schedule (ξ flag x) (ζ flag y) A C j := by
  dsimp only
  rw [unconditionalActualC485FullBilateralWorkRegroup]
  exact unconditionalActualOneScaleDecodedMatchedCleanedVector
    Q width schedule ξ ζ A C grid flag x y j positive

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

def unconditionalActualC485SelectedVerifierBorn
    {X Y A B ι T : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T]
    (G : Game X Y A B) (PA : POVM A ι) (PB : POVM B ι)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ ((ι × ι) × T)) : ℝ :=
  quadraticExpectation
    (Matrix.toEuclideanCLM (n := (ι × ι) × T) (𝕜 := ℂ)
      (directDSVActualLocalPOVMWinningEffect G PA PB x y ⊗ₖ
        (1 : Matrix T T ℂ))) z

def unconditionalActualC485RawPhysicalVerifierBorn
    {X Y A B ι κ : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G : Game X Y A B) (PA : POVM A ι) (PB : POVM B κ)
    (x : X) (y : Y) (z : EuclideanSpace ℂ (ι × κ)) : ℝ :=
  quadraticExpectation
    (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
      (directDSVActualLocalPOVMWinningEffect G PA PB x y)) z

theorem unconditionalActualC485CompleteDecodedScalarBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ} {ι κ R T : Type}
    [Fintype ι] [Fintype κ] [Fintype R] [Fintype T]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq R] [DecidableEq T]
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (selectedA :
      POVM A (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedB :
      POVM B (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedA_eq :
      selectedA =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PA)
    (selectedB_eq :
      selectedB =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PB)
    (eA : ι ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (eB : κ ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (pair : R × R ≃ T)
    (rawA : POVM A ι) (rawB : POVM B κ)
    (rawA_eq :
      rawA =
        directDSVActualReindexedRetainedPOVM eA
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM alice PA)))
    (rawB_eq :
      rawB =
        directDSVActualReindexedRetainedPOVM eB
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM bob PB)))
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (source cleaned : EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex P d N m ×
        UnconditionalSelectedCopyLocalIndex P d N m) × T))
    (source_eq : source = cleaned)
    (decoded :
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P alice)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P bob)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv
              eA eB) z)) = cleaned) :
    unconditionalActualC485SelectedVerifierBorn
        G selectedA selectedB x y source =
      unconditionalActualC485RawPhysicalVerifierBorn
        G rawA rawB x y z := by
  exact unconditionalActualC485CompleteDecodedPhysicalBorn
    G alice bob PA PB selectedA selectedB selectedA_eq selectedB_eq
    eA eB pair rawA rawB rawA_eq rawB_eq
    x y z source cleaned source_eq decoded

def unconditionalActualFairSourceHistoryStopBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (h : ExactLocallySampleableTuple X Y A B D)
    (j : Fin L) : ℝ :=
  quadraticExpectation
    (integratorActualC485WinningEffect
      (P := P) (N := N) (L := L) (m := m)
      G n S D a₀ b₀ j h.2.1 h.2.2.1)
    (integratorActualC485CleanedVector
      (S := 1) (B := P) (N := N)
      (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
      (L := L) (m := m)
      Q width schedule
      (unconditionalExactFairGammaUnit G n S D h)
      (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
      UA UB j)

def unconditionalActualFairSourcePhysicalStopBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y) (j : Fin L) : ℝ := by
  let d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
  let PA := unconditionalActualFairSourceAliceFlagPOVM
    G n S D denominator numerator nonempty a₀ P N L m flag
  let PB := unconditionalActualFairSourceBobFlagPOVM
    G n S D denominator numerator nonempty b₀ P N L m flag
  let U := unconditionalActualFairSourceAliceStoppingUnitary
    (P := P) (N := N) (L := L) (m := m)
    G n S D denominator numerator nonempty Q width schedule UA flag x
  let V := unconditionalActualFairSourceBobStoppingUnitary
    (P := P) (N := N) (L := L) (m := m)
    G n S D denominator numerator nonempty Q width schedule UB flag y
  exact
    unconditionalActualC485RawPhysicalVerifierBorn
      G (PA j.succ x) (PB j.succ y) x y
      (actualStoppingBranchVector
        (actualStoppingQuestionLocalAction U V
          (unconditionalSourcePhysicalCleanedStoppingFixedSource
            1 P N d L m)) j.succ j.succ)

theorem unconditionalActualFairSourceHistoryStopBorn_eq_selected
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (h : ExactLocallySampleableTuple X Y A B D)
    (j : Fin L) :
    unconditionalActualFairSourceHistoryStopBorn
        G n S D a₀ b₀ Q width schedule UA UB h j =
      unconditionalActualC485SelectedVerifierBorn G
        (integratorActualC485SelectedAlicePOVM
          G n S D a₀ P N m h.2.1)
        (integratorActualC485SelectedBobPOVM
          G n S D b₀ P N m h.2.2.1)
        h.2.1 h.2.2.1
        (integratorActualC485CleanedVector
          (S := 1) (B := P) (N := N)
          (d := Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D))
          (L := L) (m := m)
          Q width schedule
          (unconditionalExactFairGammaUnit G n S D h)
          (exactGlobalHistoryFinPhi
            G n S D h.2.2.2 h.2.2.1)
          UA UB j) := by
  classical
  rfl

theorem unconditionalActualFairSourcePhysicalStopBorn_eq_raw
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y) (j : Fin L) :
    let d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
    let PA := unconditionalActualFairSourceAliceFlagPOVM
      G n S D denominator numerator nonempty a₀ P N L m flag
    let PB := unconditionalActualFairSourceBobFlagPOVM
      G n S D denominator numerator nonempty b₀ P N L m flag
    let stopped := actualStoppingBranchVector
      (actualStoppingQuestionLocalAction
        (unconditionalActualFairSourceAliceStoppingUnitary
          (P := P) (N := N) (L := L) (m := m)
          G n S D denominator numerator nonempty
          Q width schedule UA flag x)
        (unconditionalActualFairSourceBobStoppingUnitary
          (P := P) (N := N) (L := L) (m := m)
          G n S D denominator numerator nonempty
          Q width schedule UB flag y)
        (unconditionalSourcePhysicalCleanedStoppingFixedSource
          1 P N d L m)) j.succ j.succ
    unconditionalActualFairSourcePhysicalStopBorn
        G n S D denominator numerator nonempty a₀ b₀
        Q width schedule UA UB flag x y j =
      unconditionalActualC485RawPhysicalVerifierBorn
        G (PA j.succ x) (PB j.succ y) x y stopped := by
  classical
  dsimp only
  rfl

theorem unconditionalActualFairSourceMatchedHistoryGamma
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y) :
    unconditionalExactFairGammaUnit G n S D
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))) =
      unconditionalActualFairSourceAliceTarget
        G n S D denominator numerator nonempty flag x := by
  rw [unconditionalExactFairGammaUnit_eq_global]
  exact
    (unconditionalFairMatchedFlag_aliceTarget_eq_aliceSample
      G n S D denominator numerator nonempty flag x y).symm

theorem unconditionalActualFairSourceMatchedHistoryPhi
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matching :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true) :
    exactGlobalHistoryFinPhi G n S D
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))).2.2.2 y =
      unconditionalActualFairSourceBobTarget
        G n S D denominator numerator nonempty flag y := by
  exact
    (unconditionalFairMatchedFlag_bobTarget_eq_aliceSample
      G n S D denominator numerator nonempty flag x y matching).symm

theorem unconditionalActualFairSourceMatchedHistoryCleanedVector
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matching :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true)
    (j : Fin L) :
    let h := exactSourceAliceSampleTuple
      D denominator numerator nonempty (flag, (x, y))
    integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N)
        (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        (L := L) (m := m)
        Q width schedule
        (unconditionalExactFairGammaUnit G n S D h)
        (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
        UA UB j =
      integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N)
        (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        (L := L) (m := m)
        Q width schedule
        (unconditionalActualFairSourceAliceTarget
          G n S D denominator numerator nonempty flag x)
        (unconditionalActualFairSourceBobTarget
          G n S D denominator numerator nonempty flag y)
        UA UB j := by
  dsimp only
  exact congrArg₂
    (fun (u v : BipartiteUnitVector
        (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))) =>
      integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N)
        (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        (L := L) (m := m)
        Q width schedule u v UA UB j)
    (unconditionalActualFairSourceMatchedHistoryGamma
      G n S D denominator numerator nonempty flag x y)
    (unconditionalActualFairSourceMatchedHistoryPhi
      G n S D denominator numerator nonempty flag x y matching)

theorem unconditionalActualFairSourcePhysicalStopBornWitness
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (grid : 0 < N)
    (width_positive : ∀ s : Fin 1, 0 < width s)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matching :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true)
    (j : Fin L) :
    unconditionalActualFairSourceHistoryStopBorn
        G n S D a₀ b₀ Q width schedule UA UB
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))) j =
      unconditionalActualFairSourcePhysicalStopBorn
        G n S D denominator numerator nonempty a₀ b₀
        Q width schedule UA UB flag x y j := by
  classical
  let d : ℕ :=
    Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
  let h := exactSourceAliceSampleTuple
    D denominator numerator nonempty (flag, (x, y))
  let targetA := unconditionalActualFairSourceAliceTarget
    G n S D denominator numerator nonempty
  let targetB := unconditionalActualFairSourceBobTarget
    G n S D denominator numerator nonempty
  let phase := unconditionalActualOneScaleFixedSourcePhaseSplit P
  let sourceA := integratorActualC485SourceAlicePOVM
    G n S D a₀ x
  let sourceB := integratorActualC485SourceBobPOVM
    G n S D b₀ y
  let atomA : Matrix.unitaryGroup (Fin d) ℂ :=
    conjugateUnitary
      (dSVDensityRationalCanonicalAliceBasis (targetA flag x))
  let atomB : Matrix.unitaryGroup (Fin d) ℂ :=
    conjugateUnitary
      (dSVUniformDensityThresholdLeftBobBasis (targetB flag y))
  let outer := unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
    (N := N) (d := d) (m := m) phase j
  let pair := unconditionalActualC485RetainedHistoryPairEquiv
    (P := P) (N := N) (d := d) j
  let selectedA := integratorActualC485SelectedAlicePOVM
    G n S D a₀ P N m x
  let selectedB := integratorActualC485SelectedBobPOVM
    G n S D b₀ P N m y
  have selectedA_eq : selectedA =
      directDSVActualReindexedRetainedPOVM
        (physical8SelectedGlobalTargetWorkEquiv P N d m)
        sourceA := by
    rfl
  have selectedB_eq : selectedB =
      directDSVActualReindexedRetainedPOVM
        (physical8SelectedGlobalTargetWorkEquiv P N d m)
        sourceB := by
    rfl
  let rawA := unconditionalActualFairSourceAliceFlagPOVM
    G n S D denominator numerator nonempty a₀ P N L m flag j.succ x
  let rawB := unconditionalActualFairSourceBobFlagPOVM
    G n S D denominator numerator nonempty b₀ P N L m flag j.succ y
  have rawA_eq : rawA =
      directDSVActualReindexedRetainedPOVM outer
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (unitaryConjugatePOVM atomA sourceA)) := by
    simpa only [rawA, outer, phase, atomA, sourceA, targetA, d] using
      (unconditionalActualFairSourceAliceFlagPOVM_succ_nested
        G n S D denominator numerator nonempty a₀
        (P := P) (N := N) (L := L) (m := m) flag j x)
  have rawB_eq : rawB =
      directDSVActualReindexedRetainedPOVM outer
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (unitaryConjugatePOVM atomB sourceB)) := by
    simpa only [rawB, outer, phase, atomB, sourceB, targetB, d] using
      (unconditionalActualFairSourceBobFlagPOVM_succ_nested
        G n S D denominator numerator nonempty b₀
        (P := P) (N := N) (L := L) (m := m) flag j y)
  let source := integratorActualC485CleanedVector
    (S := 1) (B := P) (N := N) (d := d) (L := L) (m := m)
    Q width schedule
    (unconditionalExactFairGammaUnit G n S D h)
    (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
    UA UB j
  let cleaned := integratorActualC485CleanedVector
    (S := 1) (B := P) (N := N) (d := d) (L := L) (m := m)
    Q width schedule (targetA flag x) (targetB flag y) UA UB j
  have source_eq : source = cleaned := by
    exact unconditionalActualFairSourceMatchedHistoryCleanedVector
      G n S D denominator numerator nonempty
      Q width schedule UA UB flag x y matching j
  let stopped := actualStoppingBranchVector
    (actualStoppingQuestionLocalAction
      (unconditionalActualFairSourceAliceStoppingUnitary
        (P := P) (N := N) (L := L) (m := m)
        G n S D denominator numerator nonempty
        Q width schedule UA flag x)
      (unconditionalActualFairSourceBobStoppingUnitary
        (P := P) (N := N) (L := L) (m := m)
        G n S D denominator numerator nonempty
        Q width schedule UB flag y)
      (unconditionalSourcePhysicalCleanedStoppingFixedSource
        1 P N d L m)) j.succ j.succ
  have decoded :
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P atomA)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P atomB)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv
              outer outer) stopped)) = cleaned := by
    simpa only [phase, stopped, cleaned, atomA, atomB, targetA,
      targetB, unconditionalActualFairSourceAliceStoppingUnitary,
      unconditionalActualFairSourceBobStoppingUnitary] using
      (unconditionalActualPairedDecodedMatchedCleanedVector
        Q width schedule
        (unconditionalActualFairSourceAliceTarget
          G n S D denominator numerator nonempty)
        (unconditionalActualFairSourceBobTarget
          G n S D denominator numerator nonempty)
        UA UB grid flag x y j (width_positive (schedule j)))
  have source_born :
      unconditionalActualFairSourceHistoryStopBorn
          G n S D a₀ b₀ Q width schedule UA UB h j =
        unconditionalActualC485SelectedVerifierBorn
          G selectedA selectedB x y source := by
    exact unconditionalActualFairSourceHistoryStopBorn_eq_selected
      G n S D a₀ b₀ Q width schedule UA UB h j
  have raw_born :
      unconditionalActualFairSourcePhysicalStopBorn
          G n S D denominator numerator nonempty a₀ b₀
          Q width schedule UA UB flag x y j =
        unconditionalActualC485RawPhysicalVerifierBorn
          G rawA rawB x y stopped := by
    exact unconditionalActualFairSourcePhysicalStopBorn_eq_raw
      G n S D denominator numerator nonempty a₀ b₀
      Q width schedule UA UB flag x y j
  calc
    unconditionalActualFairSourceHistoryStopBorn
        G n S D a₀ b₀ Q width schedule UA UB h j =
      unconditionalActualC485SelectedVerifierBorn
        G selectedA selectedB x y source := source_born
    _ = unconditionalActualC485RawPhysicalVerifierBorn
        G rawA rawB x y stopped :=
      unconditionalActualC485CompleteDecodedScalarBorn
        G atomA atomB sourceA sourceB selectedA selectedB
        selectedA_eq selectedB_eq outer outer pair rawA rawB
        rawA_eq rawB_eq x y stopped source cleaned source_eq decoded
    _ = unconditionalActualFairSourcePhysicalStopBorn
        G n S D denominator numerator nonempty a₀ b₀
        Q width schedule UA UB flag x y j := raw_born.symm

theorem unconditionalActualFairSourcePhysicalBranchWitness
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (grid : 0 < N)
    (width_positive : ∀ s : Fin 1, 0 < width s)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matching :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true) :
    (∑ j : Fin L,
      unconditionalActualFairSourceHistoryStopBorn
        G n S D a₀ b₀ Q width schedule UA UB
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))) j) =
      ∑ j : Fin L,
        unconditionalActualFairSourcePhysicalStopBorn
          G n S D denominator numerator nonempty a₀ b₀
          Q width schedule UA UB flag x y j := by
  apply Finset.sum_congr rfl
  intro j _
  exact unconditionalActualFairSourcePhysicalStopBornWitness
    G n S D denominator numerator nonempty a₀ b₀
    Q width schedule UA UB grid width_positive flag x y matching j

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

structure UnconditionalActualFairSourceSamplerData
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (gamma : ℝ) where
  base : ExactHistoryFlag X Y A B D
  denominator : ℕ
  denominator_positive : 0 < denominator
  numerator : ExactLocalSamplerIndex X Y D →
    ExactHistoryFlag X Y A B D → ℕ
  rational_normalized :
    ∀ index, (∑ history, numerator index history) = denominator
  support_preserving :
    ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history
  nonempty : ∀ index,
    (rationalMarked denominator (numerator index)).Nonempty
  total_variation :
    QuantumParallelRepetition.Pinsker.finiteTotalVariation
        (flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator))
        (exactSourceAliceFlagCoupling
          G n S D denominator numerator nonempty) ≤
      exactSourcePinskerRate G n S D + gamma
  mismatch :
    (∑ outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator) outcome *
        if exactSourcePermutationMatched
          D denominator numerator nonempty outcome
        then 0 else 1) ≤
      4 * (exactSourcePinskerRate G n S D + gamma)

theorem unconditionalActualFairSourceSamplerData_of_positive
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (gamma : ℝ) (gamma_positive : 0 < gamma) :
    Nonempty (UnconditionalActualFairSourceSamplerData
      G n S D gamma) := by
  obtain ⟨base, denominator, denominator_positive, numerator,
      rational_normalized, support_preserving, nonempty,
      total_variation, mismatch⟩ :=
    unconditionalSourcePhysicalRounding_exists_sourceSampler
      G n S D remaining positive gamma gamma_positive
  exact ⟨⟨base, denominator, denominator_positive, numerator,
    rational_normalized, support_preserving, nonempty,
    total_variation, mismatch⟩⟩

structure UnconditionalActualFairSourceStoppingHazardData
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (alpha : ℝ) where
  w : ℝ
  N : ℕ
  L : ℕ
  P : ℕ
  Q : ℕ
  m : ℕ
  width_large : 1 ≤ w
  grid : 0 < N
  phases : 0 < P
  harmonic : 0 < m
  fine :
    (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) : ℝ) /
        (N : ℝ) < 1 / (w + 1)
  scalar :
    1 / w +
      (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) : ℝ) *
        w / (N : ℝ) ≤ 3 * alpha ^ (1 / 3 : ℝ) / 2
  UA : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ
  UB : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ
  asynchronous :
    (∑ h : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D h *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N (fun _ : Fin 1 => w) (fun _ : Fin L => 0)
          (exactGlobalHistoryFinGamma
            G n S D h.2.2.2 h.2.1)
          (exactGlobalHistoryFinPhi
            G n S D h.2.2.2 h.2.2.1)) ≤
      64 * Real.sqrt (martingaleRate G n S D) +
        alpha ^ (1 / 3 : ℝ)
  terminal :
    (∑ h : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D h *
        dSVDensityRationalHeterogeneousPhysicalTerminalMass
          N (fun _ : Fin 1 => w) (fun _ : Fin L => 0)
          (exactGlobalHistoryFinGamma
            G n S D h.2.2.2 h.2.1)
          (exactGlobalHistoryFinPhi
            G n S D h.2.2.2 h.2.2.1)) ≤
      (alpha ^ (1 / 3 : ℝ)) ^ 2
  hazard :
    (∑ h : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D h *
        dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
          Q m (fun _ : Fin 1 => w) (fun _ : Fin L => 0)
          (exactGlobalHistoryFinGamma
            G n S D h.2.2.2 h.2.1)
          (exactGlobalHistoryFinPhi
            G n S D h.2.2.2 h.2.2.1)
          UA UB) ≤
      (34 / Real.sqrt
          (64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ))) *
          (64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ)) +
        4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ))

theorem unconditionalActualFairSourceStoppingHazardData_of_positive
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha : ℝ) (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1) :
    Nonempty (UnconditionalActualFairSourceStoppingHazardData
      G n S D alpha) := by
  obtain ⟨w, N, L, P, Q, m, width_large, grid, horizon, phases,
      resolution, harmonic, precision, fine, scalar,
      UA, UB, canonical, asynchronous, terminal, hazard⟩ :=
    unconditionalSourcePhysicalRounding_exists_fairStoppingHazard
      G n S D remaining positive alpha alpha_positive alpha_bounded small
  refine ⟨{
    w := w
    N := N
    L := L
    P := P
    Q := Q
    m := m
    width_large := width_large
    grid := grid
    phases := phases
    harmonic := harmonic
    fine := fine
    scalar := scalar
    UA := UA
    UB := UB
    asynchronous := ?_
    terminal := ?_
    hazard := ?_
  }⟩
  · simpa only using asynchronous
  · simpa only using terminal
  · simpa only using hazard

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

structure UnconditionalActualFairCachedStoppedAnalyticLedger
    {I K : Type} [Fintype I] [Fintype K]
    {H : I × K → Type}
    [∀ p, NormedAddCommGroup (H p)]
    [∀ p, InnerProductSpace ℂ (H p)]
    (law : I → ℝ)
    (actual canonical source : (p : I × K) → H p)
    (deviation clipping bad : ℝ) : Prop where
  actual_mass :
    (∑ h : I, law h * ∑ j : K, ‖actual (h, j)‖ ^ 2) ≤ 1
  canonical_mass :
    (∑ h : I, law h * ∑ j : K, ‖canonical (h, j)‖ ^ 2) ≤ 1
  canonical_row_mass : ∀ h : I,
    (∑ j : K, ‖canonical (h, j)‖ ^ 2) ≤ 1
  same_work_mass : ∀ (h : I) (j : K),
    ‖source (h, j)‖ = ‖canonical (h, j)‖
  clean_deviation :
    (∑ h : I, law h *
      ∑ j : K, ‖actual (h, j) - canonical (h, j)‖ ^ 2) ≤ deviation
  clip_deviation :
    (∑ h : I, law h *
      ∑ j : K, ‖canonical (h, j) - source (h, j)‖ ^ 2) ≤ clipping
  actual_success :
    1 - bad ≤ ∑ h : I, law h * ∑ j : K, ‖actual (h, j)‖ ^ 2

structure UnconditionalActualFairCachedSourceVerifierLedger
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    {K : Type} [Fintype K]
    {H : ExactLocallySampleableTuple X Y A B D × K → Type}
    [∀ p, NormedAddCommGroup (H p)]
    [∀ p, InnerProductSpace ℂ (H p)]
    (effect : (p : ExactLocallySampleableTuple X Y A B D × K) →
      (H p →L[ℂ] H p))
    (actual source :
      (p : ExactLocallySampleableTuple X Y A B D × K) → H p) :
    Prop where
  contraction : ∀ p, ‖effect p‖ ≤ 1
  supported_born :
    ∀ h : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D h ≠ 0 →
        ∀ j : K,
          quadraticExpectation (effect (h, j)) (source (h, j)) =
            ‖source (h, j)‖ ^ 2 *
              exactSourceConditionalWinningProbability G n S D h
  history_born_nonnegative :
    ∀ h : ExactLocallySampleableTuple X Y A B D,
      0 ≤ ∑ j : K,
        quadraticExpectation (effect (h, j)) (actual (h, j))
  history_born_bounded :
    ∀ h : ExactLocallySampleableTuple X Y A B D,
      (∑ j : K,
        quadraticExpectation (effect (h, j)) (actual (h, j))) ≤ 1

theorem unconditionalActualFairCachedLedgerStoppingTransfer
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (rational_normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (support_preserving : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    {L : ℕ} {ι : Fin (L + 1) → Type}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (PA : ExactSourceSharedFlag X Y A B D denominator →
      (r : Fin (L + 1)) → X → POVM A (ι r))
    (PB : ExactSourceSharedFlag X Y A B D denominator →
      (r : Fin (L + 1)) → Y → POVM B (ι r))
    (U : ExactSourceSharedFlag X Y A B D denominator →
      X → Matrix.unitaryGroup (Σ r : Fin (L + 1), ι r) ℂ)
    (V : ExactSourceSharedFlag X Y A B D denominator →
      Y → Matrix.unitaryGroup (Σ r : Fin (L + 1), ι r) ℂ)
    (z : ExactSourceSharedFlag X Y A B D denominator →
      EuclideanSpace ℂ
        ((Σ r : Fin (L + 1), ι r) ×
          (Σ r : Fin (L + 1), ι r)))
    (z_normalized : ∀ flag, ‖z flag‖ = 1)
    (matched :
      ExactSourceSharedFlag X Y A B D denominator ×
        (X × Y) → Bool)
    {K : Type} [Fintype K]
    {H : ExactLocallySampleableTuple X Y A B D × K → Type}
    [∀ p, NormedAddCommGroup (H p)]
    [∀ p, InnerProductSpace ℂ (H p)]
    (effect : (p : ExactLocallySampleableTuple X Y A B D × K) →
      (H p →L[ℂ] H p))
    (actual canonical source :
      (p : ExactLocallySampleableTuple X Y A B D × K) → H p)
    (epsilon lam deviation clipping bad : ℝ)
    (analytic :
      UnconditionalActualFairCachedStoppedAnalyticLedger
        (exactLocallySampleableLaw G n S D)
        actual canonical source deviation clipping bad)
    (verifier :
      UnconditionalActualFairCachedSourceVerifierLedger
        G n S D effect actual source)
    (source_failure :
      uniformRemainingFailure
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D < epsilon / 2)
    (total_variation :
      QuantumParallelRepetition.Pinsker.finiteTotalVariation
        (flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator))
        (exactSourceAliceFlagCoupling
          G n S D denominator numerator nonempty) ≤ lam)
    (mismatch :
      (∑ outcome :
        ExactSourceSharedFlag X Y A B D denominator × (X × Y),
        flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator) outcome *
          if matched outcome then 0 else 1) ≤ 4 * lam)
    (matched_physical_branch :
      ∀ (flag : ExactSourceSharedFlag X Y A B D denominator)
        (x : X) (y : Y),
        matched (flag, (x, y)) = true →
          (∑ k : K,
            quadraticExpectation
              (effect
                (exactSourceAliceSampleTuple
                  D denominator numerator nonempty (flag, (x, y)), k))
              (actual
                (exactSourceAliceSampleTuple
                  D denominator numerator nonempty (flag, (x, y)), k))) ≤
            ∑ j : Fin L,
              quadraticExpectation
                (Matrix.toEuclideanCLM
                  (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
                  (actualStoppingBranchWinningEffect
                    G (PA flag) (PB flag) j.succ j.succ x y))
                (actualStoppingBranchVector
                  (actualStoppingQuestionLocalAction
                    (U flag x) (V flag y) (z flag))
                  j.succ j.succ)) :
    1 - epsilon / 2 - 5 * lam -
        (bad + 4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
      (pureFlaggedStrategy G
        (exactSourceSharedFlagWeight D denominator)
        (exactSourceSharedFlagWeight_nonneg D denominator)
        (exactSourceSharedFlagWeight_sum D remaining denominator)
        z z_normalized
        (fun flag x => unitaryConjugatePOVM
          (U flag x)
          (dependentBlockPOVM
            (fun r => PA flag r x)))
        (fun flag y => unitaryConjugatePOVM
          (V flag y)
          (dependentBlockPOVM
            (fun r => PB flag r y)))).winProbability := by
  exact unconditionalFairPhysicalFlaggedStoppingTransfer
    G n S D remaining positive base denominator denominator_positive
    numerator rational_normalized support_preserving nonempty
    PA PB U V z z_normalized matched
    effect verifier.contraction actual canonical source
    analytic.actual_mass analytic.canonical_mass analytic.canonical_row_mass
    analytic.same_work_mass verifier.supported_born
    epsilon lam deviation clipping bad
    analytic.clean_deviation analytic.clip_deviation analytic.actual_success
    verifier.history_born_nonnegative verifier.history_born_bounded
    source_failure total_variation mismatch matched_physical_branch

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

structure UnconditionalActualFairSourceRoundingContext
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (alpha gamma : ℝ) where
  remaining : 0 < (Finset.univ \ D).card
  positive : 0 < repeatedPostselectionMass G n S D
  failure :
    uniformRemainingFailure
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) D <
        (1 - entangledValue G) / 2
  sampler :
    UnconditionalActualFairSourceSamplerData G n S D gamma
  stopping :
    UnconditionalActualFairSourceStoppingHazardData G n S D alpha

def unconditionalActualFairSourceRoundingContext_of_positive
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha gamma : ℝ)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (gamma_positive : 0 < gamma)
    (small :
      64 * Real.sqrt (martingaleRate G n S D) +
        alpha ^ (1 / 3 : ℝ) ≤ 1)
    (failure :
      uniformRemainingFailure
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D <
          (1 - entangledValue G) / 2) :
    UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma := by
  classical
  exact {
    remaining := remaining
    positive := positive
    failure := failure
    sampler := Classical.choice
      (unconditionalActualFairSourceSamplerData_of_positive
        G n S D remaining positive gamma gamma_positive)
    stopping := Classical.choice
      (unconditionalActualFairSourceStoppingHazardData_of_positive
        G n S D remaining positive alpha alpha_positive alpha_bounded small)
  }

namespace UnconditionalActualFairSourceRoundingContext

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
variable {D : Finset (Fin n)} {alpha gamma : ℝ}

def d (_c : UnconditionalActualFairSourceRoundingContext
    G n S D alpha gamma) : ℕ :=
  Fintype.card (ExactGlobalHistoryLocalIndex G n S D)

theorem dimension_pos
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : 0 < d c :=
  exactGlobalHistoryLocalIndex_card_pos G n S D

def width
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Fin 1 → ℝ :=
  fun _ => c.stopping.w

def schedule
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Fin c.stopping.L → Fin 1 :=
  fun _ => 0

theorem width_positive
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : 0 < c.stopping.w := by
  linarith [c.stopping.width_large]

theorem width_all
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : ∀ s : Fin 1, 0 < width c s := by
  intro s
  exact width_positive c

theorem fine_all
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    ∀ s : Fin 1,
      (d c : ℝ) / (c.stopping.N : ℝ) < 1 / (width c s + 1) := by
  intro s
  exact c.stopping.fine

abbrev sourceIndex
    (_c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Type :=
  ExactLocallySampleableTuple X Y A B D

def law
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : sourceIndex c → ℝ :=
  exactLocallySampleableLaw G n S D

def gammaVector
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    sourceIndex c → BipartiteUnitVector (d c) :=
  fun h => unconditionalExactFairGammaUnit G n S D h

def phiVector
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    sourceIndex c → BipartiteUnitVector (d c) :=
  fun h => exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1

def psiVector
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    sourceIndex c → EuclideanSpace ℂ (Fin (d c) × Fin (d c)) :=
  fun h => exactSourceTuplePsi G n S D h

abbrev branchSpace
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (p : sourceIndex c × Fin c.stopping.L) : Type :=
  IntegratorActualC485BranchSpace
    1 c.stopping.P c.stopping.N (d c)
    c.stopping.L c.stopping.m p.2

def actual
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (p : sourceIndex c × Fin c.stopping.L) : branchSpace c p :=
  integratorActualC485CleanedVector
    (S := 1) (B := c.stopping.P) (N := c.stopping.N)
    (d := d c) (L := c.stopping.L) (m := c.stopping.m)
    c.stopping.Q (width c) (schedule c)
    (gammaVector c p.1) (phiVector c p.1)
    c.stopping.UA c.stopping.UB p.2

def canonical
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (p : sourceIndex c × Fin c.stopping.L) : branchSpace c p :=
  integratorActualC485CanonicalVector
    (S := 1) (B := c.stopping.P) (N := c.stopping.N)
    (d := d c) (L := c.stopping.L) (m := c.stopping.m)
    (width := width c) (schedule c)
    (gammaVector c p.1) (phiVector c p.1) p.2
    (width_all c (schedule c p.2)) c.stopping.grid
    (fine_all c (schedule c p.2))

def source
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (p : sourceIndex c × Fin c.stopping.L) : branchSpace c p :=
  integratorActualC485SourceVector
    (S := 1) (B := c.stopping.P) (N := c.stopping.N)
    (d := d c) (L := c.stopping.L) (m := c.stopping.m)
    (width c) (schedule c)
    (gammaVector c p.1) (phiVector c p.1) (psiVector c p.1) p.2

theorem answerNonempty
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Nonempty A ∧ Nonempty B :=
  exactSourceAnswerTypes_nonempty_of_remaining
    G n S D c.remaining

def aliceDefault
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : A :=
  Classical.choice (answerNonempty c).1

def bobDefault
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : B :=
  Classical.choice (answerNonempty c).2

def effect
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (p : sourceIndex c × Fin c.stopping.L) :
    branchSpace c p →L[ℂ] branchSpace c p :=
  integratorActualC485WinningEffect
    (P := c.stopping.P) (N := c.stopping.N) (m := c.stopping.m)
    G n S D (aliceDefault c) (bobDefault c)
    p.2 p.1.2.1 p.1.2.2.1

def deviation
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : ℝ :=
  ∑ h : sourceIndex c, law c h *
    ∑ j : Fin c.stopping.L,
      ‖actual c (h, j) - canonical c (h, j)‖ ^ 2

def clipping
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : ℝ :=
  unconditionalActualC485FairSourceClipEnergy
    (P := c.stopping.P) (m := c.stopping.m)
    G n S D (width_positive c) c.stopping.grid c.stopping.fine
    (schedule c)

def bad
    (_c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : ℝ :=
  64 * Real.sqrt (martingaleRate G n S D) +
    alpha ^ (1 / 3 : ℝ) + (alpha ^ (1 / 3 : ℝ)) ^ 2

abbrev flag
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Type :=
  ExactSourceSharedFlag X Y A B D c.sampler.denominator

abbrev fiber
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Type :=
  UnconditionalSourcePhysicalStoppingPhaseFiber
    1 c.stopping.P c.stopping.N (d c)
    c.stopping.L c.stopping.m

def PA
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    flag c → Fin (c.stopping.L + 1) → X → POVM A (fiber c) := by
  classical
  exact unconditionalActualFairSourceAliceFlagPOVM
    G n S D c.sampler.denominator c.sampler.numerator
    c.sampler.nonempty (aliceDefault c)
    c.stopping.P c.stopping.N c.stopping.L c.stopping.m

def PB
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    flag c → Fin (c.stopping.L + 1) → Y → POVM B (fiber c) := by
  classical
  exact unconditionalActualFairSourceBobFlagPOVM
    G n S D c.sampler.denominator c.sampler.numerator
    c.sampler.nonempty (bobDefault c)
    c.stopping.P c.stopping.N c.stopping.L c.stopping.m

def U
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    flag c → X →
      Matrix.unitaryGroup
        (Σ _ : Fin (c.stopping.L + 1), fiber c) ℂ :=
  unconditionalActualFairSourceAliceStoppingUnitary
    G n S D c.sampler.denominator c.sampler.numerator
    c.sampler.nonempty c.stopping.Q
    (width c) (schedule c) c.stopping.UA

def V
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    flag c → Y →
      Matrix.unitaryGroup
        (Σ _ : Fin (c.stopping.L + 1), fiber c) ℂ :=
  unconditionalActualFairSourceBobStoppingUnitary
    G n S D c.sampler.denominator c.sampler.numerator
    c.sampler.nonempty c.stopping.Q
    (width c) (schedule c) c.stopping.UB

def prepared
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    flag c → EuclideanSpace ℂ
      ((Σ _ : Fin (c.stopping.L + 1), fiber c) ×
       (Σ _ : Fin (c.stopping.L + 1), fiber c)) :=
  fun _ => unconditionalSourcePhysicalCleanedStoppingFixedSource
    1 c.stopping.P c.stopping.N (d c)
    c.stopping.L c.stopping.m

theorem prepared_normalized
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    ∀ f : flag c, ‖prepared c f‖ = 1 := by
  intro f
  exact unconditionalSourcePhysicalCleanedStoppingFixedSource_norm
    c.stopping.phases c.stopping.grid (dimension_pos c)
    c.stopping.harmonic

def rounded
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : Strategy G :=
  unconditionalOneScaleActualSourceFlaggedStrategy
    G n S D c.remaining
    c.sampler.denominator c.sampler.numerator c.sampler.nonempty
    c.stopping.w c.stopping.N c.stopping.L c.stopping.P
    c.stopping.Q c.stopping.m c.stopping.phases c.stopping.grid
    c.stopping.harmonic c.stopping.UA c.stopping.UB

end UnconditionalActualFairSourceRoundingContext

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling
open UnconditionalActualFairSourceRoundingContext

attribute [local instance] Classical.propDecidable

theorem unconditionalActualFairSourceRoundingContext_actualRow
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (h : ExactLocallySampleableTuple X Y A B D) :
    (∑ j : Fin c.stopping.L, ‖actual c (h, j)‖ ^ 2) ≤ 1 := by
  exact unconditionalActualFairCleanedRow_le_one
    c.stopping.phases c.stopping.grid (dimension_pos c)
    c.stopping.harmonic (width c) (width_all c) (schedule c)
    (gammaVector c h) (phiVector c h)
    c.stopping.Q c.stopping.UA c.stopping.UB

theorem unconditionalActualFairSourceRoundingContext_clippingBound
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    clipping c ≤
      16 * martingaleRate G n S D +
        8 * (3 * alpha ^ (1 / 3 : ℝ) / 2) := by
  exact unconditionalActualC485FairSourceClipEnergy_le_budget
    (P := c.stopping.P) (m := c.stopping.m)
    G n S D c.remaining c.positive
    (width_positive c) c.stopping.grid (dimension_pos c)
    c.stopping.fine c.stopping.phases c.stopping.harmonic
    (schedule c) c.stopping.scalar

theorem unconditionalActualFairSourceRoundingContext_cleanBound
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    deviation c ≤
      (34 / Real.sqrt
          (64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ))) *
        (64 * Real.sqrt (martingaleRate G n S D) +
          alpha ^ (1 / 3 : ℝ)) +
        4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ)) := by
  have identification :=
    unconditionalActualC485WeightedCleanDeviation_eq_hazard
      (law c) c.stopping.Q (width c) (schedule c)
      (gammaVector c) (phiVector c)
      c.stopping.UA c.stopping.UB
      (width_all c) c.stopping.phases c.stopping.grid
      (dimension_pos c) (fine_all c)
  have fair_hazard :
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        law c h *
          dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
            c.stopping.Q c.stopping.m (width c) (schedule c)
            (gammaVector c h) (phiVector c h)
            c.stopping.UA c.stopping.UB) ≤
        (34 / Real.sqrt
            (64 * Real.sqrt (martingaleRate G n S D) +
              alpha ^ (1 / 3 : ℝ))) *
          (64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
            unconditionalPrefactorBucketCoefficient *
              Real.sqrt
                (64 * Real.sqrt (martingaleRate G n S D) +
                  alpha ^ (1 / 3 : ℝ)) := by
    change
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D h *
          dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
            c.stopping.Q c.stopping.m
            (fun _ : Fin 1 => c.stopping.w)
            (fun _ : Fin c.stopping.L => 0)
            (unconditionalExactFairGammaUnit G n S D h)
            (exactGlobalHistoryFinPhi
              G n S D h.2.2.2 h.2.2.1)
            c.stopping.UA c.stopping.UB) ≤ _
    simpa only [unconditionalExactFairGammaUnit_eq_global] using
      c.stopping.hazard
  calc
    deviation c =
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          law c h *
            dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
              c.stopping.Q c.stopping.m (width c) (schedule c)
              (gammaVector c h) (phiVector c h)
              c.stopping.UA c.stopping.UB) := by
          simpa only [deviation, actual, canonical] using identification
    _ ≤ _ := fair_hazard

theorem unconditionalActualFairSourceRoundingContext_analyticLedger
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    UnconditionalActualFairCachedStoppedAnalyticLedger
      (law c) (actual c) (canonical c) (source c)
      (deviation c) (clipping c) (bad c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact unconditionalActualFairWeightedCleanedMass_le_one
      (law c)
      (exactLocallySampleableLaw_nonneg G n S D c.positive)
      (exactLocallySampleableLaw_sum
        G n S D c.remaining c.positive)
      c.stopping.phases c.stopping.grid (dimension_pos c)
      c.stopping.harmonic (width c) (width_all c) (schedule c)
      (gammaVector c) (phiVector c)
      c.stopping.Q c.stopping.UA c.stopping.UB
  · exact unconditionalActualFairWeightedCanonicalMass_le_one
      (law c)
      (exactLocallySampleableLaw_nonneg G n S D c.positive)
      (exactLocallySampleableLaw_sum
        G n S D c.remaining c.positive)
      c.stopping.phases c.stopping.grid (dimension_pos c)
      c.stopping.harmonic (width c) (width_all c) (schedule c)
      (gammaVector c) (phiVector c) (fine_all c)
  · intro h
    exact unconditionalActualFairCanonicalRow_le_one
      c.stopping.phases c.stopping.grid (dimension_pos c)
      c.stopping.harmonic (width c) (width_all c) (schedule c)
      (gammaVector c h) (phiVector c h) (fine_all c)
  · intro h j
    exact unconditionalActualFairSourceCanonicalVector_norm
      c.stopping.phases c.stopping.grid c.stopping.harmonic
      (width c) (schedule c) (gammaVector c h) (phiVector c h)
      (psiVector c h) (exactSourceTuplePsi_norm G n S D h) j
      (width_all c (schedule c j)) (fine_all c (schedule c j))
  · exact le_refl (deviation c)
  · change
      (∑ h : ExactLocallySampleableTuple X Y A B D,
        law c h *
          ∑ j : Fin c.stopping.L,
            ‖canonical c (h, j) - source c (h, j)‖ ^ 2) ≤
        unconditionalActualC485FairSourceClipEnergy
          (P := c.stopping.P) (m := c.stopping.m)
          G n S D (width_positive c) c.stopping.grid
          c.stopping.fine (schedule c)
    unfold unconditionalActualC485FairSourceClipEnergy
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro h _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    change
      ‖canonical c (h, j) - source c (h, j)‖ ^ 2 =
        ‖source c (h, j) - canonical c (h, j)‖ ^ 2
    rw [norm_sub_rev]
  · have async :
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          law c h *
            dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
              c.stopping.N (width c) (schedule c)
              (gammaVector c h) (phiVector c h)) ≤
          64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ) := by
      change
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
              c.stopping.N
              (fun _ : Fin 1 => c.stopping.w)
              (fun _ : Fin c.stopping.L => 0)
              (unconditionalExactFairGammaUnit G n S D h)
              (exactGlobalHistoryFinPhi
                G n S D h.2.2.2 h.2.2.1)) ≤ _
      simpa only [unconditionalExactFairGammaUnit_eq_global] using
        c.stopping.asynchronous
    have finish :
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          law c h *
            dSVDensityRationalHeterogeneousPhysicalTerminalMass
              c.stopping.N (width c) (schedule c)
              (gammaVector c h) (phiVector c h)) ≤
          (alpha ^ (1 / 3 : ℝ)) ^ 2 := by
      change
        (∑ h : ExactLocallySampleableTuple X Y A B D,
          exactLocallySampleableLaw G n S D h *
            dSVDensityRationalHeterogeneousPhysicalTerminalMass
              c.stopping.N
              (fun _ : Fin 1 => c.stopping.w)
              (fun _ : Fin c.stopping.L => 0)
              (unconditionalExactFairGammaUnit G n S D h)
              (exactGlobalHistoryFinPhi
                G n S D h.2.2.2 h.2.2.1)) ≤ _
      simpa only [unconditionalExactFairGammaUnit_eq_global] using
        c.stopping.terminal
    exact unconditionalActualFairWeightedStoppedSuccess
      (law c)
      (exactLocallySampleableLaw_sum
        G n S D c.remaining c.positive)
      c.stopping.phases c.stopping.grid (dimension_pos c)
      c.stopping.harmonic (width c) (width_all c) (schedule c)
      (gammaVector c) (phiVector c)
      c.stopping.Q c.stopping.UA c.stopping.UB
      (64 * Real.sqrt (martingaleRate G n S D) +
        alpha ^ (1 / 3 : ℝ))
      ((alpha ^ (1 / 3 : ℝ)) ^ 2) async finish

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

theorem unconditionalActualFairSourceRoundingContext_verifierLedger
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    UnconditionalActualFairCachedSourceVerifierLedger
      G n S D c.effect c.actual c.source := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    exact unconditionalActualFairSourceVerifier_norm_le_one
      G n S D c.aliceDefault c.bobDefault
      p.2 p.1.2.1 p.1.2.2.1
  · intro h supported j
    change
      quadraticExpectation
          (integratorActualC485WinningEffect
            (P := c.stopping.P) (N := c.stopping.N)
            (m := c.stopping.m)
            G n S D c.aliceDefault c.bobDefault
            j h.2.1 h.2.2.1)
          (integratorActualC485SourceVector
            (S := 1) (B := c.stopping.P) (N := c.stopping.N)
            (d := c.d) (L := c.stopping.L) (m := c.stopping.m)
            c.width c.schedule
            (unconditionalExactFairGammaUnit G n S D h)
            (exactGlobalHistoryFinPhi
              G n S D h.2.2.2 h.2.2.1)
            (exactSourceTuplePsi G n S D h) j) =
        ‖integratorActualC485SourceVector
            (S := 1) (B := c.stopping.P) (N := c.stopping.N)
            (d := c.d) (L := c.stopping.L) (m := c.stopping.m)
            c.width c.schedule
            (unconditionalExactFairGammaUnit G n S D h)
            (exactGlobalHistoryFinPhi
              G n S D h.2.2.2 h.2.2.1)
            (exactSourceTuplePsi G n S D h) j‖ ^ 2 *
          exactSourceConditionalWinningProbability G n S D h
    rw [unconditionalExactFairGammaUnit_eq_global]
    exact unconditionalActualFairSourceSupportedBorn
      G n S D c.positive c.aliceDefault c.bobDefault h supported
      c.stopping.phases c.stopping.grid c.stopping.harmonic
      c.width c.schedule j
  · intro h
    exact unconditionalActualFairSourceVerifier_historyBorn_nonnegative
      G n S D c.aliceDefault c.bobDefault
      (fun h j => c.actual (h, j))
      (unconditionalActualFairSourceRoundingContext_actualRow c) h
  · intro h
    exact unconditionalActualFairSourceVerifier_historyBorn_bounded
      G n S D c.aliceDefault c.bobDefault
      (fun h j => c.actual (h, j))
      (unconditionalActualFairSourceRoundingContext_actualRow c) h

theorem unconditionalActualFairSourceRoundingContext_physicalBranch
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (flag : ExactSourceSharedFlag
      X Y A B D c.sampler.denominator)
    (x : X) (y : Y)
    (matching :
      exactSourcePermutationMatched
        D c.sampler.denominator c.sampler.numerator
        c.sampler.nonempty (flag, (x, y)) = true) :
    (∑ j : Fin c.stopping.L,
      quadraticExpectation
        (c.effect
          (exactSourceAliceSampleTuple
            D c.sampler.denominator c.sampler.numerator
            c.sampler.nonempty (flag, (x, y)), j))
        (c.actual
          (exactSourceAliceSampleTuple
            D c.sampler.denominator c.sampler.numerator
            c.sampler.nonempty (flag, (x, y)), j))) ≤
      ∑ j : Fin c.stopping.L,
        quadraticExpectation
          (Matrix.toEuclideanCLM
            (n := c.fiber × c.fiber) (𝕜 := ℂ)
            (actualStoppingBranchWinningEffect
              G (c.PA flag) (c.PB flag) j.succ j.succ x y))
          (actualStoppingBranchVector
            (actualStoppingQuestionLocalAction
              (c.U flag x) (c.V flag y) (c.prepared flag))
            j.succ j.succ) := by
  classical
  apply le_of_eq
  change
    (∑ j : Fin c.stopping.L,
      unconditionalActualFairSourceHistoryStopBorn
        G n S D c.aliceDefault c.bobDefault
        c.stopping.Q c.width c.schedule c.stopping.UA c.stopping.UB
        (exactSourceAliceSampleTuple
          D c.sampler.denominator c.sampler.numerator
          c.sampler.nonempty (flag, (x, y))) j) =
      ∑ j : Fin c.stopping.L,
        unconditionalActualFairSourcePhysicalStopBorn
          G n S D c.sampler.denominator c.sampler.numerator
          c.sampler.nonempty c.aliceDefault c.bobDefault
          c.stopping.Q c.width c.schedule
          c.stopping.UA c.stopping.UB flag x y j
  exact unconditionalActualFairSourcePhysicalBranchWitness
    G n S D c.sampler.denominator c.sampler.numerator
    c.sampler.nonempty c.aliceDefault c.bobDefault
    c.stopping.Q c.width c.schedule c.stopping.UA c.stopping.UB
    c.stopping.grid c.width_all flag x y matching

theorem unconditionalActualFairSourceRoundingContext_stoppedVerifier
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    1 - (1 - entangledValue G) / 2 -
      5 * (exactSourcePinskerRate G n S D + gamma) -
        ((64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ) +
            (alpha ^ (1 / 3 : ℝ)) ^ 2) +
          4 * Real.sqrt c.deviation + 2 * Real.sqrt c.clipping) ≤
      c.rounded.winProbability := by
  classical
  have stopped :=
    unconditionalActualFairCachedLedgerStoppingTransfer
      G n S D c.remaining c.positive
      c.sampler.base c.sampler.denominator c.sampler.denominator_positive
      c.sampler.numerator c.sampler.rational_normalized
      c.sampler.support_preserving c.sampler.nonempty
      c.PA c.PB c.U c.V c.prepared c.prepared_normalized
      (exactSourcePermutationMatched
        D c.sampler.denominator c.sampler.numerator c.sampler.nonempty)
      c.effect c.actual c.canonical c.source
      (1 - entangledValue G)
      (exactSourcePinskerRate G n S D + gamma)
      c.deviation c.clipping c.bad
      (unconditionalActualFairSourceRoundingContext_analyticLedger c)
      (unconditionalActualFairSourceRoundingContext_verifierLedger c)
      c.failure c.sampler.total_variation c.sampler.mismatch
      (fun flag x y matching =>
        unconditionalActualFairSourceRoundingContext_physicalBranch
          c flag x y matching)
  change
    1 - (1 - entangledValue G) / 2 -
      5 * (exactSourcePinskerRate G n S D + gamma) -
        ((64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ) +
            (alpha ^ (1 / 3 : ℝ)) ^ 2) +
          4 * Real.sqrt c.deviation + 2 * Real.sqrt c.clipping) ≤
      c.rounded.winProbability at stopped
  exact stopped

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

theorem unconditionalActualFairSourceRoundingData_exists_stoppedVerifier
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha gamma : ℝ)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (gamma_positive : 0 < gamma)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1)
    (failure :
      uniformRemainingFailure
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D <
        (1 - entangledValue G) / 2) :
    ∃ (deviation clipping : ℝ) (rounded : Strategy G),
      (deviation ≤
        (34 / Real.sqrt
            (64 * Real.sqrt (martingaleRate G n S D) +
              alpha ^ (1 / 3 : ℝ))) *
          (64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ))) ∧
      (clipping ≤
        16 * martingaleRate G n S D +
          8 * (3 * alpha ^ (1 / 3 : ℝ) / 2)) ∧
      (1 - (1 - entangledValue G) / 2 -
        5 * (exactSourcePinskerRate G n S D + gamma) -
          ((64 * Real.sqrt (martingaleRate G n S D) +
              alpha ^ (1 / 3 : ℝ) +
              (alpha ^ (1 / 3 : ℝ)) ^ 2) +
            4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
        rounded.winProbability) := by
  classical
  let context :=
    unconditionalActualFairSourceRoundingContext_of_positive
      G n S D remaining positive alpha gamma
      alpha_positive alpha_bounded gamma_positive small failure
  exact ⟨
    UnconditionalActualFairSourceRoundingContext.deviation context,
    UnconditionalActualFairSourceRoundingContext.clipping context,
    UnconditionalActualFairSourceRoundingContext.rounded context,
    unconditionalActualFairSourceRoundingContext_cleanBound context,
    unconditionalActualFairSourceRoundingContext_clippingBound context,
    unconditionalActualFairSourceRoundingContext_stoppedVerifier context⟩

end

noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

theorem unconditionalSourcePhysicalRounding_exists_small
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha gamma : ℝ)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (gamma_positive : 0 < gamma)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1)
    (failure :
      uniformRemainingFailure
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D <
        (1 - entangledValue G) / 2) :
    ∃ rounded : Strategy G,
      roundedWinningLowerBound
          (1 - entangledValue G)
          unconditionalSourcePhysicalRoundingUniversalConstant
          alpha (martingaleRate G n S D)
          (exactSourcePinskerRate G n S D + gamma) ≤
        rounded.winProbability := by
  obtain ⟨deviation, clipping, rounded,
      deviation_bound, clipping_bound, stopped⟩ :=
    unconditionalActualFairSourceRoundingData_exists_stoppedVerifier
      G n S D remaining positive alpha gamma
      alpha_positive alpha_bounded gamma_positive small failure
  refine ⟨rounded, ?_⟩
  exact
    unconditionalSourcePhysicalRounding_smallRoundedLower_of_stoppedVerifier
      G n S D remaining positive alpha gamma deviation clipping
      alpha_positive alpha_bounded gamma_positive small
      deviation_bound clipping_bound rounded stopped

theorem unconditionalSourceOneGameRounding_uniform :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B)
        (n : ℕ) (S : Strategy (G.repeat n))
        (D : Finset (Fin n)),
        0 < (Finset.univ \ D).card →
        0 < repeatedPostselectionMass G n S D →
        ∀ (alpha gamma : ℝ),
          0 < alpha → alpha ≤ 1 → 0 < gamma →
          uniformRemainingFailure
              (strategyEventLaw (G.repeat n) S)
              (repeatedCoordinateWin G n) D <
            (1 - entangledValue G) / 2 →
          ∃ rounded : Strategy G,
            roundedWinningLowerBound (1 - entangledValue G)
                K alpha (martingaleRate G n S D)
                (exactSourcePinskerRate G n S D + gamma) ≤
              rounded.winProbability :=
  unconditionalSourceOneGameRounding_uniform_of_small
    unconditionalSourcePhysicalRounding_exists_small

end

noncomputable section

theorem pdf_distributionUniformExponential_unconditional :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B),
        Nonempty A → Nonempty B →
        0 < 1 - entangledValue G →
        ∀ n : ℕ, 0 < n →
          repeatedEntangledValue G n ≤
            Real.exp
              (-(c *
                ((1 - entangledValue G) ^ 13 /
                  ((1 - entangledValue G) +
                    Real.log
                      ((Fintype.card A : ℝ) *
                        (Fintype.card B : ℝ))))) * (n : ℝ)) :=
  pdf_distributionUniformExponential_of_uniform_source_rounding
    unconditionalSourceOneGameRounding_uniform

theorem exactSourceOneGameRounding_unconditional
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) :
    ExactSourceOneGameRounding G := by
  obtain ⟨K, constant, round⟩ :=
    unconditionalSourceOneGameRounding_uniform
  refine ⟨K, le_trans (by norm_num : (0 : ℝ) ≤ 1) constant, ?_⟩
  exact round G

theorem exact_standardQuantumParallelRepetition_unconditional
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) :
    StandardQuantumParallelRepetition G :=
  exact_standardQuantumParallelRepetition_of_source_rounding G
    (exactSourceOneGameRounding_unconditional G)

theorem distributionUniformExponential :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B),
        Nonempty A → Nonempty B →
        0 < 1 - entangledValue G →
        ∀ n : ℕ, 0 < n →
          repeatedEntangledValue G n ≤
            Real.exp
              (-(c *
                ((1 - entangledValue G) ^ 13 /
                  ((1 - entangledValue G) +
                    Real.log
                      ((Fintype.card A : ℝ) *
                        (Fintype.card B : ℝ))))) * (n : ℝ)) :=
  pdf_distributionUniformExponential_unconditional

theorem standardQuantumParallelRepetition
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) :
    StandardQuantumParallelRepetition G :=
  exact_standardQuantumParallelRepetition_unconditional G

end

end QuantumParallelRepetition
