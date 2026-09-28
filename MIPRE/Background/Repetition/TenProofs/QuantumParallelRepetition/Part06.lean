/-
Copyright (c) 2026 the openai/ten-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/openai/ten-proofs (commit 94bc0feb, 2026-08-01) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: QuantumParallelRepetition.lean
-/
module
public import Mathlib
public import MIPRE.Background.Repetition.TenProofs.QuantumParallelRepetition.Part05

@[expose] public section

-- Part 6 of 8 of upstream's single module `QuantumParallelRepetition.lean`: its lines
-- 44530-53489, cut between top-level `noncomputable section` blocks by
-- scripts/vendor-repetition.py (the Palomar registry caps a Lean file at 10,000 lines).
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset


noncomputable section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem dSVDensityRationalPublicLogRankPhaseWeightedCrossing_le_one
    {N B : ℕ} (positive : 0 < B) (Q : ℕ)
    (r s : Fin (N + 1)) :
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing
        Q B r s ≤ 1 := by
  unfold dSVDensityRationalPublicLogRankPhaseWeightedCrossing
  calc
    _ ≤ ∑ phase : Fin B,
        dSVDensityRationalPublicLogRankPhaseWeight B phase := by
      apply Finset.sum_le_sum
      intro phase _
      split_ifs <;>
        simp [dSVDensityRationalPublicLogRankPhaseWeight]
    _ = 1 :=
      dSVDensityRationalPublicLogRankPhaseWeight_sum positive

theorem
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing_alice_le
    {N B : ℕ} (positive : 0 < B) (Q : ℕ)
    (r s : Fin (N + 1)) :
    (r.val : ℝ) *
        dSVDensityRationalPublicLogRankPhaseWeightedCrossing
          Q B r s ≤
      ((Q : ℝ) / (B : ℝ) + 1) *
          |(r.val : ℝ) - (s.val : ℝ)| +
        min (r.val : ℝ) (s.val : ℝ) / (B : ℝ) := by
  let x :=
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing
      Q B r s
  let m : ℝ := min (r.val : ℝ) (s.val : ℝ)
  let t : ℝ := |(r.val : ℝ) - (s.val : ℝ)|
  have nonnegative : 0 ≤ x :=
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing_nonneg
      Q B r s
  have probability : x ≤ 1 :=
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing_le_one
      positive Q r s
  have min_le : m ≤ (r.val : ℝ) := min_le_left _ _
  have difference : (r.val : ℝ) - m ≤ t := by
    dsimp [m, t]
    rcases le_total (r.val : ℝ) (s.val : ℝ) with ordered | ordered
    · rw [min_eq_left ordered]
      simp
    · rw [min_eq_right ordered, abs_of_nonneg
        (sub_nonneg.mpr ordered)]
  have extra : ((r.val : ℝ) - m) * x ≤ t := by
    calc
      _ ≤ ((r.val : ℝ) - m) * 1 :=
        mul_le_mul_of_nonneg_left probability
          (sub_nonneg.mpr min_le)
      _ ≤ t := by simpa using difference
  have main :=
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing_min_le
      positive Q r s
  change m * x ≤ (Q : ℝ) / (B : ℝ) * t + m / (B : ℝ)
    at main
  change (r.val : ℝ) * x ≤
    ((Q : ℝ) / (B : ℝ) + 1) * t + m / (B : ℝ)
  nlinarith

theorem
    exists_proofDSVDensityRationalPublicBucketPhysicalQuantitativeMixedPrefixCleanup_sq
    {N B : ℕ} (grid : 0 < N) (phases : 0 < B)
    {Q : ℕ} (fine : 0 < Q)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ (r s : Fin (N + 1)),
          (∑ phase : Fin B,
            dSVDensityRationalPublicLogRankPhaseWeight B phase *
              ‖localUnitaryAction
                  (A phase
                    (dSVDensityRationalPublicLogRankBucket
                      Q phase r))
                  (C phase
                    (dSVDensityRationalPublicLogRankBucket
                      Q phase s))
                  (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                    n (dSVCanonicalFailurePrefix
                      (dSVDensityRationalPublicBucketPhysicalCommonRank
                        r s))) -
                Real.sqrt (r.val : ℝ) •
                  embezzlementState (N * n)‖ ^ 2) ≤
            2 * |(r.val : ℝ) - (s.val : ℝ)| +
            4 * (r.val : ℝ) * ε ^ 2 +
            16 * (r.val : ℝ) *
              (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
            8 * (((Q : ℝ) / (B : ℝ) + 1) *
              |(r.val : ℝ) - (s.val : ℝ)| +
              min (r.val : ℝ) (s.val : ℝ) / (B : ℝ)) := by
  let bucket : Fin B → Fin (N + 1) → Option ℕ :=
    dSVDensityRationalPublicLogRankBucket Q
  let representative : Fin B → Option ℕ → Fin (N + 1) :=
    dSVDensityRationalPublicLogRankBucketRepresentative Q
  obtain ⟨n, positive, A, C, accurate⟩ :=
    exists_proofDSVDensityRationalPublicBucketPhysicalMixedPrefixCleanup_sq
      grid bucket representative ε precision
  refine ⟨n, positive, A, C, ?_⟩
  intro r s
  let gap : ℝ := |(r.val : ℝ) - (s.val : ℝ)|
  let radius : ℝ :=
    Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1
  let base : ℝ :=
    2 * gap + 4 * (r.val : ℝ) * ε ^ 2 +
      16 * (r.val : ℝ) * radius
  have representative_bound (phase : Fin B) :
      (r.val : ℝ) *
          (|(r.val : ℝ) -
            ((representative phase (bucket phase r)).val : ℝ)| /
            ((max 1
              (min r.val
                (representative phase (bucket phase r)).val) : ℕ) : ℝ)) ≤
        (r.val : ℝ) * radius := by
    by_cases zero : r.val = 0
    · simp [zero]
    · have actual :=
        dSVDensityRationalPublicLogRankBucketRepresentative_relative_abs_lt
          fine phase r zero
      change
        |(r.val : ℝ) -
          ((representative phase (bucket phase r)).val : ℝ)| /
          ((max 1
            (min r.val
              (representative phase (bucket phase r)).val) : ℕ) : ℝ) <
          radius at actual
      exact mul_le_mul_of_nonneg_left actual.le (Nat.cast_nonneg r.val)
  have point (phase : Fin B) :
      ‖localUnitaryAction
          (A phase (bucket phase r))
          (C phase (bucket phase s))
          (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
            n (dSVCanonicalFailurePrefix
              (dSVDensityRationalPublicBucketPhysicalCommonRank
                r s))) -
        Real.sqrt (r.val : ℝ) •
          embezzlementState (N * n)‖ ^ 2 ≤
        base + 8 * (r.val : ℝ) *
          (if bucket phase r = bucket phase s
            then (0 : ℝ) else 1) := by
    have actual := accurate phase r s
    have variation := representative_bound phase
    calc
      _ ≤ 2 * gap +
          2 * (r.val : ℝ) *
            (2 * ε ^ 2 +
              8 *
                |(r.val : ℝ) -
                  ((representative phase (bucket phase r)).val : ℝ)| /
                  ((max 1
                    (min r.val
                      (representative phase (bucket phase r)).val) : ℕ) : ℝ) +
              4 * (if bucket phase r = bucket phase s
                then (0 : ℝ) else 1)) := by
                simpa [gap] using actual
      _ = 2 * gap + 4 * (r.val : ℝ) * ε ^ 2 +
          16 * ((r.val : ℝ) *
            (|(r.val : ℝ) -
              ((representative phase (bucket phase r)).val : ℝ)| /
              ((max 1
                (min r.val
                  (representative phase (bucket phase r)).val) : ℕ) : ℝ))) +
          8 * (r.val : ℝ) *
            (if bucket phase r = bucket phase s
              then (0 : ℝ) else 1) := by ring
      _ ≤ base + 8 * (r.val : ℝ) *
            (if bucket phase r = bucket phase s
              then (0 : ℝ) else 1) := by
            dsimp [base]
            nlinarith
  have averaged :
      (∑ phase : Fin B,
        dSVDensityRationalPublicLogRankPhaseWeight B phase *
          ‖localUnitaryAction
              (A phase (bucket phase r))
              (C phase (bucket phase s))
              (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                n (dSVCanonicalFailurePrefix
                  (dSVDensityRationalPublicBucketPhysicalCommonRank
                    r s))) -
            Real.sqrt (r.val : ℝ) •
              embezzlementState (N * n)‖ ^ 2) ≤
        base + 8 * (r.val : ℝ) *
          dSVDensityRationalPublicLogRankPhaseWeightedCrossing
            Q B r s := by
    calc
      _ ≤ ∑ phase : Fin B,
          dSVDensityRationalPublicLogRankPhaseWeight B phase *
            (base + 8 * (r.val : ℝ) *
              (if bucket phase r = bucket phase s
                then (0 : ℝ) else 1)) := by
            apply Finset.sum_le_sum
            intro phase _
            exact mul_le_mul_of_nonneg_left (point phase)
              (by
                unfold dSVDensityRationalPublicLogRankPhaseWeight
                positivity)
      _ = base + 8 * (r.val : ℝ) *
          dSVDensityRationalPublicLogRankPhaseWeightedCrossing
            Q B r s := by
            unfold
              dSVDensityRationalPublicLogRankPhaseWeightedCrossing
            have total :=
              dSVDensityRationalPublicLogRankPhaseWeight_sum
                phases
            calc
              _ = base *
                    (∑ phase : Fin B,
                      dSVDensityRationalPublicLogRankPhaseWeight
                        B phase) +
                  8 * (r.val : ℝ) *
                    (∑ phase : Fin B,
                      dSVDensityRationalPublicLogRankPhaseWeight
                        B phase *
                        (if bucket phase r = bucket phase s
                          then (0 : ℝ) else 1)) := by
                    simp_rw [Finset.mul_sum]
                    rw [← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro phase _
                    ring
              _ = _ := by rw [total]; simp [bucket]
  have crossing :=
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing_alice_le
      phases Q r s
  change _ ≤ 2 * gap + 4 * (r.val : ℝ) * ε ^ 2 +
    16 * (r.val : ℝ) * radius +
    8 * (((Q : ℝ) / (B : ℝ) + 1) * gap +
      min (r.val : ℝ) (s.val : ℝ) / (B : ℝ))
  change
    (r.val : ℝ) *
        dSVDensityRationalPublicLogRankPhaseWeightedCrossing
          Q B r s ≤
      ((Q : ℝ) / (B : ℝ) + 1) * gap +
        min (r.val : ℝ) (s.val : ℝ) / (B : ℝ)
    at crossing
  dsimp [bucket] at averaged
  dsimp [base] at averaged
  nlinarith

def dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : ℝ :=
  dSVDensityRationalPrefixHarmonicSpectralOverlap ξ ζ i j /
    ((d : ℝ) * (N : ℝ))

theorem
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight_nonneg
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) :
    0 ≤ dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
      N ξ ζ i j := by
  exact div_nonneg
    (dSVDensityRationalPrefixHarmonicSpectralOverlap_nonneg
      ξ ζ i j)
    (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg N))

def dSVDensityRationalHeterogeneousCommonStopSpectralRankGap
    {d : ℕ} (N : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
      N ξ ζ i j *
      |((dSVDensityRationalPhysicalAcceptedRank w N ξ i).val : ℝ) -
        ((dSVDensityRationalPhysicalAcceptedRank w N ζ j).val : ℝ)|

theorem
    dSVDensityRationalHeterogeneousCommonStopSpectralRankGap_eq_hazard
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousCommonStopSpectralRankGap
        N w ξ ζ =
      dSVDensityRationalPhysicalProjectorCrossHazard N w ξ ζ := by
  rw [← dSVDensityRationalPrefixRankMismatch_physicalHazard
    grid dimension w ξ ζ]
  unfold
    dSVDensityRationalHeterogeneousCommonStopSpectralRankGap
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
    dSVDensityRationalPrefixRankMismatch
    dSVDensityRationalPrefixHarmonicSpectralOverlap
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [div_div, mul_comm (N : ℝ) (d : ℝ)]

def dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass
    {d : ℕ} (N : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
      N ξ ζ i j *
      ((dSVDensityRationalPhysicalAcceptedRank w N ξ i).val : ℝ)

theorem
    dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass_eq_diagonalBorn
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass
        N w ξ ζ =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ := by
  classical
  have row (i : Fin d) :
      (∑ j : Fin d,
        dSVDensityRationalPrefixHarmonicSpectralOverlap
          ξ ζ i j) = 1 := by
    unfold dSVDensityRationalPrefixHarmonicSpectralOverlap
    exact spectralAtomOverlap_sum_right
      (dSVSoftBobLeftReducedDensity ξ)
      (dSVSoftBobLeftReducedDensity ζ)
      (dSVSoftBobLeftReducedDensity_posSemidef ξ)
      (dSVSoftBobLeftReducedDensity_posSemidef ζ) i
  rw [dSVDensityRationalPhysicalDiagonalBornSuccess_eq
    grid dimension w ξ]
  unfold
    dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
    dSVDensityRationalLeftProjectiveDiagonalMass
  simp_rw [dSVDensityRationalPhysicalAcceptedRank_gridPrefix]
  calc
    (∑ i : Fin d, ∑ j : Fin d,
      dSVDensityRationalPrefixHarmonicSpectralOverlap ξ ζ i j /
          ((d : ℝ) * (N : ℝ)) *
        ((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ)) =
      ∑ i : Fin d,
        (((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ) / ((d : ℝ) * (N : ℝ))) *
          (∑ j : Fin d,
            dSVDensityRationalPrefixHarmonicSpectralOverlap
              ξ ζ i j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = ∑ i : Fin d,
        ((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ) / ((d : ℝ) * (N : ℝ)) := by
      simp_rw [row, mul_one]
    _ = (∑ i : Fin d,
        ((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ)) /
          ((d : ℝ) * (N : ℝ)) := by
      rw [Finset.sum_div]
    _ = ((∑ i : Fin d,
        ((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ)) / (N : ℝ)) / (d : ℝ) := by
      rw [div_div, mul_comm (N : ℝ) (d : ℝ)]
    _ = (∑ i : Fin d,
        ((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ) / (N : ℝ)) / (d : ℝ) := by
      rw [Finset.sum_div]

theorem
    exists_proofDSVDensityRationalHeterogeneousCommonStopSpectralGaugeContinuity_sq
    {d N B : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (phases : 0 < B) {Q : ℕ} (fine : 0 < Q)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ {S L : ℕ}
          (width : Fin S → ℝ) (schedule : Fin L → Fin S)
          (ξ ζ : BipartiteUnitVector d) (k : Fin L),
          ‖dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
              Q (width (schedule k)) ξ ζ A C
              (dSVDensityRationalPublicBucketPhysicalCoherentMixedState
                (N := N) (B := B)
                (width (schedule k)) n ξ ζ) -
            dSVDensityRationalPublicBucketPhysicalCoherentTargetState
              (N := N) (B := B)
              (width (schedule k)) n ξ ζ‖ ^ 2 ≤
            (10 + 8 * ((Q : ℝ) / (B : ℝ))) *
                dSVDensityRationalPhysicalProjectorCrossHazard
                  N (width (schedule k)) ξ ζ +
              (4 * ε ^ 2 +
                16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
                8 / (B : ℝ)) *
                dSVDensityRationalPhysicalDiagonalBornSuccess
                  grid dimension (width (schedule k)) ξ := by
  classical
  obtain ⟨n, harmonic, A, C, accurate⟩ :=
    exists_proofDSVDensityRationalPublicBucketPhysicalQuantitativeMixedPrefixCleanup_sq
      grid phases fine ε precision
  refine ⟨n, harmonic, A, C, ?_⟩
  intro S L width schedule ξ ζ k
  let w : ℝ := width (schedule k)
  let coefficient : Fin d → Fin d → ℝ :=
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
      N ξ ζ
  let gap : Fin d → Fin d → ℝ := fun i j =>
    |((dSVDensityRationalPhysicalAcceptedRank w N ξ i).val : ℝ) -
      ((dSVDensityRationalPhysicalAcceptedRank w N ζ j).val : ℝ)|
  let alice : Fin d → ℝ := fun i =>
    ((dSVDensityRationalPhysicalAcceptedRank w N ξ i).val : ℝ)
  let Kgap : ℝ := 10 + 8 * ((Q : ℝ) / (B : ℝ))
  let Kmass : ℝ :=
    4 * ε ^ 2 +
      16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
      8 / (B : ℝ)
  have point (i j : Fin d) :
      (∑ phase : Fin B,
        dSVDensityRationalPublicLogRankPhaseWeight B phase *
          ‖localUnitaryAction
              (A phase
                (dSVDensityRationalPublicLogRankBucket Q phase
                  (dSVDensityRationalPhysicalAcceptedRank
                    w N ξ i)))
              (C phase
                (dSVDensityRationalPublicLogRankBucket Q phase
                  (dSVDensityRationalPhysicalAcceptedRank
                    w N ζ j)))
              (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                n (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
                  w N ξ ζ i j)) -
            Real.sqrt (alice i) •
              embezzlementState (N * n)‖ ^ 2) ≤
        Kgap * gap i j + Kmass * alice i := by
    have atom := accurate
      (dSVDensityRationalPhysicalAcceptedRank w N ξ i)
      (dSVDensityRationalPhysicalAcceptedRank w N ζ j)
    rw [dSVDensityRationalPublicBucketPhysicalCommonRank_eq
      w ξ ζ i j] at atom
    change
      (∑ phase : Fin B,
        dSVDensityRationalPublicLogRankPhaseWeight B phase *
          ‖localUnitaryAction
              (A phase
                (dSVDensityRationalPublicLogRankBucket Q phase
                  (dSVDensityRationalPhysicalAcceptedRank
                    w N ξ i)))
              (C phase
                (dSVDensityRationalPublicLogRankBucket Q phase
                  (dSVDensityRationalPhysicalAcceptedRank
                    w N ζ j)))
              (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                n (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
                  w N ξ ζ i j)) -
            Real.sqrt (alice i) •
              embezzlementState (N * n)‖ ^ 2) ≤
        2 * gap i j + 4 * alice i * ε ^ 2 +
          16 * alice i *
            (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
          8 * (((Q : ℝ) / (B : ℝ) + 1) * gap i j +
            min (alice i)
              ((dSVDensityRationalPhysicalAcceptedRank
                w N ζ j).val : ℝ) / (B : ℝ)) at atom
    have min_bound :
        min (alice i)
            ((dSVDensityRationalPhysicalAcceptedRank
              w N ζ j).val : ℝ) / (B : ℝ) ≤
          alice i / (B : ℝ) :=
      div_le_div_of_nonneg_right (min_le_left _ _)
        (by exact_mod_cast phases.le)
    calc
      _ ≤ 2 * gap i j + 4 * alice i * ε ^ 2 +
          16 * alice i *
            (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
          8 * (((Q : ℝ) / (B : ℝ) + 1) * gap i j +
            min (alice i)
              ((dSVDensityRationalPhysicalAcceptedRank
                w N ζ j).val : ℝ) / (B : ℝ)) := atom
      _ = Kgap * gap i j +
          (4 * ε ^ 2 +
            16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1)) *
              alice i +
          8 * (min (alice i)
            ((dSVDensityRationalPhysicalAcceptedRank
              w N ζ j).val : ℝ) / (B : ℝ)) := by
        dsimp [Kgap]
        ring
      _ ≤ Kgap * gap i j +
          (4 * ε ^ 2 +
            16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1)) *
              alice i +
          8 * (alice i / (B : ℝ)) := by
        nlinarith [min_bound]
      _ = Kgap * gap i j + Kmass * alice i := by
        dsimp [Kmass]
        ring
  have exchange :
      dSVDensityRationalPublicBucketPhysicalPhaseWeightedMixedError
          Q w ξ ζ A C =
        ∑ i : Fin d, ∑ j : Fin d,
          coefficient i j *
            (∑ phase : Fin B,
              dSVDensityRationalPublicLogRankPhaseWeight B phase *
                ‖localUnitaryAction
                    (A phase
                      (dSVDensityRationalPublicLogRankBucket
                        Q phase
                        (dSVDensityRationalPhysicalAcceptedRank
                          w N ξ i)))
                    (C phase
                      (dSVDensityRationalPublicLogRankBucket
                        Q phase
                        (dSVDensityRationalPhysicalAcceptedRank
                          w N ζ j)))
                    (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                      n
                      (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
                        w N ξ ζ i j)) -
                  Real.sqrt (alice i) •
                    embezzlementState (N * n)‖ ^ 2) := by
    unfold dSVDensityRationalPublicBucketPhysicalPhaseWeightedMixedError
    change
      (∑ phase : Fin B,
        dSVDensityRationalPublicLogRankPhaseWeight B phase *
          ∑ i : Fin d, ∑ j : Fin d,
            coefficient i j * _) = _
    calc
      _ = ∑ phase : Fin B, ∑ i : Fin d, ∑ j : Fin d,
        dSVDensityRationalPublicLogRankPhaseWeight B phase *
          (coefficient i j *
            ‖localUnitaryAction
                (A phase
                  (dSVDensityRationalPublicLogRankBucket Q phase
                    (dSVDensityRationalPhysicalAcceptedRank
                      w N ξ i)))
                (C phase
                  (dSVDensityRationalPublicLogRankBucket Q phase
                    (dSVDensityRationalPhysicalAcceptedRank
                      w N ζ j)))
                (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                  n
                  (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
                    w N ξ ζ i j)) -
              Real.sqrt (alice i) •
                embezzlementState (N * n)‖ ^ 2) := by
          simp_rw [Finset.mul_sum]
          rfl
      _ = ∑ i : Fin d, ∑ j : Fin d, ∑ phase : Fin B,
        dSVDensityRationalPublicLogRankPhaseWeight B phase *
          (coefficient i j *
            ‖localUnitaryAction
                (A phase
                  (dSVDensityRationalPublicLogRankBucket Q phase
                    (dSVDensityRationalPhysicalAcceptedRank
                      w N ξ i)))
                (C phase
                  (dSVDensityRationalPublicLogRankBucket Q phase
                    (dSVDensityRationalPhysicalAcceptedRank
                      w N ζ j)))
                (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                  n
                  (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
                    w N ξ ζ i j)) -
              Real.sqrt (alice i) •
                embezzlementState (N * n)‖ ^ 2) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro phase _
          ring
  rw [dSVDensityRationalPublicBucketPhysicalCoherentMixedReset_distance_sq
    phases Q w ξ ζ A C, exchange]
  calc
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
        coefficient i j * (Kgap * gap i j + Kmass * alice i) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (point i j)
        (dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight_nonneg
          N ξ ζ i j)
    _ = Kgap *
          dSVDensityRationalHeterogeneousCommonStopSpectralRankGap
            N w ξ ζ +
        Kmass *
          dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass
            N w ξ ζ := by
      unfold
        dSVDensityRationalHeterogeneousCommonStopSpectralRankGap
        dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass
      change
        (∑ i : Fin d, ∑ j : Fin d,
          coefficient i j * (Kgap * gap i j + Kmass * alice i)) =
          Kgap * (∑ i : Fin d, ∑ j : Fin d,
            coefficient i j * gap i j) +
          Kmass * (∑ i : Fin d, ∑ j : Fin d,
            coefficient i j * alice i)
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      · apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = _ := by
      rw [
        dSVDensityRationalHeterogeneousCommonStopSpectralRankGap_eq_hazard
          grid dimension w ξ ζ,
        dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass_eq_diagonalBorn
          grid dimension w ξ ζ]

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

def dSVDensityRationalHeterogeneousCommonStopGaugeStageError
    {d N B : ℕ} (Q : ℕ) (w : ℝ) (n : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) : ℝ :=
  ‖dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
        Q w ξ ζ A C
        (dSVDensityRationalPublicBucketPhysicalCoherentMixedState
          (N := N) (B := B) w n ξ ζ) -
      dSVDensityRationalPublicBucketPhysicalCoherentTargetState
        (N := N) (B := B) w n ξ ζ‖ ^ 2

def dSVDensityRationalHeterogeneousStoppedCommonStopGaugeError
    {d N B S L : ℕ} (Q : ℕ) (n : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) : ℝ :=
  ∑ k : Fin L,
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k.val *
      dSVDensityRationalHeterogeneousCommonStopGaugeStageError
        Q (width (schedule k)) n ξ ζ A C

theorem
    dSVDensityRationalHeterogeneousPhysicalDiagonalSurvival_budget
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    (∑ k : Fin L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k.val *
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule k)) ξ) ≤ 1 := by
  calc
    _ ≤ ∑ k : Fin L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k.val *
        (dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k.val +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k.val) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (dSVDensityRationalHeterogeneousPhysicalStage_escape_ge_diagonal
          grid dimension width schedule ξ ζ k)
        (dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
          N width schedule ξ ζ k.val)
    _ = ∑ k ∈ Finset.range L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        (dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k) := by
      simpa using
        (Fin.sum_univ_eq_sum_range
          (fun k : ℕ =>
            dSVDensityRationalHeterogeneousPhysicalSurvival
                N width schedule ξ ζ k *
              (dSVDensityRationalHeterogeneousPhysicalStageSuccess
                  N width schedule ξ ζ k +
                dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
                  N width schedule ξ ζ k)) L)
    _ ≤ 1 :=
      dSVDensityRationalHeterogeneousPhysicalStoppedEscape_budget
        grid dimension width schedule ξ ζ

theorem
    exists_proofDSVDensityRationalHeterogeneousStoppedCommonStopGaugeErrorBound
    {d N B : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (phases : 0 < B) {Q : ℕ} (fine : 0 < Q)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ {S L : ℕ}
          (width : Fin S → ℝ) (schedule : Fin L → Fin S)
          (ξ ζ : BipartiteUnitVector d),
          dSVDensityRationalHeterogeneousStoppedCommonStopGaugeError
              Q n width schedule ξ ζ A C ≤
            (10 + 8 * ((Q : ℝ) / (B : ℝ))) *
                dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
                  N width schedule ξ ζ +
              (4 * ε ^ 2 +
                16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
                8 / (B : ℝ)) := by
  obtain ⟨n, harmonic, A, C, stage⟩ :=
    exists_proofDSVDensityRationalHeterogeneousCommonStopSpectralGaugeContinuity_sq
      grid dimension phases fine ε precision
  let Kgap : ℝ := 10 + 8 * ((Q : ℝ) / (B : ℝ))
  let Kmass : ℝ :=
    4 * ε ^ 2 +
      16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
      8 / (B : ℝ)
  have exponent_nonnegative : 0 ≤ (((B : ℝ) + 1) / (Q : ℝ)) := by
    positivity
  have exponential_nonnegative :
      0 ≤ Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1 := by
    have exponential := Real.add_one_le_exp
      (((B : ℝ) + 1) / (Q : ℝ))
    linarith
  have Kmass_nonnegative : 0 ≤ Kmass := by
    dsimp [Kmass]
    positivity
  refine ⟨n, harmonic, A, C, ?_⟩
  intro S L width schedule ξ ζ
  have diagonal_budget :=
    dSVDensityRationalHeterogeneousPhysicalDiagonalSurvival_budget
      grid dimension width schedule ξ ζ
  unfold dSVDensityRationalHeterogeneousStoppedCommonStopGaugeError
  change
    (∑ k : Fin L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k.val *
        dSVDensityRationalHeterogeneousCommonStopGaugeStageError
          Q (width (schedule k)) n ξ ζ A C) ≤
      Kgap *
          dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
            N width schedule ξ ζ + Kmass
  calc
    _ ≤ ∑ k : Fin L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k.val *
        (Kgap *
            dSVDensityRationalPhysicalProjectorCrossHazard
              N (width (schedule k)) ξ ζ +
          Kmass *
            dSVDensityRationalPhysicalDiagonalBornSuccess
              grid dimension (width (schedule k)) ξ) := by
      apply Finset.sum_le_sum
      intro k _
      have stage_bound := stage width schedule ξ ζ k
      change
        dSVDensityRationalHeterogeneousCommonStopGaugeStageError
            Q (width (schedule k)) n ξ ζ A C ≤
          Kgap *
              dSVDensityRationalPhysicalProjectorCrossHazard
                N (width (schedule k)) ξ ζ +
            Kmass *
              dSVDensityRationalPhysicalDiagonalBornSuccess
                grid dimension (width (schedule k)) ξ at stage_bound
      exact mul_le_mul_of_nonneg_left stage_bound
        (dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
          N width schedule ξ ζ k.val)
    _ =
      Kgap *
        (∑ k : Fin L,
          dSVDensityRationalHeterogeneousPhysicalSurvival
              N width schedule ξ ζ k.val *
            dSVDensityRationalPhysicalProjectorCrossHazard
              N (width (schedule k)) ξ ζ) +
      Kmass *
        (∑ k : Fin L,
          dSVDensityRationalHeterogeneousPhysicalSurvival
              N width schedule ξ ζ k.val *
            dSVDensityRationalPhysicalDiagonalBornSuccess
              grid dimension (width (schedule k)) ξ) := by
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = Kgap *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule ξ ζ +
      Kmass *
        (∑ k : Fin L,
          dSVDensityRationalHeterogeneousPhysicalSurvival
              N width schedule ξ ζ k.val *
            dSVDensityRationalPhysicalDiagonalBornSuccess
              grid dimension (width (schedule k)) ξ) := by
      rw [
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_eq_hazard]
    _ ≤ Kgap *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule ξ ζ + Kmass := by
      nlinarith [mul_nonneg Kmass_nonnegative
        (sub_nonneg.mpr diagonal_budget)]

def dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (i : Fin j.val) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
       DSVUniformDensityThresholdLocalIndex N d) :=
  dSVDensityRationalCompleteProjectiveOutcome
    (width (schedule ⟨i.val, lt_trans i.isLt j.isLt⟩))
    N ξ ζ false false

def dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) :
    EuclideanSpace ℂ
      (Fin j.val →
        (DSVUniformDensityThresholdLocalIndex N d ×
         DSVUniformDensityThresholdLocalIndex N d)) :=
  finiteTensorVector
    (dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
      width schedule ξ ζ j)

theorem
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy_eq_actual
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (i : Fin j.val) :
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
        (N := N) width schedule ξ ζ j i =
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
        width schedule ξ ζ j
        ⟨i.val, by omega⟩ := by
  symm
  exact
    dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_before
      width schedule ξ ζ j ⟨i.val, by omega⟩ i.isLt

theorem
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_apply
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (q : Fin j.val →
      (DSVUniformDensityThresholdLocalIndex N d ×
       DSVUniformDensityThresholdLocalIndex N d)) :
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
        width schedule ξ ζ j q =
      ∏ i : Fin j.val,
        dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          ⟨i.val, by omega⟩ (q i) := by
  change
    (∏ i : Fin j.val,
      dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
        width schedule ξ ζ j i (q i)) = _
  apply Finset.prod_congr rfl
  intro i _
  rw [dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy_eq_actual]

theorem
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_norm_sq
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) :
    ‖dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
        (N := N) width schedule ξ ζ j‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ j.val := by
  rw [dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector,
    finiteTensorVector_norm_sq]
  unfold dSVDensityRationalHeterogeneousPhysicalSurvival
    dSVHeterogeneousRealPrefix
  calc
    (∏ i : Fin j.val,
      ‖dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
        width schedule ξ ζ j i‖ ^ 2) =
        ∏ i : Fin j.val,
          dSVDensityRationalHeterogeneousPhysicalStageContinue
            N width schedule ξ ζ i.val := by
      apply Finset.prod_congr rfl
      intro i _
      simp [dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy,
        dSVDensityRationalHeterogeneousPhysicalStageContinue,
        dSVDensityRationalHeterogeneousPhysicalStageOutcome,
        lt_trans i.isLt j.isLt]
    _ = _ :=
      Fin.prod_univ_eq_prod_range
        (dSVDensityRationalHeterogeneousPhysicalStageContinue
          N width schedule ξ ζ) j.val

def dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
    {d N B S L : ℕ} (Q n : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) : ℝ :=
  ∑ j : Fin L,
    ‖dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
          (N := N) width schedule ξ ζ j‖ ^ 2 *
      dSVDensityRationalHeterogeneousCommonStopGaugeStageError
        Q (width (schedule j)) n ξ ζ A C

theorem
    dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard_eq_gaugeError
    {d N B S L : ℕ} (Q n : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) :
    dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
        Q n width schedule ξ ζ A C =
      dSVDensityRationalHeterogeneousStoppedCommonStopGaugeError
        Q n width schedule ξ ζ A C := by
  unfold dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
    dSVDensityRationalHeterogeneousStoppedCommonStopGaugeError
  simp_rw [
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_norm_sq]

theorem
    exists_proofDSVDensityRationalHeterogeneousStoppedCommonPrefixHazardBound
    {d N B : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (phases : 0 < B) {Q : ℕ} (fine : 0 < Q)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ {S L : ℕ}
          (width : Fin S → ℝ) (schedule : Fin L → Fin S)
          (ξ ζ : BipartiteUnitVector d),
          dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
              Q n width schedule ξ ζ A C ≤
            (10 + 8 * ((Q : ℝ) / (B : ℝ))) *
                dSVDensityRationalHeterogeneousActualAsynchronousFlagMass
                  N width schedule ξ ζ +
              (4 * ε ^ 2 +
                16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
                8 / (B : ℝ)) := by
  obtain ⟨n, harmonic, A, C, bound⟩ :=
    exists_proofDSVDensityRationalHeterogeneousStoppedCommonStopGaugeErrorBound
      grid dimension phases fine ε precision
  refine ⟨n, harmonic, A, C, ?_⟩
  intro S L width schedule ξ ζ
  rw [dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard_eq_gaugeError,
    dSVDensityRationalHeterogeneousActualAsynchronousFlagMass_eq_stoppedAsynchronousMass
      grid dimension width schedule ξ ζ]
  exact bound width schedule ξ ζ

end

noncomputable section

theorem unconditionalPublicBucket_exp_sub_one_le
    {u : ℝ} (nonnegative : 0 ≤ u) (bounded : u ≤ 1) :
    Real.exp u - 1 ≤ (Real.exp 1 - 1) * u := by
  have chord := convexOn_exp.2
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (sub_nonneg.mpr bounded) nonnegative
    (show (1 - u) + u = (1 : ℝ) by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one,
    Real.exp_zero] at chord
  nlinarith

def unconditionalPublicBucketLoss
    (B Q : ℕ) (asynchronous precision : ℝ) : ℝ :=
  (10 + 8 * ((Q : ℝ) / (B : ℝ))) * asynchronous +
    (4 * precision ^ 2 +
      16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
      8 / (B : ℝ))

theorem exists_proofUnconditionalPublicBucketBalance
    (t : ℝ) (positive : 0 < t) (bounded : t ≤ 1) :
    ∃ B Q : ℕ, 0 < B ∧ 0 < Q ∧
      (1 / (B : ℝ) ≤ t / 2) ∧
      ((Q : ℝ) / (B : ℝ) ≤ 3 / t) ∧
      (((B : ℝ) + 1) / (Q : ℝ) ≤ t) ∧
      (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1 ≤
        (Real.exp 1 - 1) * t) ∧
      ∀ asynchronous precision : ℝ, 0 ≤ asynchronous →
        unconditionalPublicBucketLoss B Q asynchronous precision ≤
          (34 / t) * asynchronous + 4 * precision ^ 2 +
            (16 * (Real.exp 1 - 1) + 4) * t := by
  let B : ℕ := ⌈(2 : ℝ) / t⌉₊
  let Q : ℕ := B ^ 2
  have B_positive : 0 < B := by
    dsimp [B]
    exact Nat.ceil_pos.mpr (div_pos (by norm_num) positive)
  have B_real_positive : 0 < (B : ℝ) := by
    exact_mod_cast B_positive
  have Q_positive : 0 < Q := pow_pos B_positive 2
  have Q_real_positive : 0 < (Q : ℝ) := by
    exact_mod_cast Q_positive
  have lower : 2 / t ≤ (B : ℝ) := by
    exact Nat.le_ceil ((2 : ℝ) / t)
  have product_lower : (2 : ℝ) ≤ (B : ℝ) * t :=
    (div_le_iff₀ positive).mp lower
  have inverse_bound : 1 / (B : ℝ) ≤ t / 2 := by
    apply (div_le_iff₀ B_real_positive).mpr
    nlinarith
  have ceiling_upper : (B : ℝ) < 2 / t + 1 := by
    exact Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 / t)
  have product_upper : (B : ℝ) * t < 2 + t := by
    calc
      (B : ℝ) * t < (2 / t + 1) * t :=
        mul_lt_mul_of_pos_right ceiling_upper positive
      _ = 2 + t := by field_simp
  have B_upper : (B : ℝ) ≤ 3 / t := by
    apply (le_div_iff₀ positive).mpr
    nlinarith
  have ratio_eq : (Q : ℝ) / (B : ℝ) = (B : ℝ) := by
    dsimp [Q]
    push_cast
    field_simp
  have ratio_bound : (Q : ℝ) / (B : ℝ) ≤ 3 / t :=
    ratio_eq.trans_le B_upper
  have B_at_least_one : (1 : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast B_positive
  have width_bound : ((B : ℝ) + 1) / (Q : ℝ) ≤ t := by
    apply (div_le_iff₀ Q_real_positive).mpr
    have multiply :=
      mul_le_mul_of_nonneg_right product_lower B_real_positive.le
    have Q_real : (Q : ℝ) = (B : ℝ) ^ 2 := by
      simp [Q]
    rw [Q_real]
    nlinarith
  have width_nonnegative :
      0 ≤ ((B : ℝ) + 1) / (Q : ℝ) := by positivity
  have exponential_bound :
      Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1 ≤
        (Real.exp 1 - 1) * t := by
    calc
      Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1 ≤
          (Real.exp 1 - 1) * (((B : ℝ) + 1) / (Q : ℝ)) :=
        unconditionalPublicBucket_exp_sub_one_le
          width_nonnegative (width_bound.trans bounded)
      _ ≤ (Real.exp 1 - 1) * t := by
        have coefficient : 0 ≤ Real.exp 1 - 1 := by
          nlinarith [Real.add_one_le_exp (1 : ℝ)]
        exact mul_le_mul_of_nonneg_left width_bound coefficient
  refine ⟨B, Q, B_positive, Q_positive, inverse_bound,
    ratio_bound, width_bound, exponential_bound, ?_⟩
  intro asynchronous precision asynchronous_nonnegative
  have reciprocal : 8 / (B : ℝ) ≤ 4 * t := by
    have scale := mul_le_mul_of_nonneg_left inverse_bound
      (by norm_num : (0 : ℝ) ≤ 8)
    calc
      8 / (B : ℝ) = 8 * (1 / (B : ℝ)) := by ring
      _ ≤ 8 * (t / 2) := scale
      _ = 4 * t := by ring
  have ratio_cost :
      (10 + 8 * ((Q : ℝ) / (B : ℝ))) * asynchronous ≤
        (34 / t) * asynchronous := by
    apply mul_le_mul_of_nonneg_right _ asynchronous_nonnegative
    have t_inverse : (1 : ℝ) ≤ 1 / t := by
      apply (le_div_iff₀ positive).mpr
      simpa using bounded
    have ratio_scaled :=
      mul_le_mul_of_nonneg_left ratio_bound
        (by norm_num : (0 : ℝ) ≤ 8)
    have ten_scaled :=
      mul_le_mul_of_nonneg_left t_inverse
        (by norm_num : (0 : ℝ) ≤ 10)
    have ten_piece : (10 : ℝ) ≤ 10 / t := by
      calc
        (10 : ℝ) = 10 * 1 := by ring
        _ ≤ 10 * (1 / t) := ten_scaled
        _ = 10 / t := by ring
    have ratio_piece :
        8 * ((Q : ℝ) / (B : ℝ)) ≤ 24 / t := by
      calc
        8 * ((Q : ℝ) / (B : ℝ)) ≤ 8 * (3 / t) := ratio_scaled
        _ = 24 / t := by ring
    calc
      10 + 8 * ((Q : ℝ) / (B : ℝ)) ≤
          10 / t + 24 / t := add_le_add ten_piece ratio_piece
      _ = 34 / t := by ring
  have exponential_scaled :=
    mul_le_mul_of_nonneg_left exponential_bound
      (by norm_num : (0 : ℝ) ≤ 16)
  unfold unconditionalPublicBucketLoss
  nlinarith

theorem exists_proofUnconditionalStoppedCommonPrefixBalancedHazard
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (t : ℝ) (positive : 0 < t) (bounded : t ≤ 1)
    (precision : ℝ) (precision_positive : 0 < precision) :
    ∃ B Q n : ℕ, 0 < B ∧ 0 < Q ∧ 0 < n ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ {S L : ℕ}
          (width : Fin S → ℝ) (schedule : Fin L → Fin S)
          (ξ ζ : BipartiteUnitVector d),
          dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
              Q n width schedule ξ ζ A C ≤
            (34 / t) *
                dSVDensityRationalHeterogeneousActualAsynchronousFlagMass
                  N width schedule ξ ζ +
              4 * precision ^ 2 +
                (16 * (Real.exp 1 - 1) + 4) * t := by
  obtain ⟨B, Q, phases, fine, _, _, _, _, balance⟩ :=
    exists_proofUnconditionalPublicBucketBalance t positive bounded
  obtain ⟨n, harmonic, A, C, source⟩ :=
    exists_proofDSVDensityRationalHeterogeneousStoppedCommonPrefixHazardBound
      grid dimension phases fine precision precision_positive
  refine ⟨B, Q, n, phases, fine, harmonic, A, C, ?_⟩
  intro S L width schedule ξ ζ
  have actual := source width schedule ξ ζ
  have asynchronous_nonnegative :
      0 ≤ dSVDensityRationalHeterogeneousActualAsynchronousFlagMass
        N width schedule ξ ζ := by
    exact
      dSVDensityRationalHeterogeneousActualAsynchronousFlagMass_nonneg
        N width schedule ξ ζ
  exact actual.trans
    (balance
      (dSVDensityRationalHeterogeneousActualAsynchronousFlagMass
        N width schedule ξ ζ)
      precision asynchronous_nonnegative)

def unconditionalPrefactorBucketCoefficient : ℝ :=
  16 * (Real.exp 1 - 1) + 4

theorem unconditionalPrefactorBucketCoefficient_nonneg :
    0 ≤ unconditionalPrefactorBucketCoefficient := by
  have exponential := Real.add_one_le_exp (1 : ℝ)
  unfold unconditionalPrefactorBucketCoefficient
  nlinarith

theorem unconditionalPrefactor_fourthRoot_sq
    {a : ℝ} (nonnegative : 0 ≤ a) :
    (a ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt a := by
  calc
    (a ^ (1 / 4 : ℝ)) ^ 2 = a ^ ((1 / 4 : ℝ) * 2) :=
      (Real.rpow_mul_natCast nonnegative (1 / 4 : ℝ) 2).symm
    _ = a ^ (1 / 2 : ℝ) := by norm_num
    _ = Real.sqrt a := (Real.sqrt_eq_rpow a).symm

theorem unconditionalPrefactor_sixtyFour_fourthRoot_le :
    (64 : ℝ) ^ (1 / 4 : ℝ) ≤ 4 := by
  have monotone := Real.rpow_le_rpow
    (by norm_num : (0 : ℝ) ≤ 64)
    (by norm_num : (64 : ℝ) ≤ 256)
    (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ))
  have fourth :
      (256 : ℝ) ^ (1 / 4 : ℝ) = 4 := by
    norm_num
  exact monotone.trans_eq fourth

theorem unconditionalPrefactor_fourthRoot_async_le
    {eta alpha : ℝ}
    (eta_nonnegative : 0 ≤ eta)
    (alpha_nonnegative : 0 ≤ alpha) :
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) ≤
      4 * eta ^ (1 / 8 : ℝ) + alpha ^ (1 / 12 : ℝ) := by
  have asynchronous_nonnegative : 0 ≤ (64 : ℝ) * Real.sqrt eta := by
    positivity
  have precision_nonnegative : 0 ≤ alpha ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg alpha_nonnegative _
  have split := Real.rpow_add_le_add_rpow
    asynchronous_nonnegative precision_nonnegative
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have eta_identity :
      (Real.sqrt eta) ^ (1 / 4 : ℝ) = eta ^ (1 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul eta_nonnegative]
    norm_num
  have alpha_identity :
      (alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) =
        alpha ^ (1 / 12 : ℝ) := by
    rw [← Real.rpow_mul alpha_nonnegative]
    norm_num
  have numerical :=
    unconditionalPrefactor_sixtyFour_fourthRoot_le
  calc
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ)
        ≤ (64 * Real.sqrt eta) ^ (1 / 4 : ℝ) +
          (alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) := split
    _ = (64 : ℝ) ^ (1 / 4 : ℝ) * eta ^ (1 / 8 : ℝ) +
          alpha ^ (1 / 12 : ℝ) := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 64)
            (Real.sqrt_nonneg eta), eta_identity, alpha_identity]
    _ ≤ 4 * eta ^ (1 / 8 : ℝ) + alpha ^ (1 / 12 : ℝ) := by
          gcongr

theorem unconditionalPrefactor_fourthRoot_async_le_twelfth
    {eta alpha : ℝ}
    (eta_nonnegative : 0 ≤ eta)
    (eta_bounded : eta ≤ 1)
    (alpha_nonnegative : 0 ≤ alpha) :
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) ≤
      4 * eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ) := by
  have root_compare : eta ^ (1 / 8 : ℝ) ≤ eta ^ (1 / 12 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge'
      eta_nonnegative eta_bounded
      (by norm_num : (0 : ℝ) ≤ 1 / 12)
      (by norm_num : (1 / 12 : ℝ) ≤ 1 / 8)
  calc
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ)
        ≤ 4 * eta ^ (1 / 8 : ℝ) + alpha ^ (1 / 12 : ℝ) :=
          unconditionalPrefactor_fourthRoot_async_le
            eta_nonnegative alpha_nonnegative
    _ ≤ 4 * eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ) := by
          gcongr

theorem unconditionalPrefactor_balancedHazard_sqrt_le
    {a rho : ℝ}
    (positive : 0 < a)
    (rho_nonnegative : 0 ≤ rho) :
    Real.sqrt
      ((34 / Real.sqrt a) * a + 4 * rho ^ 2 +
        unconditionalPrefactorBucketCoefficient * Real.sqrt a) ≤
      Real.sqrt (34 + unconditionalPrefactorBucketCoefficient) *
          a ^ (1 / 4 : ℝ) + 2 * rho := by
  have root_positive : 0 < Real.sqrt a := Real.sqrt_pos.2 positive
  have root_square : (Real.sqrt a) ^ 2 = a :=
    Real.sq_sqrt positive.le
  have coefficient_nonnegative :=
    unconditionalPrefactorBucketCoefficient_nonneg
  have coefficient_square :
      (Real.sqrt
        (34 + unconditionalPrefactorBucketCoefficient)) ^ 2 =
        34 + unconditionalPrefactorBucketCoefficient :=
    Real.sq_sqrt (by linarith)
  have fourth_square :=
    unconditionalPrefactor_fourthRoot_sq positive.le
  have product_square :
      (Real.sqrt (34 + unconditionalPrefactorBucketCoefficient) *
        a ^ (1 / 4 : ℝ)) ^ 2 =
        (34 + unconditionalPrefactorBucketCoefficient) *
          Real.sqrt a := by
    calc
      (Real.sqrt (34 + unconditionalPrefactorBucketCoefficient) *
        a ^ (1 / 4 : ℝ)) ^ 2 =
          (Real.sqrt (34 +
            unconditionalPrefactorBucketCoefficient)) ^ 2 *
            (a ^ (1 / 4 : ℝ)) ^ 2 := by ring
      _ = (34 + unconditionalPrefactorBucketCoefficient) *
          Real.sqrt a := by rw [coefficient_square, fourth_square]
  have quotient : (34 / Real.sqrt a) * a = 34 * Real.sqrt a := by
    field_simp [ne_of_gt root_positive]
    nlinarith [root_square]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [quotient]
    have cross_nonnegative :
        0 ≤ (Real.sqrt
          (34 + unconditionalPrefactorBucketCoefficient) *
          a ^ (1 / 4 : ℝ)) * rho :=
      mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _)
          (Real.rpow_nonneg positive.le _))
        rho_nonnegative
    nlinarith [product_square]

theorem unconditionalPrefactor_smallHazard_twelfthRoot_le
    {eta alpha : ℝ}
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (small : 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1) :
    Real.sqrt
      ((34 / Real.sqrt
          (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) *
          (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) +
        4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
        unconditionalPrefactorBucketCoefficient *
          Real.sqrt
            (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) ≤
      (4 * Real.sqrt
          (34 + unconditionalPrefactorBucketCoefficient) + 2) *
        (eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ)) := by
  let a : ℝ := 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)
  let rho : ℝ := alpha ^ (1 / 12 : ℝ)
  have alpha_third_positive : 0 < alpha ^ (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos alpha_positive _
  have a_positive : 0 < a := by
    dsimp [a]
    have := Real.sqrt_nonneg eta
    linarith
  have eta_root_square : (Real.sqrt eta) ^ 2 = eta :=
    Real.sq_sqrt eta_nonnegative
  have eta_bounded : eta ≤ 1 := by
    have eta_root_bounded : Real.sqrt eta ≤ 1 := by
      nlinarith [Real.sqrt_nonneg eta, alpha_third_positive]
    nlinarith [Real.sqrt_nonneg eta]
  have rho_nonnegative : 0 ≤ rho := by
    dsimp [rho]
    exact Real.rpow_nonneg alpha_positive.le _
  have eta_twelfth_nonnegative : 0 ≤ eta ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg eta_nonnegative _
  have quarter :=
    unconditionalPrefactor_fourthRoot_async_le_twelfth
      eta_nonnegative eta_bounded alpha_positive.le
  have balanced :=
    unconditionalPrefactor_balancedHazard_sqrt_le
      a_positive rho_nonnegative
  have coefficient_root_nonnegative :
      0 ≤ Real.sqrt
        (34 + unconditionalPrefactorBucketCoefficient) :=
    Real.sqrt_nonneg _
  change
    Real.sqrt
      ((34 / Real.sqrt a) * a + 4 * rho ^ 2 +
        unconditionalPrefactorBucketCoefficient * Real.sqrt a) ≤
      (4 * Real.sqrt
          (34 + unconditionalPrefactorBucketCoefficient) + 2) *
        (eta ^ (1 / 12 : ℝ) + rho)
  change a ^ (1 / 4 : ℝ) ≤
    4 * eta ^ (1 / 12 : ℝ) + rho at quarter
  nlinarith [mul_nonneg coefficient_root_nonnegative
    (sub_nonneg.mpr quarter),
    mul_nonneg coefficient_root_nonnegative rho_nonnegative,
    mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num)
      eta_twelfth_nonnegative]

theorem unconditionalPrefactor_largeVerifier_twelfthRoot_le
    {eta alpha : ℝ}
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (large : 1 < 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) :
    (2 : ℝ) ≤
      128 * (eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ)) := by
  have eta_root_nonnegative : 0 ≤ eta ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg eta_nonnegative _
  have alpha_root_nonnegative : 0 ≤ alpha ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg alpha_positive.le _
  by_cases eta_bounded : eta ≤ 1
  · have eta_root_compare :
        Real.sqrt eta ≤ eta ^ (1 / 12 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge'
        eta_nonnegative eta_bounded
        (by norm_num : (0 : ℝ) ≤ 1 / 12)
        (by norm_num : (1 / 12 : ℝ) ≤ 1 / 2)
    have alpha_root_compare :
        alpha ^ (1 / 3 : ℝ) ≤ alpha ^ (1 / 12 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge'
        alpha_positive.le alpha_bounded
        (by norm_num : (0 : ℝ) ≤ 1 / 12)
        (by norm_num : (1 / 12 : ℝ) ≤ 1 / 3)
    nlinarith
  · have eta_large : 1 ≤ eta := (lt_of_not_ge eta_bounded).le
    have eta_root_large : 1 ≤ eta ^ (1 / 12 : ℝ) :=
      Real.one_le_rpow eta_large (by norm_num : (0 : ℝ) ≤ 1 / 12)
    nlinarith

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalExactSourceScalarClipping
    (d : ℕ) (dimension : 0 < d)
    (alpha : ℝ) (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1) :
    ∃ (w : ℝ) (N : ℕ),
      1 ≤ w ∧ 0 < N ∧
      2 * (w + 1) * ((d : ℝ) / N) ≤ alpha ^ (1 / 3 : ℝ) ∧
      (1 / w + (d : ℝ) * w / (N : ℝ) ≤
        3 * alpha ^ (1 / 3 : ℝ) / 2) ∧
      (∀ ξ : BipartiteUnitVector d,
        ‖ξ.val - dSVDensityRationalCanonicalAcceptedTarget
            w N ξ‖ ^ 2 ≤ 3 * alpha ^ (1 / 3 : ℝ) / 2) ∧
      (∀ ξ ζ : BipartiteUnitVector d,
        dSVDensityRationalLeftProjectiveThresholdAtomMismatch
            w N ξ ζ /
          dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≤
            8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
              alpha ^ (1 / 3 : ℝ)) := by
  have precision : 0 < alpha ^ (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos alpha_positive _
  have small : alpha ^ (1 / 3 : ℝ) ≤ 1 :=
    Real.rpow_le_one alpha_positive.le alpha_bounded (by norm_num)
  obtain ⟨w, N, width, grid, fine, rounding, _diagonal, mismatch⟩ :=
    dSVDensityRationalLargeWidth_exists_sourceUniformParameters
      d dimension (alpha ^ (1 / 3 : ℝ)) precision small
  have scalar :
      1 / w + (d : ℝ) * w / (N : ℝ) ≤
        3 * alpha ^ (1 / 3 : ℝ) / 2 := by
    calc
      1 / w + (d : ℝ) * w / (N : ℝ) =
          1 / w + w * ((d : ℝ) / N) := by ring
      _ ≤ 3 * alpha ^ (1 / 3 : ℝ) / 2 := rounding
  refine ⟨w, N, width, grid, fine, scalar, ?_, mismatch⟩
  intro ξ
  exact
    (dSVDensityRationalCanonicalAcceptedTarget_distance_sq_le
      (by linarith) grid ξ).trans scalar

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactLocalQuestionHistoryEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    (LocalQuestionContext X Y D ×
      ExactHistoryFlag X Y A B D) ≃
      ExactLocallySampleableTuple X Y A B D where
  toFun t := (t.1.1, t.1.2.1, t.1.2.2, t.2)
  invFun t := ((t.1, t.2.1, t.2.2.1), t.2.2.2)
  left_inv t := by
    rcases t with ⟨⟨i, x, y⟩, r⟩
    rfl
  right_inv t := by
    rcases t with ⟨i, x, y, r⟩
    rfl

def exactLocallySampleableJARounded
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  G.questionWeight t.2.1 t.2.2.1 *
    ((numerator (.inl (t.1, t.2.1)) t.2.2.2 : ℝ) /
      denominator) /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

def exactLocallySampleableJBRounded
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  G.questionWeight t.2.1 t.2.2.1 *
    ((numerator (.inr (t.1, t.2.2.1)) t.2.2.2 : ℝ) /
      denominator) /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

theorem exactLocallySampleableJA_weightedConditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) :
    (exactLocallySampleableJA G n S D base ∘
      exactLocalQuestionHistoryEquiv D) =
      weightedConditionalJoint
        (localQuestionWeight G n D)
        (fun c r => exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D)
          c.1 c.2.1 r) := by
  funext t
  rcases t with ⟨⟨i, x, y⟩, r⟩
  change
    G.questionWeight x y *
      exactAliceLocalConditional D base
        (exactLocallySampleableLaw G n S D) i x r /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) =
      (G.questionWeight x y /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D) i x r
  ring

theorem exactLocallySampleableJB_weightedConditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) :
    (exactLocallySampleableJB G n S D base ∘
      exactLocalQuestionHistoryEquiv D) =
      weightedConditionalJoint
        (localQuestionWeight G n D)
        (fun c r => exactBobLocalConditional D base
          (exactLocallySampleableLaw G n S D)
          c.1 c.2.2 r) := by
  funext t
  rcases t with ⟨⟨i, x, y⟩, r⟩
  change
    G.questionWeight x y *
      exactBobLocalConditional D base
        (exactLocallySampleableLaw G n S D) i y r /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) =
      (G.questionWeight x y /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        exactBobLocalConditional D base
          (exactLocallySampleableLaw G n S D) i y r
  ring

theorem exactLocallySampleableJARounded_weightedConditional
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ) :
    (exactLocallySampleableJARounded
      G n D denominator numerator ∘
        exactLocalQuestionHistoryEquiv D) =
      weightedConditionalJoint
        (localQuestionWeight G n D)
        (fun c r =>
          (numerator (.inl (c.1, c.2.1)) r : ℝ) / denominator) := by
  funext t
  rcases t with ⟨⟨i, x, y⟩, r⟩
  change
    G.questionWeight x y *
      ((numerator (.inl (i, x)) r : ℝ) / denominator) /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) =
      (G.questionWeight x y /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ((numerator (.inl (i, x)) r : ℝ) / denominator)
  ring

theorem exactLocallySampleableJBRounded_weightedConditional
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ) :
    (exactLocallySampleableJBRounded
      G n D denominator numerator ∘
        exactLocalQuestionHistoryEquiv D) =
      weightedConditionalJoint
        (localQuestionWeight G n D)
        (fun c r =>
          (numerator (.inr (c.1, c.2.2)) r : ℝ) / denominator) := by
  funext t
  rcases t with ⟨⟨i, x, y⟩, r⟩
  change
    G.questionWeight x y *
      ((numerator (.inr (i, y)) r : ℝ) / denominator) /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) =
      (G.questionWeight x y /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ((numerator (.inr (i, y)) r : ℝ) / denominator)
  ring

theorem exactLocallySampleableJA_rounded_totalVariation_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    {gamma : ℝ}
    (approximation : ∀ k, finiteTotalVariation
      (exactLocalConditionalFamily D base
        (exactLocallySampleableLaw G n S D) k)
      (fun r => (numerator k r : ℝ) / denominator) < gamma) :
    finiteTotalVariation
        (exactLocallySampleableJA G n S D base)
        (exactLocallySampleableJARounded
          G n D denominator numerator) ≤ gamma := by
  calc
    finiteTotalVariation
        (exactLocallySampleableJA G n S D base)
        (exactLocallySampleableJARounded
          G n D denominator numerator) =
      finiteTotalVariation
        (exactLocallySampleableJA G n S D base ∘
          exactLocalQuestionHistoryEquiv D)
        (exactLocallySampleableJARounded
          G n D denominator numerator ∘
          exactLocalQuestionHistoryEquiv D) :=
      (finiteTotalVariation_equiv
        (exactLocalQuestionHistoryEquiv D)
        (exactLocallySampleableJA G n S D base)
        (exactLocallySampleableJARounded
          G n D denominator numerator)).symm
    _ = ∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c *
          finiteTotalVariation
            (fun r => exactAliceLocalConditional D base
              (exactLocallySampleableLaw G n S D)
              c.1 c.2.1 r)
            (fun r =>
              (numerator (.inl (c.1, c.2.1)) r : ℝ) /
                denominator) := by
      rw [exactLocallySampleableJA_weightedConditional,
        exactLocallySampleableJARounded_weightedConditional,
        weightedConditionalJoint_totalVariation
          (localQuestionWeight G n D)
          (localQuestionWeight_nonneg G n D)]
    _ ≤ ∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c * gamma := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _
        (localQuestionWeight_nonneg G n D c)
      exact (approximation (.inl (c.1, c.2.1))).le
    _ = gamma := by
      rw [← Finset.sum_mul,
        localQuestionWeight_sum G n D remaining]
      ring

theorem exactLocallySampleableJB_rounded_totalVariation_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    {gamma : ℝ}
    (approximation : ∀ k, finiteTotalVariation
      (exactLocalConditionalFamily D base
        (exactLocallySampleableLaw G n S D) k)
      (fun r => (numerator k r : ℝ) / denominator) < gamma) :
    finiteTotalVariation
        (exactLocallySampleableJB G n S D base)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) ≤ gamma := by
  calc
    finiteTotalVariation
        (exactLocallySampleableJB G n S D base)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) =
      finiteTotalVariation
        (exactLocallySampleableJB G n S D base ∘
          exactLocalQuestionHistoryEquiv D)
        (exactLocallySampleableJBRounded
          G n D denominator numerator ∘
          exactLocalQuestionHistoryEquiv D) :=
      (finiteTotalVariation_equiv
        (exactLocalQuestionHistoryEquiv D)
        (exactLocallySampleableJB G n S D base)
        (exactLocallySampleableJBRounded
          G n D denominator numerator)).symm
    _ = ∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c *
          finiteTotalVariation
            (fun r => exactBobLocalConditional D base
              (exactLocallySampleableLaw G n S D)
              c.1 c.2.2 r)
            (fun r =>
              (numerator (.inr (c.1, c.2.2)) r : ℝ) /
                denominator) := by
      rw [exactLocallySampleableJB_weightedConditional,
        exactLocallySampleableJBRounded_weightedConditional,
        weightedConditionalJoint_totalVariation
          (localQuestionWeight G n D)
          (localQuestionWeight_nonneg G n D)]
    _ ≤ ∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c * gamma := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _
        (localQuestionWeight_nonneg G n D c)
      exact (approximation (.inr (c.1, c.2.2))).le
    _ = gamma := by
      rw [← Finset.sum_mul,
        localQuestionWeight_sum G n D remaining]
      ring

theorem exactLocallySampleableRounded_pair_totalVariation
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ) :
    finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) =
      ∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c *
          finiteTotalVariation
            (fun r =>
              (numerator (.inl (c.1, c.2.1)) r : ℝ) / denominator)
            (fun r =>
              (numerator (.inr (c.1, c.2.2)) r : ℝ) / denominator) := by
  calc
    finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) =
      finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator ∘
          exactLocalQuestionHistoryEquiv D)
        (exactLocallySampleableJBRounded
          G n D denominator numerator ∘
          exactLocalQuestionHistoryEquiv D) :=
      (finiteTotalVariation_equiv
        (exactLocalQuestionHistoryEquiv D)
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableJBRounded
          G n D denominator numerator)).symm
    _ = _ := by
      rw [exactLocallySampleableJARounded_weightedConditional,
        exactLocallySampleableJBRounded_weightedConditional,
        weightedConditionalJoint_totalVariation
          (localQuestionWeight G n D)
          (localQuestionWeight_nonneg G n D)]

def exactLocallySampleablePermutationMismatch
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty) : ℝ :=
  ∑ c : LocalQuestionContext X Y D,
    localQuestionWeight G n D c *
      uniformPermutationProbability
        (fun permutation :
          Equiv.Perm
            (ExactHistoryFlag X Y A B D × Fin denominator) =>
          rationalPermutationOutput denominator
              (numerator (.inl (c.1, c.2.1)))
              (nonempty (.inl (c.1, c.2.1))) permutation ≠
            rationalPermutationOutput denominator
              (numerator (.inr (c.1, c.2.2)))
              (nonempty (.inr (c.1, c.2.2))) permutation)

theorem exactLocallySampleablePermutationMismatch_le_two_tv
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ) (positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ k, (∑ r, numerator k r) = denominator)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty) :
    exactLocallySampleablePermutationMismatch
        G n D denominator numerator nonempty ≤
      2 * finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) := by
  unfold exactLocallySampleablePermutationMismatch
  calc
    (∑ c : LocalQuestionContext X Y D,
      localQuestionWeight G n D c *
        uniformPermutationProbability
          (fun permutation :
            Equiv.Perm
              (ExactHistoryFlag X Y A B D × Fin denominator) =>
            rationalPermutationOutput denominator
                (numerator (.inl (c.1, c.2.1)))
                (nonempty (.inl (c.1, c.2.1))) permutation ≠
              rationalPermutationOutput denominator
                (numerator (.inr (c.1, c.2.2)))
                (nonempty (.inr (c.1, c.2.2))) permutation)) ≤
      ∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c *
          (2 * finiteTotalVariation
            (fun r =>
              (numerator (.inl (c.1, c.2.1)) r : ℝ) / denominator)
            (fun r =>
              (numerator (.inr (c.1, c.2.2)) r : ℝ) / denominator)) := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _
        (localQuestionWeight_nonneg G n D c)
      exact rationalPermutationOutput_disagreement_le_two_mul_finiteTotalVariation
        denominator positive
        (numerator (.inl (c.1, c.2.1)))
        (numerator (.inr (c.1, c.2.2)))
        (normalized (.inl (c.1, c.2.1)))
        (normalized (.inr (c.1, c.2.2)))
        (nonempty (.inl (c.1, c.2.1)))
        (nonempty (.inr (c.1, c.2.2)))
    _ = 2 *
      (∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c *
          finiteTotalVariation
            (fun r =>
              (numerator (.inl (c.1, c.2.1)) r : ℝ) / denominator)
            (fun r =>
              (numerator (.inr (c.1, c.2.2)) r : ℝ) / denominator)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = 2 * finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) := by
      rw [exactLocallySampleableRounded_pair_totalVariation]

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

abbrev ExactSourceSharedFlag
    (X Y A B : Type)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ) :=
  SourceRemainingCoordinate D ×
    Equiv.Perm
      (ExactHistoryFlag X Y A B D × Fin denominator)

def exactSourceSharedFlagWeight
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (_ : ExactSourceSharedFlag X Y A B D denominator) : ℝ :=
  (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        (ExactHistoryFlag X Y A B D × Fin denominator)) : ℝ))

theorem exactSourceSharedFlagWeight_nonneg
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (j : ExactSourceSharedFlag X Y A B D denominator) :
    0 ≤ exactSourceSharedFlagWeight D denominator j := by
  unfold exactSourceSharedFlagWeight
  positivity

theorem exactSourceSharedFlagWeight_sum
    {n : ℕ} (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (denominator : ℕ) :
    (∑ j : ExactSourceSharedFlag X Y A B D denominator,
      exactSourceSharedFlagWeight D denominator j) = 1 := by
  classical
  have coordinate_nonzero :
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt (exactRemainingCoordinate_card_pos
        D remaining))
  have permutation_nonzero :
      (Fintype.card
        (Equiv.Perm
          (ExactHistoryFlag X Y A B D × Fin denominator)) : ℝ)
        ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (Fintype.card_pos_iff.mpr
        ⟨Equiv.refl
          (ExactHistoryFlag X Y A B D × Fin denominator)⟩))
  rw [Fintype.sum_prod_type]
  simp only [exactSourceSharedFlagWeight,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

def exactSourceAlicePermutationHistory
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (j : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) : ExactHistoryFlag X Y A B D :=
  rationalPermutationOutput denominator
    (numerator (.inl (j.1, x)))
    (nonempty (.inl (j.1, x))) j.2

def exactSourceBobPermutationHistory
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (j : ExactSourceSharedFlag X Y A B D denominator)
    (y : Y) : ExactHistoryFlag X Y A B D :=
  rationalPermutationOutput denominator
    (numerator (.inr (j.1, y)))
    (nonempty (.inr (j.1, y))) j.2

def exactSourcePermutationMatched
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (ω : ExactSourceSharedFlag X Y A B D denominator ×
      (X × Y)) : Bool := by
  classical
  exact decide
    (exactSourceAlicePermutationHistory
      D denominator numerator nonempty ω.1 ω.2.1 =
      exactSourceBobPermutationHistory
        D denominator numerator nonempty ω.1 ω.2.2)

theorem exactUniformPermutationProbability_eq_indicator_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (event : Equiv.Perm ι → Prop) :
    uniformPermutationProbability event =
      (∑ permutation : Equiv.Perm ι,
        if event permutation then (1 : ℝ) else 0) /
        (Fintype.card (Equiv.Perm ι) : ℝ) := by
  classical
  unfold uniformPermutationProbability
  congr 1
  exact (Finset.sum_boole (R := ℝ) event
    (Finset.univ : Finset (Equiv.Perm ι))).symm

theorem exactSourceSharedFlag_mismatch_eq
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty) :
    (∑ ω :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator) ω *
        if exactSourcePermutationMatched
            D denominator numerator nonempty ω then 0 else 1) =
      exactLocallySampleablePermutationMismatch
        G n D denominator numerator nonempty := by
  classical
  have point
      (i : SourceRemainingCoordinate D) (x : X) (y : Y) :
      (∑ permutation :
        Equiv.Perm
          (ExactHistoryFlag X Y A B D × Fin denominator),
        ((1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
          (1 / (Fintype.card
            (Equiv.Perm
              (ExactHistoryFlag X Y A B D ×
                Fin denominator)) : ℝ))) *
          G.questionWeight x y *
          if rationalPermutationOutput denominator
              (numerator (.inl (i, x)))
              (nonempty (.inl (i, x))) permutation =
            rationalPermutationOutput denominator
              (numerator (.inr (i, y)))
              (nonempty (.inr (i, y))) permutation
          then 0 else 1) =
        (G.questionWeight x y /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
          uniformPermutationProbability
            (fun permutation :
              Equiv.Perm
                (ExactHistoryFlag X Y A B D ×
                  Fin denominator) =>
              rationalPermutationOutput denominator
                  (numerator (.inl (i, x)))
                  (nonempty (.inl (i, x))) permutation ≠
                rationalPermutationOutput denominator
                  (numerator (.inr (i, y)))
                  (nonempty (.inr (i, y))) permutation) := by
    have probability :=
      exactUniformPermutationProbability_eq_indicator_sum
        (ι := ExactHistoryFlag X Y A B D × Fin denominator)
        (fun permutation :
          Equiv.Perm
            (ExactHistoryFlag X Y A B D × Fin denominator) =>
          rationalPermutationOutput denominator
              (numerator (.inl (i, x)))
              (nonempty (.inl (i, x))) permutation ≠
            rationalPermutationOutput denominator
              (numerator (.inr (i, y)))
              (nonempty (.inr (i, y))) permutation)
    rw [probability, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro permutation _
    by_cases matched :
      rationalPermutationOutput denominator
          (numerator (.inl (i, x)))
          (nonempty (.inl (i, x))) permutation =
        rationalPermutationOutput denominator
          (numerator (.inr (i, y)))
          (nonempty (.inr (i, y))) permutation
    · simp [matched]
    · simp [matched]
      ring
  unfold exactLocallySampleablePermutationMismatch
  simp only [flaggedQuestionWeight,
    exactSourceSharedFlagWeight,
    localQuestionWeight,
    exactSourcePermutationMatched,
    exactSourceAlicePermutationHistory,
    exactSourceBobPermutationHistory,
    Fintype.sum_prod_type, decide_eq_true_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  exact point i x y

theorem exactSourceSharedFlag_mismatch_le
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    {lam : ℝ}
    (mismatch :
      exactLocallySampleablePermutationMismatch
        G n D denominator numerator nonempty ≤ 4 * lam) :
    (∑ ω :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator) ω *
        if exactSourcePermutationMatched
            D denominator numerator nonempty ω then 0 else 1) ≤
      4 * lam := by
  rw [exactSourceSharedFlag_mismatch_eq
    G n D denominator numerator nonempty]
  exact mismatch

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem reweightedSeed_reverse_source_prefix_information_budget
    {K V : Type*} [Fintype K] [Fintype V]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (seedLaw : Finset (SourceRemainingCoordinate D) →
      FiniteEventLaw K)
    (Ω : Finset (SourceRemainingCoordinate D) → Type*)
    [∀ side, Fintype (Ω side)]
    (projection : ∀ side : Finset (SourceRemainingCoordinate D),
      K × ExactOutcome X Y A B n →
        Ω side × (Fin side.card → V))
    (default : V) :
    (∑ side : Finset (SourceRemainingCoordinate D),
      reversePartitionWeight side *
        ((∑ k : Fin side.card,
          reweightedSeedPrefixEntropyIncrement
            (seedLaw side) G n S D
            (projection side) default k) /
          (side.card : ℝ))) ≤
      2 * (postselectionLogCost G n S D +
        answerLogCost (A := A) (B := B) D) /
        ((Finset.univ \ D).card : ℝ) := by
  have nonnegative_cost :
      0 ≤ postselectionLogCost G n S D +
        answerLogCost (A := A) (B := B) D := by
    have hempty := reweightedSeed_source_equation_twenty_six
      (seedLaw ∅) G n S D positive (projection ∅) default
    simpa using hempty
  exact exactRemainingReverse_relativeEntropy_budget
    D remaining
    (fun side k => reweightedSeedPrefixEntropyIncrement
      (seedLaw side) G n S D (projection side) default k)
    nonnegative_cost
    (fun side => reweightedSeed_source_equation_twenty_six
      (seedLaw side) G n S D positive (projection side) default)

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

def finiteIndependentProductWeight
    {ι V : Type*} [Fintype ι] [Fintype V]
    (q : ι → V → ℝ) (x : ι → V) : ℝ :=
  ∏ i : ι, q i (x i)

def finiteCoordinateMarginal
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (i : ι) : V → ℝ := by
  classical
  exact groupedMass (fun x : ι → V => x i) p

theorem finiteIndependentProductWeight_nonneg
    {ι V : Type*} [Fintype ι] [Fintype V]
    (q : ι → V → ℝ) (hq : ∀ i v, 0 ≤ q i v)
    (x : ι → V) :
    0 ≤ finiteIndependentProductWeight q x := by
  classical
  unfold finiteIndependentProductWeight
  exact Finset.prod_nonneg fun i _ => hq i (x i)

theorem finiteIndependentProductWeight_sum
    {ι V : Type*} [Fintype ι] [Fintype V]
    (q : ι → V → ℝ)
    (hq : ∀ i, (∑ v : V, q i v) = 1) :
    (∑ x : ι → V, finiteIndependentProductWeight q x) = 1 := by
  classical
  unfold finiteIndependentProductWeight
  calc
    (∑ x : ι → V, ∏ i : ι, q i (x i)) =
        ∏ i : ι, ∑ v : V, q i v :=
      (Fintype.prod_sum (fun i : ι => fun v : V => q i v)).symm
    _ = 1 := by simp [hq]

theorem finiteCoordinateMarginal_nonneg
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (hp : ∀ x, 0 ≤ p x)
    (i : ι) (v : V) :
    0 ≤ finiteCoordinateMarginal p i v := by
  classical
  unfold finiteCoordinateMarginal
  exact groupedMass_nonneg (fun x : ι → V => x i) p hp v

theorem finiteCoordinateMarginal_sum
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (i : ι) :
    (∑ v : V, finiteCoordinateMarginal p i v) =
      ∑ x : ι → V, p x := by
  classical
  unfold finiteCoordinateMarginal
  exact groupedMass_sum (fun x : ι → V => x i) p

theorem finiteJoint_le_coordinateMarginal
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (hp : ∀ x, 0 ≤ p x)
    (x : ι → V) (i : ι) :
    p x ≤ finiteCoordinateMarginal p i (x i) := by
  classical
  unfold finiteCoordinateMarginal groupedMass
  exact Finset.single_le_sum
    (fun a _ => hp a)
    (by simp)

theorem finiteCoordinateMarginal_absolute_continuity
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (q : ι → V → ℝ)
    (hac : ∀ x, finiteIndependentProductWeight q x = 0 → p x = 0)
    (i : ι) (v : V) :
    q i v = 0 → finiteCoordinateMarginal p i v = 0 := by
  classical
  intro hz
  unfold finiteCoordinateMarginal groupedMass
  apply Finset.sum_eq_zero
  intro x hx
  have hxi : x i = v := (Finset.mem_filter.mp hx).2
  apply hac x
  unfold finiteIndependentProductWeight
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa [hxi] using hz

theorem finiteJoint_absolute_continuous_product_marginals
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (hp : ∀ x, 0 ≤ p x)
    (x : ι → V) :
    finiteIndependentProductWeight
        (finiteCoordinateMarginal p) x = 0 → p x = 0 := by
  classical
  intro hz
  by_contra hpx
  have hpositive : 0 < p x :=
    lt_of_le_of_ne (hp x) (Ne.symm hpx)
  have hmarginal (i : ι) :
      0 < finiteCoordinateMarginal p i (x i) :=
    lt_of_lt_of_le hpositive
      (finiteJoint_le_coordinateMarginal p hp x i)
  have hproduct :
      0 < finiteIndependentProductWeight
        (finiteCoordinateMarginal p) x := by
    unfold finiteIndependentProductWeight
    exact Finset.prod_pos fun i _ => hmarginal i
  exact hproduct.ne' hz

theorem finiteCoordinateMarginal_sum_mul
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (i : ι) (f : V → ℝ) :
    (∑ x : ι → V, p x * f (x i)) =
      ∑ v : V, finiteCoordinateMarginal p i v * f v := by
  classical
  calc
    (∑ x : ι → V, p x * f (x i)) =
        ∑ v : V,
          groupedMass (fun x : ι → V => x i)
            (fun x => p x * f (x i)) v := by
      symm
      exact groupedMass_sum
        (fun x : ι → V => x i)
        (fun x => p x * f (x i))
    _ = ∑ v : V, finiteCoordinateMarginal p i v * f v := by
      apply Finset.sum_congr rfl
      intro v _
      unfold finiteCoordinateMarginal groupedMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hxi : x i = v := (Finset.mem_filter.mp hx).2
      simp [hxi]

theorem finiteProductMarginal_relativeEntropy_le
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (q : ι → V → ℝ)
    (hp : ∀ x, 0 ≤ p x)
    (hp_normalized : (∑ x : ι → V, p x) = 1)
    (hq : ∀ i v, 0 ≤ q i v)
    (hq_normalized : ∀ i, (∑ v : V, q i v) = 1)
    (absolute_continuity :
      ∀ x, finiteIndependentProductWeight q x = 0 → p x = 0) :
    (∑ i : ι,
      finiteRelativeEntropy (finiteCoordinateMarginal p i) (q i)) ≤
      finiteRelativeEntropy p (finiteIndependentProductWeight q) := by
  classical
  let marginal : ι → V → ℝ := finiteCoordinateMarginal p
  have hm_nonnegative (i : ι) (v : V) : 0 ≤ marginal i v :=
    finiteCoordinateMarginal_nonneg p hp i v
  have hm_normalized (i : ι) : (∑ v : V, marginal i v) = 1 := by
    change (∑ v : V, finiteCoordinateMarginal p i v) = 1
    rw [finiteCoordinateMarginal_sum, hp_normalized]
  have hm_absolute (x : ι → V) :
      finiteIndependentProductWeight marginal x = 0 → p x = 0 :=
    finiteJoint_absolute_continuous_product_marginals p hp x
  have hq_absolute (i : ι) (v : V) :
      q i v = 0 → marginal i v = 0 :=
    finiteCoordinateMarginal_absolute_continuity
      p q absolute_continuity i v
  have hpoint (x : ι → V) :
      p x * Real.log
        (p x / finiteIndependentProductWeight q x) =
        p x * Real.log
            (p x / finiteIndependentProductWeight marginal x) +
          ∑ i : ι,
            p x * Real.log (marginal i (x i) / q i (x i)) := by
    by_cases hpx : p x = 0
    · simp [hpx]
    · have hp_positive : 0 < p x :=
        lt_of_le_of_ne (hp x) (Ne.symm hpx)
      have hq_product :
          finiteIndependentProductWeight q x ≠ 0 := by
        intro hz
        exact hpx (absolute_continuity x hz)
      have hm_product :
          finiteIndependentProductWeight marginal x ≠ 0 := by
        intro hz
        exact hpx (hm_absolute x hz)
      have hq_factor (i : ι) : q i (x i) ≠ 0 := by
        intro hz
        apply hq_product
        unfold finiteIndependentProductWeight
        exact Finset.prod_eq_zero (Finset.mem_univ i) hz
      have hm_factor (i : ι) : marginal i (x i) ≠ 0 := by
        have hm_positive : 0 < marginal i (x i) :=
          lt_of_lt_of_le hp_positive
            (finiteJoint_le_coordinateMarginal p hp x i)
        exact hm_positive.ne'
      have hlogq :
          Real.log (finiteIndependentProductWeight q x) =
            ∑ i : ι, Real.log (q i (x i)) := by
        unfold finiteIndependentProductWeight
        exact Real.log_prod (fun i _ => hq_factor i)
      have hlogm :
          Real.log (finiteIndependentProductWeight marginal x) =
            ∑ i : ι, Real.log (marginal i (x i)) := by
        unfold finiteIndependentProductWeight
        exact Real.log_prod (fun i _ => hm_factor i)
      rw [Real.log_div hpx hq_product,
        Real.log_div hpx hm_product, hlogq, hlogm]
      simp_rw [Real.log_div (hm_factor _) (hq_factor _)]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      ring
  have hidentity :
      finiteRelativeEntropy p (finiteIndependentProductWeight q) =
        finiteRelativeEntropy p
            (finiteIndependentProductWeight marginal) +
          ∑ i : ι, finiteRelativeEntropy (marginal i) (q i) := by
    rw [finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
      p (finiteIndependentProductWeight q)
      (finiteIndependentProductWeight_nonneg q hq)
      absolute_continuity hp_normalized
      (finiteIndependentProductWeight_sum q hq_normalized)]
    rw [finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
      p (finiteIndependentProductWeight marginal)
      (finiteIndependentProductWeight_nonneg marginal hm_nonnegative)
      hm_absolute hp_normalized
      (finiteIndependentProductWeight_sum marginal hm_normalized)]
    simp_rw [finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
      (marginal _) (q _) (hq _) (hq_absolute _)
      (hm_normalized _) (hq_normalized _)]
    calc
      (∑ x : ι → V, p x *
          Real.log (p x / finiteIndependentProductWeight q x)) =
        ∑ x : ι → V,
          (p x * Real.log
            (p x / finiteIndependentProductWeight marginal x) +
            ∑ i : ι,
              p x * Real.log (marginal i (x i) / q i (x i))) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hpoint x
      _ = (∑ x : ι → V, p x *
            Real.log
              (p x / finiteIndependentProductWeight marginal x)) +
          ∑ i : ι,
            ∑ x : ι → V,
              p x * Real.log (marginal i (x i) / q i (x i)) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
      _ = (∑ x : ι → V, p x *
            Real.log
              (p x / finiteIndependentProductWeight marginal x)) +
          ∑ i : ι,
            ∑ v : V,
              marginal i v * Real.log (marginal i v / q i v) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact finiteCoordinateMarginal_sum_mul
            p i (fun v => Real.log (marginal i v / q i v))
  rw [hidentity]
  have hnonnegative :
      0 ≤ finiteRelativeEntropy p
        (finiteIndependentProductWeight marginal) :=
    finiteRelativeEntropy_nonneg p
      (finiteIndependentProductWeight marginal)
      hp (finiteIndependentProductWeight_nonneg
        marginal hm_nonnegative)
  change (∑ i : ι, finiteRelativeEntropy (marginal i) (q i)) ≤ _
  linarith

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactIndependentCoordinateQuestion_marginal
    {M Ω V : Type*} [Fintype M] [DecidableEq M]
    [Fintype Ω] [Fintype V]
    (outcome : Ω → ℝ) (question : Ω → M → V)
    (i : M) (v : V) :
    groupedMass
        (fun t : ExactForwardSeed M × Ω =>
          (t.1.coordinate, question t.2 t.1.coordinate))
        (fun t : ExactForwardSeed M × Ω =>
          exactSeedWeight t.1 * outcome t.2) (i, v) =
      (1 / (Fintype.card M : ℝ)) *
        groupedMass (fun ω : Ω => question ω i) outcome v := by
  classical
  let coordinateMass :=
    groupedMass (fun ω : Ω => question ω i) outcome v
  have hinner (seed : ExactForwardSeed M) :
      (∑ ω : Ω,
        if (seed.coordinate, question ω seed.coordinate) = (i, v)
        then exactSeedWeight seed * outcome ω
        else 0) =
      if seed.coordinate = i
      then exactSeedWeight seed * coordinateMass
      else 0 := by
    by_cases hc : seed.coordinate = i
    · subst i
      simp only [Prod.mk.injEq, true_and, ↓reduceIte]
      dsimp [coordinateMass]
      unfold groupedMass
      rw [Finset.sum_filter]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      split_ifs <;> simp_all
    · simp [hc]
  unfold groupedMass
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [hinner]
  calc
    (∑ seed : ExactForwardSeed M,
      if seed.coordinate = i
      then exactSeedWeight seed * coordinateMass
      else 0) =
        (∑ seed : ExactForwardSeed M,
          if seed.coordinate = i
          then exactSeedWeight seed else 0) * coordinateMass := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro seed _
          split_ifs <;> simp
    _ = (1 / (Fintype.card M : ℝ)) * coordinateMass := by
      rw [exactSeedWeight_coordinate_marginal i]

theorem strategyAliceQuestionPrior_marginal
    (G : Game X Y A B) (S : Strategy G) (x : X) :
    groupedMass (fun ω : StrategyOutcome X Y A B => ω.1)
        (strategyEventLaw G S).weight x =
      G.marginalX x := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  change
    (∑ x' : X, ∑ y : Y, ∑ a : A, ∑ b : B,
      if x' = x then
        G.questionWeight x' y * S.outcomeProbability x' y a b
      else 0) = G.marginalX x
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  unfold Game.marginalX
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [← Finset.mul_sum]
  rw [S.outcomeProbability_normalized x y]
  ring

theorem strategyBobQuestionPrior_marginal
    (G : Game X Y A B) (S : Strategy G) (y : Y) :
    groupedMass (fun ω : StrategyOutcome X Y A B => ω.2.1)
        (strategyEventLaw G S).weight y =
      G.marginalY y := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  change
    (∑ x : X, ∑ y' : Y, ∑ a : A, ∑ b : B,
      if y' = y then
        G.questionWeight x y' * S.outcomeProbability x y' a b
      else 0) = G.marginalY y
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  unfold Game.marginalY
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [← Finset.mul_sum]
  rw [S.outcomeProbability_normalized x y]
  ring

theorem repeatedAliceQuestionPrior_product
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (xs : Fin n → X) :
    groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.1)
        (strategyEventLaw (G.repeat n) S).weight xs =
      finiteIndependentProductWeight
        (fun _ : Fin n => G.marginalX) xs := by
  classical
  calc
    groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.1)
        (strategyEventLaw (G.repeat n) S).weight xs =
      (G.repeat n).marginalX xs := by
        calc
          groupedMass
              (fun ω : ExactOutcome X Y A B n => ω.1)
              (strategyEventLaw (G.repeat n) S).weight xs =
            @groupedMass
              (ExactOutcome X Y A B n) inferInstance
              (Fin n → X)
              (fun a b => Classical.propDecidable (a = b))
              (fun ω : ExactOutcome X Y A B n => ω.1)
              (strategyEventLaw (G.repeat n) S).weight xs := by
                exact congrFun
                  (exactGroupedMass_decidableEq_irrel _ _
                    (fun ω : ExactOutcome X Y A B n => ω.1)
                    (strategyEventLaw (G.repeat n) S).weight) xs
          _ = (G.repeat n).marginalX xs :=
            strategyAliceQuestionPrior_marginal
              (G.repeat n) S xs
    _ = finiteIndependentProductWeight
        (fun _ : Fin n => G.marginalX) xs := by
      unfold Game.marginalX finiteIndependentProductWeight
      simp only [Game.repeat_questionWeight]
      exact (Fintype.prod_sum
        (fun i : Fin n => fun y : Y => G.questionWeight (xs i) y)).symm

theorem repeatedBobQuestionPrior_product
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (ys : Fin n → Y) :
    groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.2.1)
        (strategyEventLaw (G.repeat n) S).weight ys =
      finiteIndependentProductWeight
        (fun _ : Fin n => G.marginalY) ys := by
  classical
  calc
    groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.2.1)
        (strategyEventLaw (G.repeat n) S).weight ys =
      (G.repeat n).marginalY ys := by
        calc
          groupedMass
              (fun ω : ExactOutcome X Y A B n => ω.2.1)
              (strategyEventLaw (G.repeat n) S).weight ys =
            @groupedMass
              (ExactOutcome X Y A B n) inferInstance
              (Fin n → Y)
              (fun a b => Classical.propDecidable (a = b))
              (fun ω : ExactOutcome X Y A B n => ω.2.1)
              (strategyEventLaw (G.repeat n) S).weight ys := by
                exact congrFun
                  (exactGroupedMass_decidableEq_irrel _ _
                    (fun ω : ExactOutcome X Y A B n => ω.2.1)
                    (strategyEventLaw (G.repeat n) S).weight) ys
          _ = (G.repeat n).marginalY ys :=
            strategyBobQuestionPrior_marginal
              (G.repeat n) S ys
    _ = finiteIndependentProductWeight
        (fun _ : Fin n => G.marginalY) ys := by
      unfold Game.marginalY finiteIndependentProductWeight
      simp only [Game.repeat_questionWeight]
      exact (Fintype.prod_sum
        (fun i : Fin n => fun x : X => G.questionWeight x (ys i))).symm

def repeatedAlicePostselectedQuestionLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : (Fin n → X) → ℝ := by
  classical
  exact groupedMass
    (fun ω : ExactOutcome X Y A B n => ω.1)
    (repeatedConditionedOutcomeLaw G n S D)

def repeatedBobPostselectedQuestionLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : (Fin n → Y) → ℝ := by
  classical
  exact groupedMass
    (fun ω : ExactOutcome X Y A B n => ω.2.1)
    (repeatedConditionedOutcomeLaw G n S D)

theorem exactGroupedMass_equiv
    {Ω K V : Type*} [Fintype Ω] [Fintype K] [Fintype V]
    (equiv : Ω ≃ K) (projection : Ω → V) (mass : Ω → ℝ)
    (v : V) :
    groupedMass (fun k : K => projection (equiv.symm k))
        (fun k : K => mass (equiv.symm k)) v =
      groupedMass projection mass v := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter, Finset.sum_filter]
  exact equiv.symm.sum_comp
    (fun ω : Ω => if projection ω = v then mass ω else 0)

theorem exactAliceInformationPosterior_firstMarginal_pushforward
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : SourceRemainingCoordinate D) (x : X) :
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) (i, x) =
      groupedMass
        (fun t : ExactLocallySampleableTuple X Y A B D =>
          (t.1, t.2.1))
        (exactLocallySampleableLaw G n S D) (i, x) := by
  classical
  let equiv := exactAliceInformationEquiv
    (X := X) (Y := Y) (A := A) (B := B) D
  let projection :=
    fun t : ExactLocallySampleableTuple X Y A B D =>
      (t.1, t.2.1)
  let mass := exactLocallySampleableLaw G n S D
  have hfirst := congrFun
    (groupedMass_first
      (exactAliceInformationPosterior G n S D)) (i, x)
  have hreindex := exactGroupedMass_equiv
    equiv projection mass (i, x)
  have hprojection :
      (fun k :
        (SourceRemainingCoordinate D × X) ×
          (ExactHistoryFlag X Y A B D × Y) =>
        projection (equiv.symm k)) = Prod.fst := by
    funext k
    rcases k with ⟨⟨j, z⟩, r, w⟩
    rfl
  have hmass :
      (fun k :
        (SourceRemainingCoordinate D × X) ×
          (ExactHistoryFlag X Y A B D × Y) =>
        mass (equiv.symm k)) =
        exactAliceInformationPosterior G n S D := by
    funext k
    rfl
  rw [hprojection, hmass] at hreindex
  calc
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) (i, x) =
      groupedMass Prod.fst
        (exactAliceInformationPosterior G n S D) (i, x) := by
          exact hfirst.symm
    _ = groupedMass projection mass (i, x) := by
      have hchange :
          groupedMass Prod.fst
              (exactAliceInformationPosterior G n S D) (i, x) =
            @groupedMass
              ((SourceRemainingCoordinate D × X) ×
                (ExactHistoryFlag X Y A B D × Y))
              inferInstance (SourceRemainingCoordinate D × X)
              (fun a b => Classical.propDecidable (a = b))
              Prod.fst
              (exactAliceInformationPosterior G n S D) (i, x) := by
        exact congrFun
          (exactGroupedMass_decidableEq_irrel _ _ Prod.fst
            (exactAliceInformationPosterior G n S D)) (i, x)
      have hreindex' :
          @groupedMass
              ((SourceRemainingCoordinate D × X) ×
                (ExactHistoryFlag X Y A B D × Y))
              inferInstance (SourceRemainingCoordinate D × X)
              (fun a b => Classical.propDecidable (a = b))
              Prod.fst
              (exactAliceInformationPosterior G n S D) (i, x) =
            @groupedMass
              (ExactLocallySampleableTuple X Y A B D)
              inferInstance (SourceRemainingCoordinate D × X)
              (fun a b => Classical.propDecidable (a = b))
              projection mass (i, x) := by
        exact hreindex
      have hright :
          @groupedMass
              (ExactLocallySampleableTuple X Y A B D)
              inferInstance (SourceRemainingCoordinate D × X)
              (fun a b => Classical.propDecidable (a = b))
              projection mass (i, x) =
            groupedMass projection mass (i, x) := by
        exact congrFun
          (exactGroupedMass_decidableEq_irrel _ _
            projection mass) (i, x)
      exact hchange.trans (hreindex'.trans hright)

theorem exactBobInformationPosterior_firstMarginal_pushforward
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : SourceRemainingCoordinate D) (y : Y) :
    jointFirstMarginal
        (exactBobInformationPosterior G n S D) (i, y) =
      groupedMass
        (fun t : ExactLocallySampleableTuple X Y A B D =>
          (t.1, t.2.2.1))
        (exactLocallySampleableLaw G n S D) (i, y) := by
  classical
  let equiv := exactBobInformationEquiv
    (X := X) (Y := Y) (A := A) (B := B) D
  let projection :=
    fun t : ExactLocallySampleableTuple X Y A B D =>
      (t.1, t.2.2.1)
  let mass := exactLocallySampleableLaw G n S D
  have hfirst := congrFun
    (groupedMass_first
      (exactBobInformationPosterior G n S D)) (i, y)
  have hreindex := exactGroupedMass_equiv
    equiv projection mass (i, y)
  have hprojection :
      (fun k :
        (SourceRemainingCoordinate D × Y) ×
          (ExactHistoryFlag X Y A B D × X) =>
        projection (equiv.symm k)) = Prod.fst := by
    funext k
    rcases k with ⟨⟨j, z⟩, r, w⟩
    rfl
  have hmass :
      (fun k :
        (SourceRemainingCoordinate D × Y) ×
          (ExactHistoryFlag X Y A B D × X) =>
        mass (equiv.symm k)) =
        exactBobInformationPosterior G n S D := by
    funext k
    rfl
  rw [hprojection, hmass] at hreindex
  calc
    jointFirstMarginal
        (exactBobInformationPosterior G n S D) (i, y) =
      groupedMass Prod.fst
        (exactBobInformationPosterior G n S D) (i, y) := by
          exact hfirst.symm
    _ = groupedMass projection mass (i, y) := by
      have hchange :
          groupedMass Prod.fst
              (exactBobInformationPosterior G n S D) (i, y) =
            @groupedMass
              ((SourceRemainingCoordinate D × Y) ×
                (ExactHistoryFlag X Y A B D × X))
              inferInstance (SourceRemainingCoordinate D × Y)
              (fun a b => Classical.propDecidable (a = b))
              Prod.fst
              (exactBobInformationPosterior G n S D) (i, y) := by
        exact congrFun
          (exactGroupedMass_decidableEq_irrel _ _ Prod.fst
            (exactBobInformationPosterior G n S D)) (i, y)
      have hreindex' :
          @groupedMass
              ((SourceRemainingCoordinate D × Y) ×
                (ExactHistoryFlag X Y A B D × X))
              inferInstance (SourceRemainingCoordinate D × Y)
              (fun a b => Classical.propDecidable (a = b))
              Prod.fst
              (exactBobInformationPosterior G n S D) (i, y) =
            @groupedMass
              (ExactLocallySampleableTuple X Y A B D)
              inferInstance (SourceRemainingCoordinate D × Y)
              (fun a b => Classical.propDecidable (a = b))
              projection mass (i, y) := by
        exact hreindex
      have hright :
          @groupedMass
              (ExactLocallySampleableTuple X Y A B D)
              inferInstance (SourceRemainingCoordinate D × Y)
              (fun a b => Classical.propDecidable (a = b))
              projection mass (i, y) =
            groupedMass projection mass (i, y) := by
        exact congrFun
          (exactGroupedMass_decidableEq_irrel _ _
            projection mass) (i, y)
      exact hchange.trans (hreindex'.trans hright)

theorem exactAliceInformationPosterior_firstMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : SourceRemainingCoordinate D) (x : X) :
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) (i, x) =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        groupedMass
          (fun ω : ExactOutcome X Y A B n => ω.1 i.val)
          (repeatedConditionedOutcomeLaw G n S D) x := by
  classical
  let code := exactLocallySampleableCode
    (X := X) (Y := Y) (A := A) (B := B) D
  let projection :=
    fun t : ExactLocallySampleableTuple X Y A B D =>
      (t.1, t.2.1)
  let joint := exactPostselectedJointLaw G n S D
  have hlaw :
      exactLocallySampleableLaw G n S D =
        groupedMass code joint := by
    unfold exactLocallySampleableLaw
      exactSourcePushforward
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  have hcomp := congrFun
    (groupedMass_comp code projection joint) (i, x)
  have hprojection :
      projection ∘ code =
        (fun q : ExactJointOutcome X Y A B D =>
          (q.1.coordinate, q.2.1 q.1.coordinate.val)) := by
    funext q
    rfl
  rw [hprojection] at hcomp
  calc
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) (i, x) =
      groupedMass projection
        (exactLocallySampleableLaw G n S D) (i, x) :=
      exactAliceInformationPosterior_firstMarginal_pushforward
        G n S D i x
    _ = groupedMass projection (groupedMass code joint) (i, x) := by
      rw [hlaw]
    _ = groupedMass
        (fun q : ExactJointOutcome X Y A B D =>
          (q.1.coordinate, q.2.1 q.1.coordinate.val)) joint (i, x) :=
      hcomp
    _ = (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        groupedMass
          (fun ω : ExactOutcome X Y A B n => ω.1 i.val)
          (repeatedConditionedOutcomeLaw G n S D) x := by
      exact exactIndependentCoordinateQuestion_marginal
        (repeatedConditionedOutcomeLaw G n S D)
        (fun ω : ExactOutcome X Y A B n =>
          fun j : SourceRemainingCoordinate D => ω.1 j.val) i x

theorem exactBobInformationPosterior_firstMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : SourceRemainingCoordinate D) (y : Y) :
    jointFirstMarginal
        (exactBobInformationPosterior G n S D) (i, y) =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        groupedMass
          (fun ω : ExactOutcome X Y A B n => ω.2.1 i.val)
          (repeatedConditionedOutcomeLaw G n S D) y := by
  classical
  let code := exactLocallySampleableCode
    (X := X) (Y := Y) (A := A) (B := B) D
  let projection :=
    fun t : ExactLocallySampleableTuple X Y A B D =>
      (t.1, t.2.2.1)
  let joint := exactPostselectedJointLaw G n S D
  have hlaw :
      exactLocallySampleableLaw G n S D =
        groupedMass code joint := by
    unfold exactLocallySampleableLaw
      exactSourcePushforward
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  have hcomp := congrFun
    (groupedMass_comp code projection joint) (i, y)
  have hprojection :
      projection ∘ code =
        (fun q : ExactJointOutcome X Y A B D =>
          (q.1.coordinate, q.2.2.1 q.1.coordinate.val)) := by
    funext q
    rfl
  rw [hprojection] at hcomp
  calc
    jointFirstMarginal
        (exactBobInformationPosterior G n S D) (i, y) =
      groupedMass projection
        (exactLocallySampleableLaw G n S D) (i, y) :=
      exactBobInformationPosterior_firstMarginal_pushforward
        G n S D i y
    _ = groupedMass projection (groupedMass code joint) (i, y) := by
      rw [hlaw]
    _ = groupedMass
        (fun q : ExactJointOutcome X Y A B D =>
          (q.1.coordinate, q.2.2.1 q.1.coordinate.val)) joint (i, y) :=
      hcomp
    _ = (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        groupedMass
          (fun ω : ExactOutcome X Y A B n => ω.2.1 i.val)
          (repeatedConditionedOutcomeLaw G n S D) y := by
      exact exactIndependentCoordinateQuestion_marginal
        (repeatedConditionedOutcomeLaw G n S D)
        (fun ω : ExactOutcome X Y A B n =>
          fun j : SourceRemainingCoordinate D => ω.2.1 j.val) i y

theorem finiteProductMarginal_projection_relativeEntropy_le
    {Ω ι V : Type*} [Fintype Ω] [Fintype ι] [Fintype V]
    (posterior prior : Ω → ℝ) (projection : Ω → (ι → V))
    (q : ι → V → ℝ) (budget : ℝ)
    (posterior_nonnegative : ∀ ω, 0 ≤ posterior ω)
    (posterior_normalized : (∑ ω : Ω, posterior ω) = 1)
    (prior_nonnegative : ∀ ω, 0 ≤ prior ω)
    (absolute_continuity : ∀ ω, prior ω = 0 → posterior ω = 0)
    (coordinate_nonnegative : ∀ i v, 0 ≤ q i v)
    (coordinate_normalized : ∀ i, (∑ v : V, q i v) = 1)
    (actual_prior :
      groupedMass projection prior =
        finiteIndependentProductWeight q)
    (actual_budget : finiteRelativeEntropy posterior prior ≤ budget) :
    (∑ i : ι,
      finiteRelativeEntropy
        (finiteCoordinateMarginal
          (groupedMass projection posterior) i)
        (q i)) ≤ budget := by
  classical
  let projected := groupedMass projection posterior
  have hnonnegative (x : ι → V) : 0 ≤ projected x :=
    groupedMass_nonneg projection posterior
      posterior_nonnegative x
  have hnormalized : (∑ x : ι → V, projected x) = 1 := by
    dsimp [projected]
    rw [groupedMass_sum, posterior_normalized]
  have habsolute (x : ι → V) :
      finiteIndependentProductWeight q x = 0 → projected x = 0 := by
    intro hx
    have hprior : groupedMass projection prior x = 0 := by
      rw [actual_prior]
      exact hx
    exact groupedMass_absolute_continuity
      projection posterior prior prior_nonnegative
      absolute_continuity x hprior
  have htensor := finiteProductMarginal_relativeEntropy_le
    projected q hnonnegative hnormalized coordinate_nonnegative
    coordinate_normalized habsolute
  have hdpi := finite_relative_entropy_data_processing
    projection posterior prior posterior_nonnegative prior_nonnegative
    absolute_continuity
  rw [actual_prior] at hdpi
  exact htensor.trans (hdpi.trans actual_budget)

theorem repeatedAliceCoordinateInformation_sum_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ j : Fin n,
      finiteRelativeEntropy
        (finiteCoordinateMarginal
          (repeatedAlicePostselectedQuestionLaw G n S D) j)
        G.marginalX) ≤
      postselectionLogCost G n S D := by
  classical
  let posterior := repeatedConditionedOutcomeLaw G n S D
  let prior := (strategyEventLaw (G.repeat n) S).weight
  let projection :=
    fun ω : ExactOutcome X Y A B n => ω.1
  let q := fun _ : Fin n => G.marginalX
  have hposterior (ω : ExactOutcome X Y A B n) :
      0 ≤ posterior ω :=
    conditionedEventDistribution_nonneg
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive ω
  have hnormalized :
      (∑ ω : ExactOutcome X Y A B n, posterior ω) = 1 :=
    conditionedEventDistribution_sum
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive
  have hac (ω : ExactOutcome X Y A B n) :
      prior ω = 0 → posterior ω = 0 :=
    conditionedEventDistribution_absolute_continuity
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) ω
  have hprior :
      groupedMass projection prior =
        finiteIndependentProductWeight q := by
    funext xs
    exact repeatedAliceQuestionPrior_product G n S xs
  have hbudget :
      finiteRelativeEntropy posterior prior ≤
        postselectionLogCost G n S D := by
    exact le_of_eq
      (repeatedConditionedOutcomeLaw_relativeEntropy
        G n S D positive)
  have h := finiteProductMarginal_projection_relativeEntropy_le
    posterior prior projection q
    (postselectionLogCost G n S D)
    hposterior hnormalized
    (strategyEventLaw (G.repeat n) S).weight_nonneg hac
    (fun j x => G.marginalX_nonneg x)
    (fun j => G.marginalX_normalized)
    hprior hbudget
  have hprojected :
      groupedMass projection posterior =
        repeatedAlicePostselectedQuestionLaw G n S D := by
    unfold repeatedAlicePostselectedQuestionLaw
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  rw [hprojected] at h
  exact h

theorem repeatedBobCoordinateInformation_sum_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ j : Fin n,
      finiteRelativeEntropy
        (finiteCoordinateMarginal
          (repeatedBobPostselectedQuestionLaw G n S D) j)
        G.marginalY) ≤
      postselectionLogCost G n S D := by
  classical
  let posterior := repeatedConditionedOutcomeLaw G n S D
  let prior := (strategyEventLaw (G.repeat n) S).weight
  let projection :=
    fun ω : ExactOutcome X Y A B n => ω.2.1
  let q := fun _ : Fin n => G.marginalY
  have hposterior (ω : ExactOutcome X Y A B n) :
      0 ≤ posterior ω :=
    conditionedEventDistribution_nonneg
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive ω
  have hnormalized :
      (∑ ω : ExactOutcome X Y A B n, posterior ω) = 1 :=
    conditionedEventDistribution_sum
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive
  have hac (ω : ExactOutcome X Y A B n) :
      prior ω = 0 → posterior ω = 0 :=
    conditionedEventDistribution_absolute_continuity
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) ω
  have hprior :
      groupedMass projection prior =
        finiteIndependentProductWeight q := by
    funext ys
    exact repeatedBobQuestionPrior_product G n S ys
  have hbudget :
      finiteRelativeEntropy posterior prior ≤
        postselectionLogCost G n S D := by
    exact le_of_eq
      (repeatedConditionedOutcomeLaw_relativeEntropy
        G n S D positive)
  have h := finiteProductMarginal_projection_relativeEntropy_le
    posterior prior projection q
    (postselectionLogCost G n S D)
    hposterior hnormalized
    (strategyEventLaw (G.repeat n) S).weight_nonneg hac
    (fun j y => G.marginalY_nonneg y)
    (fun j => G.marginalY_normalized)
    hprior hbudget
  have hprojected :
      groupedMass projection posterior =
        repeatedBobPostselectedQuestionLaw G n S D := by
    unfold repeatedBobPostselectedQuestionLaw
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  rw [hprojected] at h
  exact h

theorem finiteCoordinateMarginal_groupedMass
    {Ω ι V : Type*} [Fintype Ω] [Fintype ι] [Fintype V]
    (projection : Ω → (ι → V)) (mass : Ω → ℝ)
    (i : ι) (v : V) :
    finiteCoordinateMarginal
        (groupedMass projection mass) i v =
      groupedMass (fun ω : Ω => projection ω i) mass v := by
  classical
  let eval : (ι → V) → V := fun x => x i
  have h := congrFun
    (groupedMass_comp projection eval mass) v
  unfold finiteCoordinateMarginal
  have hleft :
      groupedMass (fun x : ι → V => x i)
          (groupedMass projection mass) v =
        @groupedMass (ι → V) inferInstance V
          (fun a b => Classical.propDecidable (a = b))
          eval (groupedMass projection mass) v := by
    exact congrFun
      (exactGroupedMass_decidableEq_irrel _ _
        eval (groupedMass projection mass)) v
  have hright :
      @groupedMass Ω inferInstance V
          (fun a b => Classical.propDecidable (a = b))
          (eval ∘ projection) mass v =
        groupedMass (fun ω : Ω => projection ω i) mass v := by
    exact congrFun
      (exactGroupedMass_decidableEq_irrel _ _
        (fun ω : Ω => projection ω i) mass) v
  exact hleft.trans (h.trans hright)

theorem finiteUniformCoordinate_relativeEntropy
    {ι V : Type*} [Fintype ι] [Fintype V]
    (positive : 0 < Fintype.card ι)
    (posterior : ι → V → ℝ) (prior : V → ℝ) :
    finiteRelativeEntropy
        (fun t : ι × V =>
          (1 / (Fintype.card ι : ℝ)) * posterior t.1 t.2)
        (fun t : ι × V =>
          (1 / (Fintype.card ι : ℝ)) * prior t.2) =
      (1 / (Fintype.card ι : ℝ)) *
        ∑ i : ι, finiteRelativeEntropy (posterior i) prior := by
  classical
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  have huniform : (1 / (Fintype.card ι : ℝ)) ≠ 0 :=
    one_div_ne_zero hcard
  unfold finiteRelativeEntropy
  rw [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [mul_div_mul_left _ _ huniform]
  ring

theorem repeatedAlicePostselectedQuestionLaw_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (xs : Fin n → X) :
    0 ≤ repeatedAlicePostselectedQuestionLaw G n S D xs := by
  classical
  unfold repeatedAlicePostselectedQuestionLaw
  apply groupedMass_nonneg
  intro ω
  exact conditionedEventDistribution_nonneg
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
    positive ω

theorem repeatedBobPostselectedQuestionLaw_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (ys : Fin n → Y) :
    0 ≤ repeatedBobPostselectedQuestionLaw G n S D ys := by
  classical
  unfold repeatedBobPostselectedQuestionLaw
  apply groupedMass_nonneg
  intro ω
  exact conditionedEventDistribution_nonneg
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
    positive ω

theorem repeatedAlicePostselectedCoordinateMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (j : Fin n) (x : X) :
    finiteCoordinateMarginal
        (repeatedAlicePostselectedQuestionLaw G n S D) j x =
      groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.1 j)
        (repeatedConditionedOutcomeLaw G n S D) x := by
  classical
  let projection :=
    fun ω : ExactOutcome X Y A B n => ω.1
  let posterior := repeatedConditionedOutcomeLaw G n S D
  have hlaw :
      repeatedAlicePostselectedQuestionLaw G n S D =
        groupedMass projection posterior := by
    unfold repeatedAlicePostselectedQuestionLaw
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  rw [hlaw]
  exact finiteCoordinateMarginal_groupedMass
    projection posterior j x

theorem repeatedBobPostselectedCoordinateMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (j : Fin n) (y : Y) :
    finiteCoordinateMarginal
        (repeatedBobPostselectedQuestionLaw G n S D) j y =
      groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.2.1 j)
        (repeatedConditionedOutcomeLaw G n S D) y := by
  classical
  let projection :=
    fun ω : ExactOutcome X Y A B n => ω.2.1
  let posterior := repeatedConditionedOutcomeLaw G n S D
  have hlaw :
      repeatedBobPostselectedQuestionLaw G n S D =
        groupedMass projection posterior := by
    unfold repeatedBobPostselectedQuestionLaw
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  rw [hlaw]
  exact finiteCoordinateMarginal_groupedMass
    projection posterior j y

theorem exactAliceSourceMarginalInformation_eq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceMarginalInformation G n S D base =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ∑ i : SourceRemainingCoordinate D,
          finiteRelativeEntropy
            (finiteCoordinateMarginal
              (repeatedAlicePostselectedQuestionLaw G n S D)
              i.val)
            G.marginalX := by
  classical
  let posterior := repeatedAlicePostselectedQuestionLaw G n S D
  have hposterior :
      jointFirstMarginal
          (exactAliceInformationPosterior G n S D) =
        (fun t : SourceRemainingCoordinate D × X =>
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            finiteCoordinateMarginal posterior t.1.val t.2) := by
    funext t
    rcases t with ⟨i, x⟩
    rw [exactAliceInformationPosterior_firstMarginal]
    congr 1
    exact (repeatedAlicePostselectedCoordinateMarginal
      G n S D i.val x).symm
  have hreference :
      jointFirstMarginal
          (exactAliceInformationReference G n S D base) =
        (fun t : SourceRemainingCoordinate D × X =>
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            G.marginalX t.2) := by
    funext t
    rcases t with ⟨i, x⟩
    rw [exactAliceInformationReference_firstMarginal]
    change G.marginalX x /
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) = _
    ring
  unfold exactAliceSourceMarginalInformation
  rw [hposterior, hreference]
  exact finiteUniformCoordinate_relativeEntropy
    (exactRemainingCoordinate_card_pos D remaining)
    (fun i : SourceRemainingCoordinate D =>
      finiteCoordinateMarginal posterior i.val)
    G.marginalX

theorem exactBobSourceMarginalInformation_eq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D) :
    exactBobSourceMarginalInformation G n S D base =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ∑ i : SourceRemainingCoordinate D,
          finiteRelativeEntropy
            (finiteCoordinateMarginal
              (repeatedBobPostselectedQuestionLaw G n S D)
              i.val)
            G.marginalY := by
  classical
  let posterior := repeatedBobPostselectedQuestionLaw G n S D
  have hposterior :
      jointFirstMarginal
          (exactBobInformationPosterior G n S D) =
        (fun t : SourceRemainingCoordinate D × Y =>
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            finiteCoordinateMarginal posterior t.1.val t.2) := by
    funext t
    rcases t with ⟨i, y⟩
    rw [exactBobInformationPosterior_firstMarginal]
    congr 1
    exact (repeatedBobPostselectedCoordinateMarginal
      G n S D i.val y).symm
  have hreference :
      jointFirstMarginal
          (exactBobInformationReference G n S D base) =
        (fun t : SourceRemainingCoordinate D × Y =>
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            G.marginalY t.2) := by
    funext t
    rcases t with ⟨i, y⟩
    rw [exactBobInformationReference_firstMarginal]
    change G.marginalY y /
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) = _
    ring
  unfold exactBobSourceMarginalInformation
  rw [hposterior, hreference]
  exact finiteUniformCoordinate_relativeEntropy
    (exactRemainingCoordinate_card_pos D remaining)
    (fun i : SourceRemainingCoordinate D =>
      finiteCoordinateMarginal posterior i.val)
    G.marginalY

theorem sourceRemaining_nonnegative_sum_le
    {n : ℕ} (D : Finset (Fin n)) (f : Fin n → ℝ)
    (nonnegative : ∀ j, 0 ≤ f j) :
    (∑ i : SourceRemainingCoordinate D, f i.val) ≤
      ∑ j : Fin n, f j := by
  classical
  change
    (∑ i ∈ (Finset.univ \ D).attach, f i.val) ≤
      ∑ j : Fin n, f j
  rw [Finset.sum_attach]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Finset.univ \ D))
    (fun j _ _ => nonnegative j)

theorem exactAliceSourceMarginalInformation_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceMarginalInformation G n S D base ≤
      postselectionLogCost G n S D /
        ((Finset.univ \ D).card : ℝ) := by
  classical
  let posterior := repeatedAlicePostselectedQuestionLaw G n S D
  let coordinateInfo : Fin n → ℝ := fun j =>
    finiteRelativeEntropy
      (finiteCoordinateMarginal posterior j) G.marginalX
  have hnonnegative (j : Fin n) : 0 ≤ coordinateInfo j := by
    exact finiteRelativeEntropy_nonneg
      (finiteCoordinateMarginal posterior j) G.marginalX
      (fun x => finiteCoordinateMarginal_nonneg
        posterior
        (repeatedAlicePostselectedQuestionLaw_nonneg
          G n S D positive) j x)
      G.marginalX_nonneg
  have hremaining :
      (∑ i : SourceRemainingCoordinate D, coordinateInfo i.val) ≤
        postselectionLogCost G n S D := by
    exact
      (sourceRemaining_nonnegative_sum_le
        D coordinateInfo hnonnegative).trans
      (repeatedAliceCoordinateInformation_sum_le
        G n S D positive)
  have hcard :
      Fintype.card (SourceRemainingCoordinate D) =
        (Finset.univ \ D).card := by
    simp
  calc
    exactAliceSourceMarginalInformation G n S D base =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ∑ i : SourceRemainingCoordinate D, coordinateInfo i.val :=
      exactAliceSourceMarginalInformation_eq
        G n S D remaining base
    _ ≤ (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        postselectionLogCost G n S D := by
      exact mul_le_mul_of_nonneg_left hremaining
        (one_div_nonneg.mpr (Nat.cast_nonneg _))
    _ = postselectionLogCost G n S D /
        ((Finset.univ \ D).card : ℝ) := by
      rw [hcard]
      ring

theorem exactBobSourceMarginalInformation_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactBobSourceMarginalInformation G n S D base ≤
      postselectionLogCost G n S D /
        ((Finset.univ \ D).card : ℝ) := by
  classical
  let posterior := repeatedBobPostselectedQuestionLaw G n S D
  let coordinateInfo : Fin n → ℝ := fun j =>
    finiteRelativeEntropy
      (finiteCoordinateMarginal posterior j) G.marginalY
  have hnonnegative (j : Fin n) : 0 ≤ coordinateInfo j := by
    exact finiteRelativeEntropy_nonneg
      (finiteCoordinateMarginal posterior j) G.marginalY
      (fun y => finiteCoordinateMarginal_nonneg
        posterior
        (repeatedBobPostselectedQuestionLaw_nonneg
          G n S D positive) j y)
      G.marginalY_nonneg
  have hremaining :
      (∑ i : SourceRemainingCoordinate D, coordinateInfo i.val) ≤
        postselectionLogCost G n S D := by
    exact
      (sourceRemaining_nonnegative_sum_le
        D coordinateInfo hnonnegative).trans
      (repeatedBobCoordinateInformation_sum_le
        G n S D positive)
  have hcard :
      Fintype.card (SourceRemainingCoordinate D) =
        (Finset.univ \ D).card := by
    simp
  calc
    exactBobSourceMarginalInformation G n S D base =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ∑ i : SourceRemainingCoordinate D, coordinateInfo i.val :=
      exactBobSourceMarginalInformation_eq
        G n S D remaining base
    _ ≤ (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        postselectionLogCost G n S D := by
      exact mul_le_mul_of_nonneg_left hremaining
        (one_div_nonneg.mpr (Nat.cast_nonneg _))
    _ = postselectionLogCost G n S D /
        ((Finset.univ \ D).card : ℝ) := by
      rw [hcard]
      ring

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exact_source_equation_twenty_three_of_conditioned_reverse_prefix
    {KA KB : Type*} [Fintype KA] [Fintype KB]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (seedLawA : Finset (SourceRemainingCoordinate D) →
      FiniteEventLaw KA)
    (seedLawB : Finset (SourceRemainingCoordinate D) →
      FiniteEventLaw KB)
    (ΩA ΩB : Finset (SourceRemainingCoordinate D) → Type*)
    [∀ side, Fintype (ΩA side)]
    [∀ side, Fintype (ΩB side)]
    (projectionA : ∀ side : Finset (SourceRemainingCoordinate D),
      KA × ExactOutcome X Y A B n →
        ΩA side × (Fin side.card → Y))
    (projectionB : ∀ side : Finset (SourceRemainingCoordinate D),
      KB × ExactOutcome X Y A B n →
        ΩB side × (Fin side.card → X))
    (defaultY : Y) (defaultX : X)
    (aliceConditionedReverseIdentification :
      exactAliceSourceConditionalInformation G n S D base =
        ∑ side : Finset (SourceRemainingCoordinate D),
          reversePartitionWeight side *
            ((∑ k : Fin side.card,
              reweightedSeedPrefixEntropyIncrement
                (seedLawA side) G n S D
                (projectionA side) defaultY k) /
              (side.card : ℝ)))
    (bobConditionedReverseIdentification :
      exactBobSourceConditionalInformation G n S D base =
        ∑ side : Finset (SourceRemainingCoordinate D),
          reversePartitionWeight side *
            ((∑ k : Fin side.card,
              reweightedSeedPrefixEntropyIncrement
                (seedLawB side) G n S D
                (projectionB side) defaultX k) /
              (side.card : ℝ))) :
    ExactSourceClassicalInformationBound G n S D base := by
  constructor
  · rw [exact_source_equation_twenty_four_alice
      G n S D remaining positive base]
    change
      exactAliceSourceMarginalInformation G n S D base +
          exactAliceSourceConditionalInformation G n S D base ≤
        exactSourceClassicalInformationRate G n S D
    calc
      exactAliceSourceMarginalInformation G n S D base +
          exactAliceSourceConditionalInformation G n S D base ≤
        postselectionLogCost G n S D /
            ((Finset.univ \ D).card : ℝ) +
          2 * (postselectionLogCost G n S D +
            answerLogCost (A := A) (B := B) D) /
              ((Finset.univ \ D).card : ℝ) := by
            apply add_le_add
            · exact exactAliceSourceMarginalInformation_le
                G n S D remaining positive base
            · rw [aliceConditionedReverseIdentification]
              exact
                reweightedSeed_reverse_source_prefix_information_budget
                  G n S D remaining positive
                  seedLawA ΩA projectionA defaultY
      _ = exactSourceClassicalInformationRate G n S D := by
        unfold exactSourceClassicalInformationRate
        ring
  · rw [exact_source_equation_twenty_four_bob
      G n S D remaining positive base]
    change
      exactBobSourceMarginalInformation G n S D base +
          exactBobSourceConditionalInformation G n S D base ≤
        exactSourceClassicalInformationRate G n S D
    calc
      exactBobSourceMarginalInformation G n S D base +
          exactBobSourceConditionalInformation G n S D base ≤
        postselectionLogCost G n S D /
            ((Finset.univ \ D).card : ℝ) +
          2 * (postselectionLogCost G n S D +
            answerLogCost (A := A) (B := B) D) /
              ((Finset.univ \ D).card : ℝ) := by
            apply add_le_add
            · exact exactBobSourceMarginalInformation_le
                G n S D remaining positive base
            · rw [bobConditionedReverseIdentification]
              exact
                reweightedSeed_reverse_source_prefix_information_budget
                  G n S D remaining positive
                  seedLawB ΩB projectionB defaultX
      _ = exactSourceClassicalInformationRate G n S D := by
        unfold exactSourceClassicalInformationRate
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

def exactConditionedReverseAlicePrefixEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (k : Fin side.card) : ℝ :=
  reweightedSeedPrefixEntropyIncrement
    (exactReverseAliceConditionalSeedLaw
      (exactRemainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseAliceSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)
    default k

def exactConditionedReverseBobPrefixEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (k : Fin side.card) : ℝ :=
  reweightedSeedPrefixEntropyIncrement
    (exactReverseBobConditionalSeedLaw
      (exactRemainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseBobSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)
    default k

def exactConditionedReverseAlicePrefixInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : Y) : ℝ :=
  ∑ side : Finset (SourceRemainingCoordinate D),
    reversePartitionWeight side *
      ((∑ k : Fin side.card,
        exactConditionedReverseAlicePrefixEntropyIncrement
          G n S D remaining side default k) /
        (side.card : ℝ))

def exactConditionedReverseBobPrefixInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X) : ℝ :=
  ∑ side : Finset (SourceRemainingCoordinate D),
    reversePartitionWeight side *
      ((∑ k : Fin side.card,
        exactConditionedReverseBobPrefixEntropyIncrement
          G n S D remaining side default k) /
        (side.card : ℝ))

def ExactReverseAliceConditionalHistoryIdentification
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D)
    (default : Y) : Prop :=
  exactAliceSourceConditionalInformation G n S D base =
    exactConditionedReverseAlicePrefixInformation
      G n S D remaining default

def ExactReverseBobConditionalHistoryIdentification
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D)
    (default : X) : Prop :=
  exactBobSourceConditionalInformation G n S D base =
    exactConditionedReverseBobPrefixInformation
      G n S D remaining default

theorem exact_source_equation_twenty_three_of_actual_conditioned_reindex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (defaultY : Y) (defaultX : X)
    (alice : ExactReverseAliceConditionalHistoryIdentification
      G n S D remaining base defaultY)
    (bob : ExactReverseBobConditionalHistoryIdentification
      G n S D remaining base defaultX) :
    ExactSourceClassicalInformationBound G n S D base := by
  apply
    exact_source_equation_twenty_three_of_conditioned_reverse_prefix
      G n S D remaining positive base
      (exactReverseAliceConditionalSeedLaw
        (exactRemainingCoordinate_card_pos D remaining))
      (exactReverseBobConditionalSeedLaw
        (exactRemainingCoordinate_card_pos D remaining))
      (ExactReverseAliceFixedInformation X Y D)
      (ExactReverseBobFixedInformation X Y D)
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B) D)
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B) D)
      defaultY defaultX
  · exact alice
  · exact bob

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem finiteRelativeEntropy_self
    {I : Type*} [Fintype I] (mass : I → ℝ) :
    finiteRelativeEntropy mass mass = 0 := by
  unfold finiteRelativeEntropy
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : mass i = 0
  · simp [hi]
  · simp [hi, InformationTheory.klFun]

theorem finiteConditionalHistoryRelativeEntropy_eq
    {I R V : Type*} [Fintype I] [Fintype R] [Fintype V]
    (p q : I × (R × V) → ℝ)
    (p_nonnegative : ∀ point, 0 ≤ p point)
    (q_nonnegative : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (reference : I → R → V → ℝ)
    (same_history : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        jointFirstMarginal (jointConditional p i) =
          jointFirstMarginal (jointConditional q i))
    (next_reference : ∀ i r,
      jointFirstMarginal p i ≠ 0 →
      jointFirstMarginal (jointConditional p i) r ≠ 0 →
        jointConditional (jointConditional q i) r = reference i r) :
    (∑ i : I,
      jointFirstMarginal p i *
        finiteRelativeEntropy
          (jointConditional p i)
          (jointConditional q i)) =
      ∑ i : I,
        jointFirstMarginal p i *
          (∑ r : R,
            jointFirstMarginal (jointConditional p i) r *
              finiteRelativeEntropy
                (jointConditional (jointConditional p i) r)
                (reference i r)) := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hpi : jointFirstMarginal p i = 0
  · simp [hpi]
  · have hqi : jointFirstMarginal q i ≠ 0 := by
      intro hz
      exact hpi
        (jointFirstMarginal_absolute_continuity
          p q q_nonnegative absolute_continuity i hz)
    have hpconditional :
        ∀ t : R × V, 0 ≤ jointConditional p i t := by
      intro t
      exact div_nonneg (p_nonnegative (i, t))
        (jointFirstMarginal_nonneg p p_nonnegative i)
    have hqconditional :
        ∀ t : R × V, 0 ≤ jointConditional q i t := by
      intro t
      exact div_nonneg (q_nonnegative (i, t))
        (jointFirstMarginal_nonneg q q_nonnegative i)
    have hconditional_absolute :
        ∀ t : R × V,
          jointConditional q i t = 0 →
            jointConditional p i t = 0 := by
      intro t hz
      have hqzero : q (i, t) = 0 := by
        change q (i, t) / jointFirstMarginal q i = 0 at hz
        exact (div_eq_zero_iff.mp hz).resolve_right hqi
      simp [jointConditional,
        absolute_continuity (i, t) hqzero]
    have hchain := finite_relative_entropy_joint_chain_rule
      (jointConditional p i) (jointConditional q i)
      hpconditional hqconditional hconditional_absolute
      (jointConditional_sum p i hpi)
      (jointConditional_sum q i hqi)
    have hhistory_entropy :
        finiteRelativeEntropy
          (jointFirstMarginal (jointConditional p i))
          (jointFirstMarginal (jointConditional q i)) = 0 := by
      rw [← same_history i hpi]
      exact finiteRelativeEntropy_self _
    rw [hhistory_entropy, zero_add] at hchain
    rw [hchain]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : jointFirstMarginal (jointConditional p i) r = 0
    · simp [hr]
    · rw [next_reference i r hpi hr]

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem finiteSupportedConditionalHistoryReferenceFirstMarginal_eq
    {I R V : Type*} [Fintype I] [Fintype R] [Fintype V]
    (p q : I × (R × V) → ℝ)
    (q_nonnegative : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (reference : I → R → V → ℝ)
    (reference_normalized : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r, (∑ v : V, reference i r v) = 1)
    (factor : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r v,
          q (i, (r, v)) =
            jointFirstMarginal q i *
              jointFirstMarginal (jointConditional p i) r *
              reference i r v)
    (i : I) (supported : jointFirstMarginal p i ≠ 0) :
    jointFirstMarginal (jointConditional q i) =
      jointFirstMarginal (jointConditional p i) := by
  have hqi : jointFirstMarginal q i ≠ 0 := by
    intro hz
    exact supported
      (jointFirstMarginal_absolute_continuity
        p q q_nonnegative absolute_continuity i hz)
  funext r
  change
    (∑ v : V,
      q (i, (r, v)) / jointFirstMarginal q i) =
      jointFirstMarginal (jointConditional p i) r
  simp_rw [factor i supported r]
  calc
    (∑ v : V,
      (jointFirstMarginal q i *
        jointFirstMarginal (jointConditional p i) r *
        reference i r v) / jointFirstMarginal q i) =
      ∑ v : V,
        jointFirstMarginal (jointConditional p i) r *
          reference i r v := by
        apply Finset.sum_congr rfl
        intro v _
        field_simp [hqi]
    _ = jointFirstMarginal (jointConditional p i) r := by
      rw [← Finset.mul_sum, reference_normalized i supported r]
      ring

theorem finiteSupportedConditionalHistoryReferenceConditional_eq
    {I R V : Type*} [Fintype I] [Fintype R] [Fintype V]
    (p q : I × (R × V) → ℝ)
    (q_nonnegative : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (reference : I → R → V → ℝ)
    (reference_normalized : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r, (∑ v : V, reference i r v) = 1)
    (factor : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r v,
          q (i, (r, v)) =
            jointFirstMarginal q i *
              jointFirstMarginal (jointConditional p i) r *
              reference i r v)
    (i : I) (r : R)
    (supported : jointFirstMarginal p i ≠ 0)
    (history_supported :
      jointFirstMarginal (jointConditional p i) r ≠ 0) :
    jointConditional (jointConditional q i) r = reference i r := by
  have hqi : jointFirstMarginal q i ≠ 0 := by
    intro hz
    exact supported
      (jointFirstMarginal_absolute_continuity
        p q q_nonnegative absolute_continuity i hz)
  have hhistory :=
    finiteSupportedConditionalHistoryReferenceFirstMarginal_eq
      p q q_nonnegative absolute_continuity
      reference reference_normalized factor i supported
  funext v
  change
    (q (i, (r, v)) / jointFirstMarginal q i) /
        jointFirstMarginal (jointConditional q i) r =
      reference i r v
  rw [factor i supported r v, congrFun hhistory r]
  field_simp [hqi, history_supported]

theorem finiteSupportedConditionalHistoryRelativeEntropy_eq_of_factor
    {I R V : Type*} [Fintype I] [Fintype R] [Fintype V]
    (p q : I × (R × V) → ℝ)
    (p_nonnegative : ∀ point, 0 ≤ p point)
    (q_nonnegative : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (reference : I → R → V → ℝ)
    (reference_normalized : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r, (∑ v : V, reference i r v) = 1)
    (factor : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r v,
          q (i, (r, v)) =
            jointFirstMarginal q i *
              jointFirstMarginal (jointConditional p i) r *
              reference i r v) :
    (∑ i : I,
      jointFirstMarginal p i *
        finiteRelativeEntropy
          (jointConditional p i)
          (jointConditional q i)) =
      ∑ i : I,
        jointFirstMarginal p i *
          (∑ r : R,
            jointFirstMarginal (jointConditional p i) r *
              finiteRelativeEntropy
                (jointConditional (jointConditional p i) r)
                (reference i r)) := by
  apply finiteConditionalHistoryRelativeEntropy_eq
    p q p_nonnegative q_nonnegative absolute_continuity reference
  · intro i hi
    exact
      (finiteSupportedConditionalHistoryReferenceFirstMarginal_eq
        p q q_nonnegative absolute_continuity
        reference reference_normalized factor i hi).symm
  · intro i r hi hr
    exact
      finiteSupportedConditionalHistoryReferenceConditional_eq
        p q q_nonnegative absolute_continuity
        reference reference_normalized factor i r hi hr

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactAliceInformationPosterior_firstMarginal_eq_localMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (i : SourceRemainingCoordinate D) (x : X) :
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) (i, x) =
      exactAliceLocalMass D
        (exactLocallySampleableLaw G n S D) i x := by
  unfold jointFirstMarginal
  rw [Fintype.sum_prod_type]
  rfl

theorem exactBobInformationPosterior_firstMarginal_eq_localMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (i : SourceRemainingCoordinate D) (y : Y) :
    jointFirstMarginal
        (exactBobInformationPosterior G n S D) (i, y) =
      exactBobLocalMass D
        (exactLocallySampleableLaw G n S D) i y := by
  unfold jointFirstMarginal
  rw [Fintype.sum_prod_type]
  rfl

theorem exactAliceSupportedQuestion_marginal_pos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (x : X)
    (supported : jointFirstMarginal
      (exactAliceInformationPosterior G n S D) (i, x) ≠ 0) :
    0 < G.marginalX x := by
  let p := exactAliceInformationPosterior G n S D
  let q := exactAliceInformationReference G n S D base
  have hqnonnegative : ∀ t, 0 ≤ q t := by
    intro t
    exact exactLocallySampleableJA_nonneg
      G n S D positive base
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hac : ∀ t, q t = 0 → p t = 0 := by
    intro t hz
    exact exactLocallySampleableLaw_absolute_continuous_JA
      G n S D remaining positive base
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t) hz
  have hqmass : jointFirstMarginal q (i, x) ≠ 0 := by
    intro hz
    exact supported
      (jointFirstMarginal_absolute_continuity
        p q hqnonnegative hac (i, x) hz)
  rw [exactAliceInformationReference_firstMarginal
    G n S D base i x] at hqmass
  have hx : G.marginalX x ≠ 0 := by
    intro hz
    apply hqmass
    change G.marginalX x /
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) = 0
    rw [hz]
    simp
  exact lt_of_le_of_ne (G.marginalX_nonneg x) (Ne.symm hx)

theorem exactBobSupportedQuestion_marginal_pos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (y : Y)
    (supported : jointFirstMarginal
      (exactBobInformationPosterior G n S D) (i, y) ≠ 0) :
    0 < G.marginalY y := by
  let p := exactBobInformationPosterior G n S D
  let q := exactBobInformationReference G n S D base
  have hqnonnegative : ∀ t, 0 ≤ q t := by
    intro t
    exact exactLocallySampleableJB_nonneg
      G n S D positive base
      ((exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hac : ∀ t, q t = 0 → p t = 0 := by
    intro t hz
    exact exactLocallySampleableLaw_absolute_continuous_JB
      G n S D remaining positive base
      ((exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t) hz
  have hqmass : jointFirstMarginal q (i, y) ≠ 0 := by
    intro hz
    exact supported
      (jointFirstMarginal_absolute_continuity
        p q hqnonnegative hac (i, y) hz)
  rw [exactBobInformationReference_firstMarginal
    G n S D base i y] at hqmass
  have hy : G.marginalY y ≠ 0 := by
    intro hz
    apply hqmass
    change G.marginalY y /
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) = 0
    rw [hz]
    simp
  exact lt_of_le_of_ne (G.marginalY_nonneg y) (Ne.symm hy)

theorem exactAliceInformationPosterior_historyMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (x : X)
    (supported : jointFirstMarginal
      (exactAliceInformationPosterior G n S D) (i, x) ≠ 0)
    (r : ExactHistoryFlag X Y A B D) :
    jointFirstMarginal
        (jointConditional
          (exactAliceInformationPosterior G n S D) (i, x)) r =
      exactAliceLocalConditional D base
        (exactLocallySampleableLaw G n S D) i x r := by
  have hmass :=
    exactAliceInformationPosterior_firstMarginal_eq_localMass
      G n S D i x
  have hlocal :
      exactAliceLocalMass D
        (exactLocallySampleableLaw G n S D) i x ≠ 0 := by
    rw [← hmass]
    exact supported
  unfold jointFirstMarginal jointConditional
  change
    (∑ y : Y,
      exactLocallySampleableLaw G n S D (i, x, y, r) /
        jointFirstMarginal
          (exactAliceInformationPosterior G n S D) (i, x)) =
      exactAliceLocalConditional D base
        (exactLocallySampleableLaw G n S D) i x r
  rw [← Finset.sum_div, hmass]
  simp [exactAliceLocalConditional, hlocal]

theorem exactBobInformationPosterior_historyMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (y : Y)
    (supported : jointFirstMarginal
      (exactBobInformationPosterior G n S D) (i, y) ≠ 0)
    (r : ExactHistoryFlag X Y A B D) :
    jointFirstMarginal
        (jointConditional
          (exactBobInformationPosterior G n S D) (i, y)) r =
      exactBobLocalConditional D base
        (exactLocallySampleableLaw G n S D) i y r := by
  have hmass :=
    exactBobInformationPosterior_firstMarginal_eq_localMass
      G n S D i y
  have hlocal :
      exactBobLocalMass D
        (exactLocallySampleableLaw G n S D) i y ≠ 0 := by
    rw [← hmass]
    exact supported
  unfold jointFirstMarginal jointConditional
  change
    (∑ x : X,
      exactLocallySampleableLaw G n S D (i, x, y, r) /
        jointFirstMarginal
          (exactBobInformationPosterior G n S D) (i, y)) =
      exactBobLocalConditional D base
        (exactLocallySampleableLaw G n S D) i y r
  rw [← Finset.sum_div, hmass]
  simp [exactBobLocalConditional, hlocal]

theorem exactAliceInformationReference_supported_factor
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (x : X)
    (supported : jointFirstMarginal
      (exactAliceInformationPosterior G n S D) (i, x) ≠ 0)
    (r : ExactHistoryFlag X Y A B D) (y : Y) :
    exactAliceInformationReference G n S D base
        ((i, x), (r, y)) =
      jointFirstMarginal
          (exactAliceInformationReference G n S D base) (i, x) *
        jointFirstMarginal
          (jointConditional
            (exactAliceInformationPosterior G n S D) (i, x)) r *
        G.conditionalYGivenX x y := by
  rw [exactAliceInformationReference_firstMarginal
    G n S D base i x,
    exactAliceInformationPosterior_historyMarginal
      G n S D base i x supported r]
  change
    G.questionWeight x y *
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D) i x r /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ) =
      (G.marginalX x /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D) i x r *
        G.conditionalYGivenX x y
  rw [← G.marginalX_mul_conditionalYGivenX x y]
  ring

theorem exactBobInformationReference_supported_factor
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (y : Y)
    (supported : jointFirstMarginal
      (exactBobInformationPosterior G n S D) (i, y) ≠ 0)
    (r : ExactHistoryFlag X Y A B D) (x : X) :
    exactBobInformationReference G n S D base
        ((i, y), (r, x)) =
      jointFirstMarginal
          (exactBobInformationReference G n S D base) (i, y) *
        jointFirstMarginal
          (jointConditional
            (exactBobInformationPosterior G n S D) (i, y)) r *
        G.conditionalXGivenY y x := by
  rw [exactBobInformationReference_firstMarginal
    G n S D base i y,
    exactBobInformationPosterior_historyMarginal
      G n S D base i y supported r]
  change
    G.questionWeight x y *
        exactBobLocalConditional D base
          (exactLocallySampleableLaw G n S D) i y r /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ) =
      (G.marginalY y /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        exactBobLocalConditional D base
          (exactLocallySampleableLaw G n S D) i y r *
        G.conditionalXGivenY y x
  rw [← G.marginalY_mul_conditionalXGivenY x y]
  ring

theorem exactAliceSourceConditionalInformation_eq_question
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceConditionalInformation G n S D base =
      ∑ ix : SourceRemainingCoordinate D × X,
        jointFirstMarginal
          (exactAliceInformationPosterior G n S D) ix *
          (∑ r : ExactHistoryFlag X Y A B D,
            jointFirstMarginal
                (jointConditional
                  (exactAliceInformationPosterior G n S D) ix) r *
              finiteRelativeEntropy
                (jointConditional
                  (jointConditional
                    (exactAliceInformationPosterior G n S D) ix) r)
                (G.conditionalYGivenX ix.2)) := by
  let p := exactAliceInformationPosterior G n S D
  let q := exactAliceInformationReference G n S D base
  have hp : ∀ t, 0 ≤ p t := by
    intro t
    exact exactLocallySampleableLaw_nonneg
      G n S D positive
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hq : ∀ t, 0 ≤ q t := by
    intro t
    exact exactLocallySampleableJA_nonneg
      G n S D positive base
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hac : ∀ t, q t = 0 → p t = 0 := by
    intro t hz
    exact exactLocallySampleableLaw_absolute_continuous_JA
      G n S D remaining positive base
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t) hz
  unfold exactAliceSourceConditionalInformation
  apply finiteSupportedConditionalHistoryRelativeEntropy_eq_of_factor
    p q hp hq hac
    (fun ix _ => G.conditionalYGivenX ix.2)
  · intro ix hix r
    exact G.conditionalYGivenX_sum ix.2
      (exactAliceSupportedQuestion_marginal_pos
        G n S D remaining positive base ix.1 ix.2 hix)
  · intro ix hix r y
    exact exactAliceInformationReference_supported_factor
      G n S D base ix.1 ix.2 hix r y

theorem exactBobSourceConditionalInformation_eq_question
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactBobSourceConditionalInformation G n S D base =
      ∑ iy : SourceRemainingCoordinate D × Y,
        jointFirstMarginal
          (exactBobInformationPosterior G n S D) iy *
          (∑ r : ExactHistoryFlag X Y A B D,
            jointFirstMarginal
                (jointConditional
                  (exactBobInformationPosterior G n S D) iy) r *
              finiteRelativeEntropy
                (jointConditional
                  (jointConditional
                    (exactBobInformationPosterior G n S D) iy) r)
                (G.conditionalXGivenY iy.2)) := by
  let p := exactBobInformationPosterior G n S D
  let q := exactBobInformationReference G n S D base
  have hp : ∀ t, 0 ≤ p t := by
    intro t
    exact exactLocallySampleableLaw_nonneg
      G n S D positive
      ((exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hq : ∀ t, 0 ≤ q t := by
    intro t
    exact exactLocallySampleableJB_nonneg
      G n S D positive base
      ((exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hac : ∀ t, q t = 0 → p t = 0 := by
    intro t hz
    exact exactLocallySampleableLaw_absolute_continuous_JB
      G n S D remaining positive base
      ((exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t) hz
  unfold exactBobSourceConditionalInformation
  apply finiteSupportedConditionalHistoryRelativeEntropy_eq_of_factor
    p q hp hq hac
    (fun iy _ => G.conditionalXGivenY iy.2)
  · intro iy hiy r
    exact G.conditionalXGivenY_sum iy.2
      (exactBobSupportedQuestion_marginal_pos
        G n S D remaining positive base iy.1 iy.2 hiy)
  · intro iy hiy r x
    exact exactBobInformationReference_supported_factor
      G n S D base iy.1 iy.2 hiy r x

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

abbrev ExactReverseAliceNextContext
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :=
  (ExactReverseAliceFixedInformation X Y D side ×
    ConditionedAnswerFlag A B D) ×
    (Fin side.card → Y)

abbrev ExactReverseBobNextContext
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :=
  (ExactReverseBobFixedInformation X Y D side ×
    ConditionedAnswerFlag A B D) ×
    (Fin side.card → X)

def exactConditionedReverseAliceNextJoint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactReverseAliceNextContext X Y A B D side → ℝ :=
  reweightedSeedPrefixJoint
    (exactReverseAliceConditionalSeedLaw
      (exactRemainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseAliceSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)

def exactConditionedReverseAliceNextPrior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactReverseAliceNextContext X Y A B D side → ℝ :=
  reweightedSeedPrefixPrior
    (exactReverseAliceConditionalSeedLaw
      (exactRemainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseAliceSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)

def exactConditionedReverseBobNextJoint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactReverseBobNextContext X Y A B D side → ℝ :=
  reweightedSeedPrefixJoint
    (exactReverseBobConditionalSeedLaw
      (exactRemainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseBobSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)

def exactConditionedReverseBobNextPrior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactReverseBobNextContext X Y A B D side → ℝ :=
  reweightedSeedPrefixPrior
    (exactReverseBobConditionalSeedLaw
      (exactRemainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseBobSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)

theorem exactReverseAliceMaskedProjection_eq_of_history
    {n : ℕ} (D : Finset (Fin n))
    (default : Y)
    (q q' : ExactJointOutcome X Y A B D)
    (same_history :
      exactHistoryCode D q =
        exactHistoryCode D q')
    (same_question :
      q.2.1 q.1.coordinate.val =
        q'.2.1 q'.1.coordinate.val) :
    finitePrefixMask
      default
      ((exactReverseAliceContext q.1).sideRank
        ⟨q.1.coordinate,
          exactReverseLeftSide_coordinate_mem q.1⟩).castSucc
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseLeftSide q.1) q) =
    finitePrefixMask
      default
      ((exactReverseAliceContext q.1).sideRank
        ⟨q.1.coordinate,
          exactReverseLeftSide_coordinate_mem q.1⟩).castSucc
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseLeftSide q.1) q') := by
  rcases q with ⟨seed, outcome⟩
  rcases q' with ⟨seed', outcome'⟩
  have hseed : seed = seed' :=
    congrArg (fun r : ExactHistoryFlag X Y A B D => r.seed)
      same_history
  subst seed'
  have htuple := congrArg
    (exactHistoryFlagEquiv
      (X := X) (Y := Y) (A := A) (B := B) D)
    same_history
  change
    (⟨seed,
       (exactRevealCode D seed
         (outcome.1, outcome.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D) =
    (⟨seed,
       (exactRevealCode D seed
         (outcome'.1, outcome'.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D) at htuple
  have hpair := eq_of_heq (Sigma.mk.inj htuple).2
  have hreveal :
      exactRevealCode D seed
          (outcome.1, outcome.2.1) =
        exactRevealCode D seed
          (outcome'.1, outcome'.2.1) :=
    congrArg Prod.fst hpair
  have hac := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.aliceConditioned) hreveal
  have hbc := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.bobConditioned) hreveal
  have hal := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.aliceLeft) hreveal
  have hbr := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.bobRight) hreveal
  have hbl := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.bobLeftPrefix) hreveal
  have har := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.aliceRightPrefix) hreveal
  let side := exactReverseLeftSide seed
  let context := exactReverseAliceContext seed
  let marker : Fin side.card :=
    context.sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
  have hmarker : marker.val = seed.leftCut.val := by
    exact exactReverseAliceContext_marked_rank seed
  have hfixed :
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome)).1 =
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome')).1 := by
    simp only [side, exactReverseAliceSourceProjection,
      exactReverseAliceContextAt_actual]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Prod.ext
      · exact hac
      apply Prod.ext
      · exact hbc
      apply Prod.ext
      · funext j
        by_cases hj : j.val = seed.coordinate
        · have hval : j.val.val = seed.coordinate.val :=
            congrArg Subtype.val hj
          simpa [hval] using same_question
        · have hleft :
              j.val ∈ exactLeft
                seed.coordinate seed.partition := by
            have hmem :
                j.val ∈ insert seed.coordinate
                  (exactLeft seed.coordinate seed.partition) :=
              j.property
            exact (Finset.mem_insert.mp hmem).resolve_left hj
          exact congrFun hal ⟨j.val, hleft⟩
      apply Prod.ext
      · funext j
        have hj :
            j.val ∈ exactRight
              seed.coordinate seed.partition := by
          simpa [exactReverseAliceContextAt,
            exactReverseAliceContext] using j.property
        exact congrFun hbr ⟨j.val, hj⟩
      funext j
      have hj : j.val ∈ exactRightPrefix seed := by
        have hprefix :
            exactReverseContextOtherPrefix
              (exactReverseAliceContextAt
                (exactReverseLeftSide seed) seed) =
              exactRightPrefix seed := by
          rw [exactReverseAliceContextAt_actual,
            exactReverseAliceContext_otherPrefix]
        exact (Finset.ext_iff.mp hprefix j.val).mp j.property
      exact congrFun har ⟨j.val, hj⟩
  apply Prod.ext
  · exact hfixed
  · funext k
    by_cases hk : k.val < marker.val
    · have hbefore :
          (context.sideRank.symm k).val ∈
            exactLeftPrefix seed := by
        rw [← exactReverseAliceContext_prefix_before_marked seed]
        apply (exactOrderedSidePrefix_mem_iff
          side context.sideRank marker.castSucc
          (context.sideRank.symm k).val).mpr
        refine ⟨(context.sideRank.symm k).property, ?_⟩
        change
          (context.sideRank (context.sideRank.symm k)).val <
            marker.val
        rw [Equiv.apply_symm_apply]
        exact hk
      have hy := congrFun hbl
        ⟨(context.sideRank.symm k).val, hbefore⟩
      change
        outcome.2.1 (context.sideRank.symm k).val.val =
          outcome'.2.1 (context.sideRank.symm k).val.val at hy
      have hkcut : k.val < seed.leftCut.val := by
        rw [← hmarker]
        exact hk
      simpa [finitePrefixMask,
        exactReverseAliceSourceProjection,
        exactReverseAliceContextAt,
        side, context, marker, hkcut] using hy
    · have hkcut : ¬ k.val < seed.leftCut.val := by
        rw [← hmarker]
        exact hk
      simp [finitePrefixMask,
        exactReverseAliceSourceProjection,
        exactReverseAliceContextAt,
        hkcut]

theorem exactReverseBobMaskedProjection_eq_of_history
    {n : ℕ} (D : Finset (Fin n))
    (default : X)
    (q q' : ExactJointOutcome X Y A B D)
    (same_history :
      exactHistoryCode D q =
        exactHistoryCode D q')
    (same_question :
      q.2.2.1 q.1.coordinate.val =
        q'.2.2.1 q'.1.coordinate.val) :
    finitePrefixMask
      default
      ((exactReverseBobContext q.1).sideRank
        ⟨q.1.coordinate,
          exactReverseRightSide_coordinate_mem q.1⟩).castSucc
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseRightSide q.1) q) =
    finitePrefixMask
      default
      ((exactReverseBobContext q.1).sideRank
        ⟨q.1.coordinate,
          exactReverseRightSide_coordinate_mem q.1⟩).castSucc
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseRightSide q.1) q') := by
  rcases q with ⟨seed, outcome⟩
  rcases q' with ⟨seed', outcome'⟩
  have hseed : seed = seed' :=
    congrArg (fun r : ExactHistoryFlag X Y A B D => r.seed)
      same_history
  subst seed'
  have htuple := congrArg
    (exactHistoryFlagEquiv
      (X := X) (Y := Y) (A := A) (B := B) D)
    same_history
  change
    (⟨seed,
       (exactRevealCode D seed
         (outcome.1, outcome.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D) =
    (⟨seed,
       (exactRevealCode D seed
         (outcome'.1, outcome'.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D) at htuple
  have hpair := eq_of_heq (Sigma.mk.inj htuple).2
  have hreveal :
      exactRevealCode D seed
          (outcome.1, outcome.2.1) =
        exactRevealCode D seed
          (outcome'.1, outcome'.2.1) :=
    congrArg Prod.fst hpair
  have hac := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.aliceConditioned) hreveal
  have hbc := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.bobConditioned) hreveal
  have hal := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.aliceLeft) hreveal
  have hbr := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.bobRight) hreveal
  have hbl := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.bobLeftPrefix) hreveal
  have har := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.aliceRightPrefix) hreveal
  let side := exactReverseRightSide seed
  let context := exactReverseBobContext seed
  let marker : Fin side.card :=
    context.sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
  have hmarker : marker.val = seed.rightCut.val := by
    exact exactReverseBobContext_marked_rank seed
  have hfixed :
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome)).1 =
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome')).1 := by
    simp only [side, exactReverseBobSourceProjection,
      exactReverseBobContextAt_actual]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Prod.ext
      · exact hac
      apply Prod.ext
      · exact hbc
      apply Prod.ext
      · funext j
        by_cases hj : j.val = seed.coordinate
        · have hval : j.val.val = seed.coordinate.val :=
            congrArg Subtype.val hj
          simpa [hval] using same_question
        · have hright :
              j.val ∈ exactRight
                seed.coordinate seed.partition := by
            have hmem :
                j.val ∈ insert seed.coordinate
                  (exactRight seed.coordinate seed.partition) :=
              j.property
            exact (Finset.mem_insert.mp hmem).resolve_left hj
          exact congrFun hbr ⟨j.val, hright⟩
      apply Prod.ext
      · funext j
        have hj :
            j.val ∈ exactLeft
              seed.coordinate seed.partition := by
          simpa [exactReverseBobContextAt,
            exactReverseBobContext] using j.property
        exact congrFun hal ⟨j.val, hj⟩
      funext j
      have hj : j.val ∈ exactLeftPrefix seed := by
        have hprefix :
            exactReverseContextOtherPrefix
              (exactReverseBobContextAt
                (exactReverseRightSide seed) seed) =
              exactLeftPrefix seed := by
          rw [exactReverseBobContextAt_actual,
            exactReverseBobContext_otherPrefix]
        exact (Finset.ext_iff.mp hprefix j.val).mp j.property
      exact congrFun hbl ⟨j.val, hj⟩
  apply Prod.ext
  · exact hfixed
  · funext k
    by_cases hk : k.val < marker.val
    · have hbefore :
          (context.sideRank.symm k).val ∈
            exactRightPrefix seed := by
        rw [← exactReverseBobContext_prefix_before_marked seed]
        apply (exactOrderedSidePrefix_mem_iff
          side context.sideRank marker.castSucc
          (context.sideRank.symm k).val).mpr
        refine ⟨(context.sideRank.symm k).property, ?_⟩
        change
          (context.sideRank (context.sideRank.symm k)).val <
            marker.val
        rw [Equiv.apply_symm_apply]
        exact hk
      have hx := congrFun har
        ⟨(context.sideRank.symm k).val, hbefore⟩
      change
        outcome.1 (context.sideRank.symm k).val.val =
          outcome'.1 (context.sideRank.symm k).val.val at hx
      have hkcut : k.val < seed.rightCut.val := by
        rw [← hmarker]
        exact hk
      simpa [finitePrefixMask,
        exactReverseBobSourceProjection,
        exactReverseBobContextAt,
        side, context, marker, hkcut] using hx
    · have hkcut : ¬ k.val < seed.rightCut.val := by
        rw [← hmarker]
        exact hk
      simp [finitePrefixMask,
        exactReverseBobSourceProjection,
        exactReverseBobContextAt,
        hkcut]

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem groupedMass_product_injective_seed
    {K Ω C T : Type*}
    [Fintype K] [Fintype Ω] [Fintype C] [Fintype T]
    [DecidableEq C] [DecidableEq T]
    (code : K → C) (injective : Function.Injective code)
    (projection : K → Ω → T)
    (seedWeight : K → ℝ) (outcomeWeight : Ω → ℝ)
    (seed : K) (target : T) :
    groupedMass
        (fun q : K × Ω => (code q.1, projection q.1 q.2))
        (fun q : K × Ω => seedWeight q.1 * outcomeWeight q.2)
        (code seed, target) =
      seedWeight seed *
        groupedMass (projection seed) outcomeWeight target := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter, Fintype.sum_prod_type,
    Finset.sum_filter, Finset.mul_sum]
  simp [injective.eq_iff]
  rw [Finset.sum_eq_single seed]
  · simp
  · intro other _ different
    simp [different]
  · simp

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem jointConditional_groupedMass_eq_of_fiber
    {Ω C D V : Type*}
    [Fintype Ω] [Fintype C] [Fintype D] [Fintype V]
    [DecidableEq (C × V)] [DecidableEq (D × V)]
    (mass : Ω → ℝ)
    (left : Ω → C) (right : Ω → D) (next : Ω → V)
    (leftTarget : C) (rightTarget : D)
    (same_fiber : ∀ outcome : Ω,
      left outcome = leftTarget ↔ right outcome = rightTarget) :
    jointConditional
        (groupedMass (fun outcome => (left outcome, next outcome)) mass)
        leftTarget =
      jointConditional
        (groupedMass (fun outcome => (right outcome, next outcome)) mass)
        rightTarget := by
  classical
  have hatom (value : V) :
      groupedMass
          (fun outcome => (left outcome, next outcome)) mass
          (leftTarget, value) =
        groupedMass
          (fun outcome => (right outcome, next outcome)) mass
          (rightTarget, value) := by
    unfold groupedMass
    apply Finset.sum_congr
    · ext outcome
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Prod.mk.injEq]
      exact and_congr_left (fun _ => same_fiber outcome)
    · intro outcome _
      rfl
  have hmarginal :
      jointFirstMarginal
          (groupedMass
            (fun outcome => (left outcome, next outcome)) mass)
          leftTarget =
        jointFirstMarginal
          (groupedMass
            (fun outcome => (right outcome, next outcome)) mass)
          rightTarget := by
    unfold jointFirstMarginal
    apply Finset.sum_congr rfl
    intro value _
    exact hatom value
  funext value
  unfold jointConditional
  rw [hatom value, hmarginal]

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactReverseAliceMarkedHistoryContext
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : Y)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseAliceNextContext X Y A B D
      (exactReverseLeftSide seed) :=
  let side := exactReverseLeftSide seed
  let marker :=
    (exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
  let projection :=
    exactReverseAliceSourceProjection
      (X := X) (Y := Y) (A := A) (B := B)
      D side (seed, outcome)
  finitePrefixMask default marker.castSucc
    ((projection.1,
      repeatedConditionedAnswerFlag G n S D outcome),
      projection.2)

def exactReverseBobMarkedHistoryContext
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseBobNextContext X Y A B D
      (exactReverseRightSide seed) :=
  let side := exactReverseRightSide seed
  let marker :=
    (exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
  let projection :=
    exactReverseBobSourceProjection
      (X := X) (Y := Y) (A := A) (B := B)
      D side (seed, outcome)
  finitePrefixMask default marker.castSucc
    ((projection.1,
      repeatedConditionedAnswerFlag G n S D outcome),
      projection.2)

theorem exactConditionedAnswerFlag_eq_of_history
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (q q' : ExactJointOutcome X Y A B D)
    (same_history :
      exactHistoryCode D q =
        exactHistoryCode D q') :
    repeatedConditionedAnswerFlag G n S D q.2 =
      repeatedConditionedAnswerFlag G n S D q'.2 := by
  apply Prod.ext
  · exact congrArg
      (fun r : ExactHistoryFlag X Y A B D => r.aliceAnswer)
      same_history
  · exact congrArg
      (fun r : ExactHistoryFlag X Y A B D => r.bobAnswer)
      same_history

theorem exactReverseAliceMarkedHistoryContext_eq_of_history
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : Y)
    (seed : ExactRemainingSeed D)
    (outcome outcome' : ExactOutcome X Y A B n)
    (same_history :
      exactHistoryCode D (seed, outcome) =
        exactHistoryCode D (seed, outcome'))
    (same_question :
      outcome.1 seed.coordinate.val =
        outcome'.1 seed.coordinate.val) :
    exactReverseAliceMarkedHistoryContext
        G n S D default seed outcome =
      exactReverseAliceMarkedHistoryContext
        G n S D default seed outcome' := by
  have hmask := exactReverseAliceMaskedProjection_eq_of_history
    (X := X) (Y := Y) (A := A) (B := B)
    D default (seed, outcome) (seed, outcome')
    same_history same_question
  have hflag := exactConditionedAnswerFlag_eq_of_history
    G n S D (seed, outcome) (seed, outcome') same_history
  have hfixed :
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseLeftSide seed) (seed, outcome)).1 =
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseLeftSide seed) (seed, outcome')).1 := by
    have h := congrArg
      (fun t :
        ExactReverseAliceFixedInformation X Y D
          (exactReverseLeftSide seed) ×
            (Fin (exactReverseLeftSide seed).card → Y) =>
        t.1) hmask
    simpa only [finitePrefixMask] using h
  have hprefix :
      (finitePrefixMask default
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩).castSucc
        (exactReverseAliceSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D (exactReverseLeftSide seed) (seed, outcome))).2 =
      (finitePrefixMask default
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩).castSucc
        (exactReverseAliceSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D (exactReverseLeftSide seed) (seed, outcome'))).2 := by
    exact congrArg
      (fun t :
        ExactReverseAliceFixedInformation X Y D
          (exactReverseLeftSide seed) ×
            (Fin (exactReverseLeftSide seed).card → Y) =>
        t.2) hmask
  unfold exactReverseAliceMarkedHistoryContext
  dsimp
  apply Prod.ext
  · apply Prod.ext
    · exact hfixed
    · exact hflag
  · exact hprefix

theorem exactReverseBobMarkedHistoryContext_eq_of_history
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (outcome outcome' : ExactOutcome X Y A B n)
    (same_history :
      exactHistoryCode D (seed, outcome) =
        exactHistoryCode D (seed, outcome'))
    (same_question :
      outcome.2.1 seed.coordinate.val =
        outcome'.2.1 seed.coordinate.val) :
    exactReverseBobMarkedHistoryContext
        G n S D default seed outcome =
      exactReverseBobMarkedHistoryContext
        G n S D default seed outcome' := by
  have hmask := exactReverseBobMaskedProjection_eq_of_history
    (X := X) (Y := Y) (A := A) (B := B)
    D default (seed, outcome) (seed, outcome')
    same_history same_question
  have hflag := exactConditionedAnswerFlag_eq_of_history
    G n S D (seed, outcome) (seed, outcome') same_history
  have hfixed :
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseRightSide seed) (seed, outcome)).1 =
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseRightSide seed) (seed, outcome')).1 := by
    have h := congrArg
      (fun t :
        ExactReverseBobFixedInformation X Y D
          (exactReverseRightSide seed) ×
            (Fin (exactReverseRightSide seed).card → X) =>
        t.1) hmask
    simpa only [finitePrefixMask] using h
  have hprefix :
      (finitePrefixMask default
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩).castSucc
        (exactReverseBobSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D (exactReverseRightSide seed) (seed, outcome))).2 =
      (finitePrefixMask default
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩).castSucc
        (exactReverseBobSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D (exactReverseRightSide seed) (seed, outcome'))).2 := by
    exact congrArg
      (fun t :
        ExactReverseBobFixedInformation X Y D
          (exactReverseRightSide seed) ×
            (Fin (exactReverseRightSide seed).card → X) =>
        t.2) hmask
  unfold exactReverseBobMarkedHistoryContext
  dsimp
  apply Prod.ext
  · apply Prod.ext
    · exact hfixed
    · exact hflag
  · exact hprefix

theorem exactReverseAlice_history_of_marked_context
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : Y)
    (seed : ExactRemainingSeed D)
    (outcome outcome' : ExactOutcome X Y A B n)
    (same_context :
      exactReverseAliceMarkedHistoryContext
          G n S D default seed outcome =
        exactReverseAliceMarkedHistoryContext
          G n S D default seed outcome') :
    outcome.1 seed.coordinate.val =
        outcome'.1 seed.coordinate.val ∧
      exactHistoryCode D (seed, outcome) =
        exactHistoryCode D (seed, outcome') := by
  let side := exactReverseLeftSide seed
  let context := exactReverseAliceContext seed
  let marker : Fin side.card :=
    context.sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
  have hfixed :
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome)).1 =
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome')).1 := by
    have h := congrArg
      (fun t : ExactReverseAliceNextContext
        X Y A B D (exactReverseLeftSide seed) => t.1.1)
      same_context
    simpa only [exactReverseAliceMarkedHistoryContext,
      finitePrefixMask, side] using h
  have hflag :
      repeatedConditionedAnswerFlag G n S D outcome =
        repeatedConditionedAnswerFlag G n S D outcome' := by
    have h := congrArg
      (fun t : ExactReverseAliceNextContext
        X Y A B D (exactReverseLeftSide seed) => t.1.2)
      same_context
    simpa only [exactReverseAliceMarkedHistoryContext,
      finitePrefixMask] using h
  have hprefix :
      (finitePrefixMask default marker.castSucc
        (exactReverseAliceSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D side (seed, outcome))).2 =
      (finitePrefixMask default marker.castSucc
        (exactReverseAliceSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D side (seed, outcome'))).2 := by
    have h := congrArg
      (fun t : ExactReverseAliceNextContext
        X Y A B D (exactReverseLeftSide seed) => t.2)
      same_context
    simpa only [exactReverseAliceMarkedHistoryContext,
      finitePrefixMask, side, context, marker] using h
  have hfields := eq_of_heq (Sigma.mk.inj hfixed).2
  have hac := congrArg (fun t => t.1) hfields
  have hbc := congrArg (fun t => t.2.1) hfields
  have hside := congrArg (fun t => t.2.2.1) hfields
  have hother := congrArg (fun t => t.2.2.2.1) hfields
  have hoppositePrefix := congrArg (fun t => t.2.2.2.2) hfields
  have hquestion :
      outcome.1 seed.coordinate.val =
        outcome'.1 seed.coordinate.val := by
    have h := congrFun hside
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
    exact h
  have hreveal :
      exactRevealCode D seed
          (outcome.1, outcome.2.1) =
        exactRevealCode D seed
          (outcome'.1, outcome'.2.1) := by
    apply (exactRevealHistoryEquiv
      (X := X) (Y := Y) D seed).injective
    apply Prod.ext
    · exact hac
    apply Prod.ext
    · exact hbc
    apply Prod.ext
    · funext j
      have hj : j.val ∈ side := by
        change j.val ∈ insert seed.coordinate
          (exactLeft seed.coordinate seed.partition)
        exact Finset.mem_insert_of_mem j.property
      exact congrFun hside ⟨j.val, hj⟩
    apply Prod.ext
    · funext j
      have hotherSide :
          (exactReverseAliceContextAt side seed).otherSide =
            exactRight seed.coordinate seed.partition := by
        change
          (exactReverseAliceContextAt
            (exactReverseLeftSide seed) seed).otherSide = _
        rw [exactReverseAliceContextAt_actual]
        rfl
      have hj :
          j.val ∈
            (exactReverseAliceContextAt side seed).otherSide :=
        (Finset.ext_iff.mp hotherSide j.val).mpr j.property
      exact congrFun hother ⟨j.val, hj⟩
    apply Prod.ext
    · funext j
      have hbefore :
          j.val ∈ exactReverseContextPrefixBefore
            context marker := by
        change
          j.val ∈ exactReverseContextPrefixBefore
            (exactReverseAliceContext seed)
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩)
        rw [exactReverseAliceContext_prefix_before_marked]
        exact j.property
      have hparts :=
        (exactOrderedSidePrefix_mem_iff
          side context.sideRank marker.castSucc j.val).mp
          (by simpa [exactReverseContextPrefixBefore]
            using hbefore)
      let position : Fin side.card :=
        context.sideRank ⟨j.val, hparts.1⟩
      have hlt : position.val < marker.val := by
        simpa [position] using hparts.2
      have hltCut : position.val < seed.leftCut.val := by
        calc
          position.val < marker.val := hlt
          _ = seed.leftCut.val := by
            exact exactReverseAliceContext_marked_rank seed
      have h := congrFun hprefix position
      change outcome.2.1 j.val.val = outcome'.2.1 j.val.val
      simpa [finitePrefixMask,
        exactReverseAliceSourceProjection,
        exactReverseAliceContextAt, side,
        context, marker, position, hlt, hltCut] using h
    · funext j
      have hotherPrefix :
          exactReverseContextOtherPrefix
              (exactReverseAliceContextAt side seed) =
            exactRightPrefix seed := by
        change
          exactReverseContextOtherPrefix
            (exactReverseAliceContextAt
              (exactReverseLeftSide seed) seed) = _
        rw [exactReverseAliceContextAt_actual,
          exactReverseAliceContext_otherPrefix]
      have hj :
          j.val ∈ exactReverseContextOtherPrefix
            (exactReverseAliceContextAt side seed) :=
        (Finset.ext_iff.mp hotherPrefix j.val).mpr j.property
      exact congrFun hoppositePrefix ⟨j.val, hj⟩
  refine ⟨hquestion, ?_⟩
  apply (exactHistoryFlagEquiv
    (X := X) (Y := Y) (A := A) (B := B) D).injective
  change
    (⟨seed,
       (exactRevealCode D seed (outcome.1, outcome.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D) =
    (⟨seed,
       (exactRevealCode D seed (outcome'.1, outcome'.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D)
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · exact hreveal
    apply Prod.ext
    · exact congrArg Prod.fst hflag
    · exact congrArg Prod.snd hflag

theorem exactReverseBob_history_of_marked_context
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (outcome outcome' : ExactOutcome X Y A B n)
    (same_context :
      exactReverseBobMarkedHistoryContext
          G n S D default seed outcome =
        exactReverseBobMarkedHistoryContext
          G n S D default seed outcome') :
    outcome.2.1 seed.coordinate.val =
        outcome'.2.1 seed.coordinate.val ∧
      exactHistoryCode D (seed, outcome) =
        exactHistoryCode D (seed, outcome') := by
  let side := exactReverseRightSide seed
  let context := exactReverseBobContext seed
  let marker : Fin side.card :=
    context.sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
  have hfixed :
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome)).1 =
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome')).1 := by
    have h := congrArg
      (fun t : ExactReverseBobNextContext
        X Y A B D (exactReverseRightSide seed) => t.1.1)
      same_context
    simpa only [exactReverseBobMarkedHistoryContext,
      finitePrefixMask, side] using h
  have hflag :
      repeatedConditionedAnswerFlag G n S D outcome =
        repeatedConditionedAnswerFlag G n S D outcome' := by
    have h := congrArg
      (fun t : ExactReverseBobNextContext
        X Y A B D (exactReverseRightSide seed) => t.1.2)
      same_context
    simpa only [exactReverseBobMarkedHistoryContext,
      finitePrefixMask] using h
  have hprefix :
      (finitePrefixMask default marker.castSucc
        (exactReverseBobSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D side (seed, outcome))).2 =
      (finitePrefixMask default marker.castSucc
        (exactReverseBobSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D side (seed, outcome'))).2 := by
    have h := congrArg
      (fun t : ExactReverseBobNextContext
        X Y A B D (exactReverseRightSide seed) => t.2)
      same_context
    simpa only [exactReverseBobMarkedHistoryContext,
      finitePrefixMask, side, context, marker] using h
  have hfields := eq_of_heq (Sigma.mk.inj hfixed).2
  have hac := congrArg (fun t => t.1) hfields
  have hbc := congrArg (fun t => t.2.1) hfields
  have hside := congrArg (fun t => t.2.2.1) hfields
  have hother := congrArg (fun t => t.2.2.2.1) hfields
  have hoppositePrefix := congrArg (fun t => t.2.2.2.2) hfields
  have hquestion :
      outcome.2.1 seed.coordinate.val =
        outcome'.2.1 seed.coordinate.val := by
    have h := congrFun hside
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
    exact h
  have hreveal :
      exactRevealCode D seed
          (outcome.1, outcome.2.1) =
        exactRevealCode D seed
          (outcome'.1, outcome'.2.1) := by
    apply (exactRevealHistoryEquiv
      (X := X) (Y := Y) D seed).injective
    apply Prod.ext
    · exact hac
    apply Prod.ext
    · exact hbc
    apply Prod.ext
    · funext j
      have hotherSide :
          (exactReverseBobContextAt side seed).otherSide =
            exactLeft seed.coordinate seed.partition := by
        change
          (exactReverseBobContextAt
            (exactReverseRightSide seed) seed).otherSide = _
        rw [exactReverseBobContextAt_actual]
        rfl
      have hj :
          j.val ∈
            (exactReverseBobContextAt side seed).otherSide :=
        (Finset.ext_iff.mp hotherSide j.val).mpr j.property
      exact congrFun hother ⟨j.val, hj⟩
    apply Prod.ext
    · funext j
      have hj : j.val ∈ side := by
        change j.val ∈ insert seed.coordinate
          (exactRight seed.coordinate seed.partition)
        exact Finset.mem_insert_of_mem j.property
      exact congrFun hside ⟨j.val, hj⟩
    apply Prod.ext
    · funext j
      have hotherPrefix :
          exactReverseContextOtherPrefix
              (exactReverseBobContextAt side seed) =
            exactLeftPrefix seed := by
        change
          exactReverseContextOtherPrefix
            (exactReverseBobContextAt
              (exactReverseRightSide seed) seed) = _
        rw [exactReverseBobContextAt_actual,
          exactReverseBobContext_otherPrefix]
      have hj :
          j.val ∈ exactReverseContextOtherPrefix
            (exactReverseBobContextAt side seed) :=
        (Finset.ext_iff.mp hotherPrefix j.val).mpr j.property
      exact congrFun hoppositePrefix ⟨j.val, hj⟩
    · funext j
      have hbefore :
          j.val ∈ exactReverseContextPrefixBefore
            context marker := by
        change
          j.val ∈ exactReverseContextPrefixBefore
            (exactReverseBobContext seed)
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩)
        rw [exactReverseBobContext_prefix_before_marked]
        exact j.property
      have hparts :=
        (exactOrderedSidePrefix_mem_iff
          side context.sideRank marker.castSucc j.val).mp
          (by simpa [exactReverseContextPrefixBefore]
            using hbefore)
      let position : Fin side.card :=
        context.sideRank ⟨j.val, hparts.1⟩
      have hlt : position.val < marker.val := by
        simpa [position] using hparts.2
      have hltCut : position.val < seed.rightCut.val := by
        calc
          position.val < marker.val := hlt
          _ = seed.rightCut.val := by
            exact exactReverseBobContext_marked_rank seed
      have h := congrFun hprefix position
      change outcome.1 j.val.val = outcome'.1 j.val.val
      simpa [finitePrefixMask,
        exactReverseBobSourceProjection,
        exactReverseBobContextAt, side,
        context, marker, position, hlt, hltCut] using h
  refine ⟨hquestion, ?_⟩
  apply (exactHistoryFlagEquiv
    (X := X) (Y := Y) (A := A) (B := B) D).injective
  change
    (⟨seed,
       (exactRevealCode D seed (outcome.1, outcome.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D) =
    (⟨seed,
       (exactRevealCode D seed (outcome'.1, outcome'.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D)
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · exact hreveal
    apply Prod.ext
    · exact congrArg Prod.fst hflag
    · exact congrArg Prod.snd hflag

theorem exactReverseAliceMarkedHistoryContext_fiber_iff
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : Y)
    (seed : ExactRemainingSeed D)
    (outcome reference : ExactOutcome X Y A B n) :
    (exactReverseAliceMarkedHistoryContext
        G n S D default seed outcome =
      exactReverseAliceMarkedHistoryContext
        G n S D default seed reference) ↔
      (outcome.1 seed.coordinate.val,
        exactHistoryCode D (seed, outcome)) =
      (reference.1 seed.coordinate.val,
        exactHistoryCode D (seed, reference)) := by
  constructor
  · intro same
    obtain ⟨hquestion, hhistory⟩ :=
      exactReverseAlice_history_of_marked_context
        G n S D default seed outcome reference same
    exact Prod.ext hquestion hhistory
  · intro same
    apply exactReverseAliceMarkedHistoryContext_eq_of_history
      G n S D default seed outcome reference
    · exact congrArg Prod.snd same
    · exact congrArg Prod.fst same

theorem exactReverseBobMarkedHistoryContext_fiber_iff
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (outcome reference : ExactOutcome X Y A B n) :
    (exactReverseBobMarkedHistoryContext
        G n S D default seed outcome =
      exactReverseBobMarkedHistoryContext
        G n S D default seed reference) ↔
      (outcome.2.1 seed.coordinate.val,
        exactHistoryCode D (seed, outcome)) =
      (reference.2.1 seed.coordinate.val,
        exactHistoryCode D (seed, reference)) := by
  constructor
  · intro same
    obtain ⟨hquestion, hhistory⟩ :=
      exactReverseBob_history_of_marked_context
        G n S D default seed outcome reference same
    exact Prod.ext hquestion hhistory
  · intro same
    apply exactReverseBobMarkedHistoryContext_eq_of_history
      G n S D default seed outcome reference
    · exact congrArg Prod.snd same
    · exact congrArg Prod.fst same

theorem exactReverseAliceMarkedPosteriorConditional_eq_sourceFiber
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
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            ((outcome.1 seed.coordinate.val,
              exactHistoryCode D (seed, outcome)),
              outcome.2.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (reference.1 seed.coordinate.val,
          exactHistoryCode D (seed, reference)) := by
  apply jointConditional_groupedMass_eq_of_fiber
    (repeatedConditionedOutcomeLaw G n S D)
    (fun outcome : ExactOutcome X Y A B n =>
      exactReverseAliceMarkedHistoryContext
        G n S D default seed outcome)
    (fun outcome : ExactOutcome X Y A B n =>
      (outcome.1 seed.coordinate.val,
        exactHistoryCode D (seed, outcome)))
    (fun outcome : ExactOutcome X Y A B n =>
      outcome.2.1 seed.coordinate.val)
    (exactReverseAliceMarkedHistoryContext
      G n S D default seed reference)
    (reference.1 seed.coordinate.val,
      exactHistoryCode D (seed, reference))
  intro outcome
  exact exactReverseAliceMarkedHistoryContext_fiber_iff
    G n S D default seed outcome reference

theorem exactReverseBobMarkedPosteriorConditional_eq_sourceFiber
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
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            ((outcome.2.1 seed.coordinate.val,
              exactHistoryCode D (seed, outcome)),
              outcome.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (reference.2.1 seed.coordinate.val,
          exactHistoryCode D (seed, reference)) := by
  apply jointConditional_groupedMass_eq_of_fiber
    (repeatedConditionedOutcomeLaw G n S D)
    (fun outcome : ExactOutcome X Y A B n =>
      exactReverseBobMarkedHistoryContext
        G n S D default seed outcome)
    (fun outcome : ExactOutcome X Y A B n =>
      (outcome.2.1 seed.coordinate.val,
        exactHistoryCode D (seed, outcome)))
    (fun outcome : ExactOutcome X Y A B n =>
      outcome.1 seed.coordinate.val)
    (exactReverseBobMarkedHistoryContext
      G n S D default seed reference)
    (reference.2.1 seed.coordinate.val,
      exactHistoryCode D (seed, reference))
  intro outcome
  exact exactReverseBobMarkedHistoryContext_fiber_iff
    G n S D default seed outcome reference

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem reweightedSeedPrefixPrior_as_flagged_pushforward
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ}
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (t : (Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) :
    reweightedSeedPrefixPrior
        seedLaw G n S D projection t =
      groupedMass
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          (((projection q.2).1, q.1), (projection q.2).2))
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (reweightedSeedPriorEventLaw
              seedLaw G n S).weight q.2)
        t := by
  classical
  change
    groupedMass projection
        (reweightedSeedPriorEventLaw seedLaw G n S).weight
        (t.1.1, t.2) *
      finiteUniformWeight
        (ConditionedAnswerFlag A B D) = _
  calc
    groupedMass projection
        (reweightedSeedPriorEventLaw seedLaw G n S).weight
        (t.1.1, t.2) *
      finiteUniformWeight
        (ConditionedAnswerFlag A B D) =
      finiteUniformWeight
        (ConditionedAnswerFlag A B D) *
        groupedMass projection
          (reweightedSeedPriorEventLaw seedLaw G n S).weight
          (t.1.1, t.2) := by
            ring
    _ = groupedMass
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          (q.1, projection q.2))
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (reweightedSeedPriorEventLaw
              seedLaw G n S).weight q.2)
        (t.1.2, (t.1.1, t.2)) := by
          symm
          exact groupedMass_product_injective_seed
            (fun z : ConditionedAnswerFlag A B D => z)
            (fun _ _ same => same)
            (fun (_ : ConditionedAnswerFlag A B D) q =>
              projection q)
            (fun _ : ConditionedAnswerFlag A B D =>
              finiteUniformWeight
                (ConditionedAnswerFlag A B D))
            (reweightedSeedPriorEventLaw seedLaw G n S).weight
            t.1.2 (t.1.1, t.2)
    _ = groupedMass
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          (((projection q.2).1, q.1), (projection q.2).2))
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (reweightedSeedPriorEventLaw
              seedLaw G n S).weight q.2)
        t := by
          unfold groupedMass
          congr 1
          ext q
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro same
            have hflag : q.1 = t.1.2 :=
              congrArg Prod.fst same
            have hprojection : projection q.2 = (t.1.1, t.2) :=
              congrArg Prod.snd same
            apply Prod.ext
            · apply Prod.ext
              · exact congrArg
                  (fun u : Ω × (Fin h → V) => u.1) hprojection
              · exact hflag
            · exact congrArg
                (fun u : Ω × (Fin h → V) => u.2) hprojection
          · intro same
            have hfixed :
                ((projection q.2).1, q.1) = t.1 :=
              congrArg Prod.fst same
            have hsequence : (projection q.2).2 = t.2 :=
              congrArg Prod.snd same
            apply Prod.ext
            · exact congrArg
                (fun u : Ω × ConditionedAnswerFlag A B D => u.2)
                hfixed
            · apply Prod.ext
              · exact congrArg
                  (fun u : Ω × ConditionedAnswerFlag A B D =>
                    u.1) hfixed
              · exact hsequence

theorem reweightedSeedPrefixPrior_next_flagged_pushforward
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ}
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (k : Fin h)
    (target :
      ((Ω × ConditionedAnswerFlag A B D) ×
        (Fin h → V)) × V) :
    groupedMass (exactPrefixNextCode default k)
        (reweightedSeedPrefixPrior
          seedLaw G n S D projection) target =
      groupedMass
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          exactPrefixNextCode default k
            (((projection q.2).1, q.1), (projection q.2).2))
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (reweightedSeedPriorEventLaw
              seedLaw G n S).weight q.2)
        target := by
  classical
  let augmented :
      ConditionedAnswerFlag A B D ×
        (K × ExactOutcome X Y A B n) →
          (Ω × ConditionedAnswerFlag A B D) ×
            (Fin h → V) :=
    fun q => (((projection q.2).1, q.1), (projection q.2).2)
  let weight :
      ConditionedAnswerFlag A B D ×
        (K × ExactOutcome X Y A B n) → ℝ :=
    fun q =>
      finiteUniformWeight
          (ConditionedAnswerFlag A B D) *
        (reweightedSeedPriorEventLaw
          seedLaw G n S).weight q.2
  have hprior :
      reweightedSeedPrefixPrior
          seedLaw G n S D projection =
        groupedMass augmented weight := by
    funext t
    exact reweightedSeedPrefixPrior_as_flagged_pushforward
      seedLaw G n S D projection t
  rw [hprior]
  exact congrFun
    (groupedMass_comp augmented
      (exactPrefixNextCode default k) weight) target

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem finiteGroupedExpectation_eq_atom_sum
    {Ω C : Type*} [Fintype Ω] [Fintype C] [DecidableEq C]
    (code : Ω → C) (mass : Ω → ℝ) (value : C → ℝ) :
    (∑ target : C, groupedMass code mass target * value target) =
      ∑ outcome : Ω, mass outcome * value (code outcome) := by
  classical
  unfold groupedMass
  calc
    (∑ target : C,
      (∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          code outcome = target), mass outcome) * value target) =
      ∑ target : C,
        ∑ outcome ∈
          (Finset.univ.filter fun outcome : Ω =>
            code outcome = target),
          mass outcome * value (code outcome) := by
        apply Finset.sum_congr rfl
        intro target _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro outcome houtcome
        have hcode : code outcome = target :=
          (Finset.mem_filter.mp houtcome).2
        rw [hcode]
    _ = ∑ outcome : Ω, mass outcome * value (code outcome) :=
      Finset.sum_fiberwise Finset.univ code
        (fun outcome => mass outcome * value (code outcome))

theorem jointFirstMarginal_groupedContextNext
    {Ω C V : Type*} [Fintype Ω] [Fintype C] [Fintype V]
    [DecidableEq C] [DecidableEq (C × V)]
    (context : Ω → C) (next : Ω → V)
    (mass : Ω → ℝ) (target : C) :
    jointFirstMarginal
        (groupedMass
          (fun outcome => (context outcome, next outcome)) mass)
        target =
      groupedMass context mass target := by
  classical
  unfold jointFirstMarginal groupedMass
  calc
    (∑ value : V,
      ∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          (context outcome, next outcome) = (target, value)),
        mass outcome) =
      ∑ value : V,
        ∑ outcome ∈
          ((Finset.univ.filter fun outcome : Ω =>
            context outcome = target).filter
              fun outcome => next outcome = value),
          mass outcome := by
        apply Finset.sum_congr rfl
        intro value _
        congr 1
        ext outcome
        simp [Prod.mk.injEq]
    _ = ∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          context outcome = target), mass outcome :=
      Finset.sum_fiberwise
        (Finset.univ.filter fun outcome : Ω =>
          context outcome = target)
        next mass

theorem finiteNextInformation_eq_atom_sum
    {Ω C V : Type*} [Fintype Ω] [Fintype C] [Fintype V]
    [DecidableEq C] [DecidableEq (C × V)]
    (context : Ω → C) (next : Ω → V)
    (mass : Ω → ℝ) (reference : C → V → ℝ) :
    (∑ target : C,
      jointFirstMarginal
          (groupedMass
            (fun outcome => (context outcome, next outcome)) mass)
          target *
        finiteRelativeEntropy
          (jointConditional
            (groupedMass
              (fun outcome => (context outcome, next outcome)) mass)
            target)
          (reference target)) =
      ∑ outcome : Ω,
        mass outcome *
          finiteRelativeEntropy
            (jointConditional
              (groupedMass
                (fun source => (context source, next source)) mass)
              (context outcome))
            (reference (context outcome)) := by
  simp_rw [jointFirstMarginal_groupedContextNext
    context next mass]
  exact finiteGroupedExpectation_eq_atom_sum
    context mass
    (fun target =>
      finiteRelativeEntropy
        (jointConditional
          (groupedMass
            (fun outcome => (context outcome, next outcome)) mass)
          target)
        (reference target))

theorem jointAtom_eq_zero_of_firstMarginal_zero
    {I V : Type*} [Fintype I] [Fintype V]
    (mass : I × V → ℝ)
    (nonnegative : ∀ point, 0 ≤ mass point)
    (index : I)
    (zero : jointFirstMarginal mass index = 0)
    (value : V) :
    mass (index, value) = 0 := by
  unfold jointFirstMarginal at zero
  exact
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun value _ => nonnegative (index, value))).mp
      zero value (Finset.mem_univ value)

theorem nestedFirstMarginal_mul_conditional
    {I R V : Type*} [Fintype I] [Fintype R] [Fintype V]
    (mass : I × (R × V) → ℝ)
    (nonnegative : ∀ point, 0 ≤ mass point)
    (index : I) (history : R) :
    jointFirstMarginal mass index *
        jointFirstMarginal (jointConditional mass index) history =
    jointFirstMarginal
        (fun point : (I × R) × V =>
          mass (point.1.1, (point.1.2, point.2)))
        (index, history) := by
  unfold jointFirstMarginal jointConditional
  change
    (∑ point : R × V, mass (index, point)) *
        (∑ value : V,
          mass (index, (history, value)) /
            (∑ point : R × V, mass (index, point))) =
      ∑ value : V, mass (index, (history, value))
  rw [← Finset.sum_div]
  by_cases houter : (∑ point : R × V, mass (index, point)) = 0
  · have hinner : (∑ value : V, mass (index, (history, value))) = 0 := by
      apply Finset.sum_eq_zero
      intro value _
      exact jointAtom_eq_zero_of_firstMarginal_zero
        mass nonnegative index houter (history, value)
    simp [houter, hinner]
  · field_simp [houter]

theorem nestedConditional_eq_flat
    {I R V : Type*} [Fintype I] [Fintype R] [Fintype V]
    (mass : I × (R × V) → ℝ)
    (nonnegative : ∀ point, 0 ≤ mass point)
    (index : I) (history : R) :
    jointConditional (jointConditional mass index) history =
      jointConditional
        (fun point : (I × R) × V =>
          mass (point.1.1, (point.1.2, point.2)))
        (index, history) := by
  funext value
  unfold jointConditional jointFirstMarginal
  rw [← Finset.sum_div]
  by_cases houter : (∑ point : R × V, mass (index, point)) = 0
  · have hatom : mass (index, (history, value)) = 0 :=
      jointAtom_eq_zero_of_firstMarginal_zero
        mass nonnegative index houter (history, value)
    simp [houter, hatom]
  · by_cases hhistory : (∑ v : V, mass (index, (history, v))) = 0
    · have hatom : mass (index, (history, value)) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun v _ => nonnegative (index, (history, v)))).mp
          hhistory value (Finset.mem_univ value)
      simp [hatom, hhistory]
    · field_simp [houter, hhistory]

theorem finiteNestedNextInformation_eq_atom_sum
    {I R V : Type*} [Fintype I] [Fintype R] [Fintype V]
    (mass : I × (R × V) → ℝ)
    (nonnegative : ∀ point, 0 ≤ mass point)
    (reference : I → V → ℝ) :
    (∑ index : I,
      jointFirstMarginal mass index *
        (∑ history : R,
          jointFirstMarginal
              (jointConditional mass index) history *
            finiteRelativeEntropy
              (jointConditional
                (jointConditional mass index) history)
              (reference index))) =
      ∑ point : I × (R × V),
        mass point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom : (I × R) × V =>
                mass (atom.1.1, (atom.1.2, atom.2)))
              (point.1, point.2.1))
            (reference point.1) := by
  classical
  simp_rw [Finset.mul_sum]
  simp_rw [← mul_assoc,
    nestedFirstMarginal_mul_conditional mass nonnegative,
    nestedConditional_eq_flat mass nonnegative]
  let flat : (I × R) × V → ℝ :=
    fun atom => mass (atom.1.1, (atom.1.2, atom.2))
  let score : I × R → ℝ :=
    fun target =>
      finiteRelativeEntropy
        (jointConditional flat target)
        (reference target.1)
  have h := finiteGroupedExpectation_eq_atom_sum
    (fun atom : (I × R) × V => atom.1) flat score
  have hfirst (target : I × R) :
      groupedMass
          (fun atom : (I × R) × V => atom.1)
          flat target =
        jointFirstMarginal flat target := by
    exact congrFun (groupedMass_first flat) target
  simp_rw [hfirst] at h
  change
    (∑ index : I, ∑ history : R,
      jointFirstMarginal flat (index, history) *
        score (index, history)) = _
  calc
    (∑ index : I, ∑ history : R,
      jointFirstMarginal flat (index, history) *
        score (index, history)) =
      ∑ target : I × R,
        jointFirstMarginal flat target * score target := by
          rw [Fintype.sum_prod_type]
    _ = ∑ atom : (I × R) × V,
        flat atom * score atom.1 := h
    _ = ∑ point : I × (R × V),
        mass point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom : (I × R) × V =>
                mass (atom.1.1, (atom.1.2, atom.2)))
              (point.1, point.2.1))
            (reference point.1) := by
          simp only [flat, score, Fintype.sum_prod_type]

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem reweightedSeedPrefixJoint_as_actual_flagged_pushforward
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ}
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (target : (Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) :
    reweightedSeedPrefixJoint
        seedLaw G n S D projection target =
      groupedMass
        (fun point : K × ExactOutcome X Y A B n =>
          (((projection point).1,
            repeatedConditionedAnswerFlag G n S D point.2),
            (projection point).2))
        (reweightedSeedPosterior seedLaw G n S D)
        target := by
  classical
  unfold reweightedSeedPrefixJoint
    reweightedSeedFlaggedProjectionLaw groupedMass
  apply Finset.sum_congr
  · ext point
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      exactSourcePrefixFlagEquiv]
    change
      ((projection point,
          repeatedConditionedAnswerFlag G n S D point.2) =
        ((target.1.1, target.2), target.1.2)) ↔
      (((projection point).1,
          repeatedConditionedAnswerFlag G n S D point.2),
        (projection point).2) = target
    constructor
    · intro same
      have hprojection :
          projection point = (target.1.1, target.2) :=
        congrArg
          (fun t :
            (Ω × (Fin h → V)) × ConditionedAnswerFlag A B D =>
            t.1) same
      have hflag :
          repeatedConditionedAnswerFlag G n S D point.2 =
            target.1.2 :=
        congrArg
          (fun t :
            (Ω × (Fin h → V)) × ConditionedAnswerFlag A B D =>
            t.2) same
      apply Prod.ext
      · apply Prod.ext
        · exact congrArg
            (fun t : Ω × (Fin h → V) => t.1) hprojection
        · exact hflag
      · exact congrArg
          (fun t : Ω × (Fin h → V) => t.2) hprojection
    · intro same
      have hfixed :
          ((projection point).1,
            repeatedConditionedAnswerFlag G n S D point.2) =
            target.1 :=
        congrArg
          (fun t :
            (Ω × ConditionedAnswerFlag A B D) ×
              (Fin h → V) => t.1) same
      have hsequence : (projection point).2 = target.2 :=
        congrArg
          (fun t :
            (Ω × ConditionedAnswerFlag A B D) ×
              (Fin h → V) => t.2) same
      apply Prod.ext
      · apply Prod.ext
        · exact congrArg
            (fun t : Ω × ConditionedAnswerFlag A B D => t.1)
            hfixed
        · exact hsequence
      · exact congrArg
          (fun t : Ω × ConditionedAnswerFlag A B D => t.2)
          hfixed
  · intro point _
    rfl

theorem exactAliceSourceConditionalInformation_eq_atom_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceConditionalInformation G n S D base =
      ∑ point : (SourceRemainingCoordinate D × X) ×
          (ExactHistoryFlag X Y A B D × Y),
        exactAliceInformationPosterior G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom :
                ((SourceRemainingCoordinate D × X) ×
                    ExactHistoryFlag X Y A B D) × Y =>
                exactAliceInformationPosterior G n S D
                  (atom.1.1, (atom.1.2, atom.2)))
              (point.1, point.2.1))
            (G.conditionalYGivenX point.1.2) := by
  have hnonnegative :
      ∀ point,
        0 ≤ exactAliceInformationPosterior
          G n S D point := by
    intro point
    exact exactLocallySampleableLaw_nonneg
      G n S D positive
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm point)
  calc
    exactAliceSourceConditionalInformation G n S D base =
      ∑ index : SourceRemainingCoordinate D × X,
        jointFirstMarginal
          (exactAliceInformationPosterior G n S D) index *
          (∑ history : ExactHistoryFlag X Y A B D,
            jointFirstMarginal
                (jointConditional
                  (exactAliceInformationPosterior G n S D)
                  index) history *
              finiteRelativeEntropy
                (jointConditional
                  (jointConditional
                    (exactAliceInformationPosterior G n S D)
                    index) history)
                (G.conditionalYGivenX index.2)) :=
      exactAliceSourceConditionalInformation_eq_question
        G n S D remaining positive base
    _ = _ :=
      finiteNestedNextInformation_eq_atom_sum
        (exactAliceInformationPosterior G n S D)
        hnonnegative
        (fun index : SourceRemainingCoordinate D × X =>
          G.conditionalYGivenX index.2)

theorem exactBobSourceConditionalInformation_eq_atom_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactBobSourceConditionalInformation G n S D base =
      ∑ point : (SourceRemainingCoordinate D × Y) ×
          (ExactHistoryFlag X Y A B D × X),
        exactBobInformationPosterior G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom :
                ((SourceRemainingCoordinate D × Y) ×
                    ExactHistoryFlag X Y A B D) × X =>
                exactBobInformationPosterior G n S D
                  (atom.1.1, (atom.1.2, atom.2)))
              (point.1, point.2.1))
            (G.conditionalXGivenY point.1.2) := by
  have hnonnegative :
      ∀ point,
        0 ≤ exactBobInformationPosterior
          G n S D point := by
    intro point
    exact exactLocallySampleableLaw_nonneg
      G n S D positive
      ((exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm point)
  calc
    exactBobSourceConditionalInformation G n S D base =
      ∑ index : SourceRemainingCoordinate D × Y,
        jointFirstMarginal
          (exactBobInformationPosterior G n S D) index *
          (∑ history : ExactHistoryFlag X Y A B D,
            jointFirstMarginal
                (jointConditional
                  (exactBobInformationPosterior G n S D)
                  index) history *
              finiteRelativeEntropy
                (jointConditional
                  (jointConditional
                    (exactBobInformationPosterior G n S D)
                    index) history)
                (G.conditionalXGivenY index.2)) :=
      exactBobSourceConditionalInformation_eq_question
        G n S D remaining positive base
    _ = _ :=
      finiteNestedNextInformation_eq_atom_sum
        (exactBobInformationPosterior G n S D)
        hnonnegative
        (fun index : SourceRemainingCoordinate D × Y =>
          G.conditionalXGivenY index.2)

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

theorem exactPermutationOutputUniformPushforward
    {R : Type*} [Fintype R] [DecidableEq R]
    (denominator : ℕ) (numerator : R → ℕ)
    (normalized : (∑ r, numerator r) = denominator)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (letter : R) :
    groupedMass
        (rationalPermutationOutput denominator numerator nonempty)
        (fun _ : Equiv.Perm (R × Fin denominator) =>
          (1 : ℝ) / (Fintype.card
            (Equiv.Perm (R × Fin denominator)) : ℝ)) letter =
      (numerator letter : ℝ) / denominator := by
  classical
  calc
    groupedMass
        (rationalPermutationOutput denominator numerator nonempty)
        (fun _ : Equiv.Perm (R × Fin denominator) =>
          (1 : ℝ) / (Fintype.card
            (Equiv.Perm (R × Fin denominator)) : ℝ)) letter =
      uniformPermutationProbability
        (fun permutation : Equiv.Perm (R × Fin denominator) =>
          rationalPermutationOutput denominator numerator nonempty
            permutation = letter) := by
        rw [exactUniformPermutationProbability_eq_indicator_sum]
        unfold groupedMass
        rw [Finset.sum_filter, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro permutation _
        by_cases selected :
          rationalPermutationOutput denominator numerator nonempty
            permutation = letter
        · simp [selected]
        · simp [selected]
    _ = (numerator letter : ℝ) / denominator :=
      rationalPermutationOutput_probability denominator numerator
        normalized nonempty letter

theorem exactPermutationOutputUniformExpectation
    {R : Type*} [Fintype R] [DecidableEq R]
    (denominator : ℕ) (numerator : R → ℕ)
    (normalized : (∑ r, numerator r) = denominator)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (value : R → ℝ) :
    (∑ permutation : Equiv.Perm (R × Fin denominator),
      ((1 : ℝ) /
        (Fintype.card (Equiv.Perm (R × Fin denominator)) : ℝ)) *
          value (rationalPermutationOutput denominator numerator
            nonempty permutation)) =
      ∑ letter : R, ((numerator letter : ℝ) / denominator) *
        value letter := by
  calc
    (∑ permutation : Equiv.Perm (R × Fin denominator),
      ((1 : ℝ) /
        (Fintype.card (Equiv.Perm (R × Fin denominator)) : ℝ)) *
          value (rationalPermutationOutput denominator numerator
            nonempty permutation)) =
      ∑ letter : R,
        groupedMass
          (rationalPermutationOutput denominator numerator nonempty)
          (fun _ : Equiv.Perm (R × Fin denominator) =>
            (1 : ℝ) /
              (Fintype.card (Equiv.Perm
                (R × Fin denominator)) : ℝ)) letter * value letter :=
        (finiteGroupedExpectation_eq_atom_sum
          (rationalPermutationOutput denominator numerator nonempty)
          (fun _ : Equiv.Perm (R × Fin denominator) =>
            (1 : ℝ) /
              (Fintype.card (Equiv.Perm
                (R × Fin denominator)) : ℝ)) value).symm
    _ = ∑ letter : R,
      ((numerator letter : ℝ) / denominator) * value letter := by
        simp_rw [exactPermutationOutputUniformPushforward
          denominator numerator normalized nonempty]

def exactSourceAliceSampleTuple
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y)) :
    ExactLocallySampleableTuple X Y A B D :=
  (outcome.1.1, outcome.2.1, outcome.2.2,
    exactSourceAlicePermutationHistory
      D denominator numerator nonempty outcome.1 outcome.2.1)

theorem exactSourceAliceSampleTuple_expectation
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ k, (∑ r, numerator k r) = denominator)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (value : ExactLocallySampleableTuple X Y A B D → ℝ) :
    (∑ outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator) outcome *
          value (exactSourceAliceSampleTuple
            D denominator numerator nonempty outcome)) =
      ∑ history : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableJARounded
          G n D denominator numerator history * value history := by
  classical
  have point (coordinate : SourceRemainingCoordinate D)
      (x : X) (y : Y) :
      (∑ permutation :
        Equiv.Perm
          (ExactHistoryFlag X Y A B D × Fin denominator),
        ((1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
          (1 / (Fintype.card
            (Equiv.Perm
              (ExactHistoryFlag X Y A B D ×
                Fin denominator)) : ℝ))) *
          G.questionWeight x y *
          value (coordinate, x, y,
            rationalPermutationOutput denominator
              (numerator (.inl (coordinate, x)))
              (nonempty (.inl (coordinate, x))) permutation)) =
        ∑ history : ExactHistoryFlag X Y A B D,
          (G.questionWeight x y *
            ((numerator (.inl (coordinate, x)) history : ℝ) /
              denominator) /
              (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            value (coordinate, x, y, history) := by
    have output := exactPermutationOutputUniformExpectation
      denominator (numerator (.inl (coordinate, x)))
      (normalized (.inl (coordinate, x)))
      (nonempty (.inl (coordinate, x)))
      (fun history : ExactHistoryFlag X Y A B D =>
        value (coordinate, x, y, history))
    calc
      (∑ permutation :
        Equiv.Perm
          (ExactHistoryFlag X Y A B D × Fin denominator),
        ((1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
          (1 / (Fintype.card
            (Equiv.Perm
              (ExactHistoryFlag X Y A B D ×
                Fin denominator)) : ℝ))) *
          G.questionWeight x y *
          value (coordinate, x, y,
            rationalPermutationOutput denominator
              (numerator (.inl (coordinate, x)))
              (nonempty (.inl (coordinate, x))) permutation)) =
        (G.questionWeight x y /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
          (∑ permutation :
            Equiv.Perm
              (ExactHistoryFlag X Y A B D × Fin denominator),
            ((1 : ℝ) /
              (Fintype.card
                (Equiv.Perm
                  (ExactHistoryFlag X Y A B D ×
                    Fin denominator)) : ℝ)) *
              value (coordinate, x, y,
                rationalPermutationOutput denominator
                  (numerator (.inl (coordinate, x)))
                  (nonempty (.inl (coordinate, x))) permutation)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro permutation _
            ring
      _ = (G.questionWeight x y /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
          (∑ history : ExactHistoryFlag X Y A B D,
            ((numerator (.inl (coordinate, x)) history : ℝ) /
              denominator) * value (coordinate, x, y, history)) := by
            rw [output]
      _ = ∑ history : ExactHistoryFlag X Y A B D,
          (G.questionWeight x y *
            ((numerator (.inl (coordinate, x)) history : ℝ) /
              denominator) /
              (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            value (coordinate, x, y, history) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro history _
            ring
  simp only [flaggedQuestionWeight,
    exactSourceSharedFlagWeight,
    exactSourceAliceSampleTuple,
    exactSourceAlicePermutationHistory,
    exactLocallySampleableJARounded,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  exact point coordinate x y

theorem exactSourceAliceSampleTuple_groupedMass
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ k, (∑ r, numerator k r) = denominator)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (history : ExactLocallySampleableTuple X Y A B D) :
    groupedMass
      (exactSourceAliceSampleTuple
        D denominator numerator nonempty)
      (flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator)) history =
      exactLocallySampleableJARounded
        G n D denominator numerator history := by
  classical
  have expectation := exactSourceAliceSampleTuple_expectation
    G n D denominator numerator normalized nonempty
    (fun candidate => if candidate = history then (1 : ℝ) else 0)
  simpa [groupedMass, Finset.sum_filter, mul_ite] using expectation

end

noncomputable section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]

def exactFiniteFiberLift
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (outcome : Ω) : ℝ :=
  target (projection outcome) * original outcome /
    groupedMass projection original (projection outcome)

omit [Fintype T] in

theorem exactFiniteFiberLift_groupedMass
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0)
    (point : T) :
    groupedMass projection
      (exactFiniteFiberLift projection original target) point =
        target point := by
  classical
  change
    (∑ outcome ∈
      (Finset.univ.filter fun outcome : Ω =>
        projection outcome = point),
      exactFiniteFiberLift projection original target outcome) =
        target point
  calc
    (∑ outcome ∈
      (Finset.univ.filter fun outcome : Ω =>
        projection outcome = point),
      exactFiniteFiberLift projection original target outcome) =
      ∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          projection outcome = point),
        target point * original outcome /
          groupedMass projection original point := by
          apply Finset.sum_congr rfl
          intro outcome member
          have same : projection outcome = point :=
            (Finset.mem_filter.mp member).2
          simp [exactFiniteFiberLift, same]
    _ = target point * groupedMass projection original point /
          groupedMass projection original point := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
          rfl
    _ = target point := by
          by_cases empty : groupedMass projection original point = 0
          · simp [empty, supported point empty]
          · field_simp

theorem exactFiniteFiberLift_expectation
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0)
    (value : T → ℝ) :
    (∑ outcome : Ω,
      exactFiniteFiberLift projection original target outcome *
        value (projection outcome)) =
      ∑ point : T, target point * value point := by
  calc
    (∑ outcome : Ω,
      exactFiniteFiberLift projection original target outcome *
        value (projection outcome)) =
      ∑ point : T,
        groupedMass projection
          (exactFiniteFiberLift projection original target) point *
            value point :=
      (finiteGroupedExpectation_eq_atom_sum projection
        (exactFiniteFiberLift projection original target)
        value).symm
    _ = ∑ point : T, target point * value point := by
      simp_rw [exactFiniteFiberLift_groupedMass
        projection original target supported]

omit [Fintype T] in

theorem exactFiniteFiberLift_absolute_groupedMass
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (original_nonnegative : ∀ outcome, 0 ≤ original outcome)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0)
    (point : T) :
    groupedMass projection
      (fun outcome =>
        |original outcome -
          exactFiniteFiberLift projection original target outcome|)
      point =
        |groupedMass projection original point - target point| := by
  classical
  by_cases empty : groupedMass projection original point = 0
  · have vanishes : ∀ outcome,
        outcome ∈ (Finset.univ.filter fun outcome : Ω =>
          projection outcome = point) → original outcome = 0 := by
      intro outcome member
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun outcome _ => original_nonnegative outcome)).mp
          (show
            (∑ outcome ∈
              (Finset.univ.filter fun outcome : Ω =>
                projection outcome = point),
              original outcome) = 0 from empty)
          outcome member
    unfold groupedMass
    rw [Finset.sum_eq_zero (fun outcome member => by
      have zero := vanishes outcome member
      simp [exactFiniteFiberLift, zero])]
    simpa [supported point empty, groupedMass] using
      (congrArg abs empty).symm
  · have pointwise (outcome : Ω)
        (member : outcome ∈
          (Finset.univ.filter fun outcome : Ω =>
            projection outcome = point)) :
        |original outcome -
          exactFiniteFiberLift projection original target outcome| =
          original outcome *
            |groupedMass projection original point - target point| /
              groupedMass projection original point := by
      have same : projection outcome = point :=
        (Finset.mem_filter.mp member).2
      have mass_nonnegative :
          0 ≤ groupedMass projection original point := by
        unfold groupedMass
        exact Finset.sum_nonneg
          (fun outcome _ => original_nonnegative outcome)
      have mass_positive :
          0 < groupedMass projection original point :=
        lt_of_le_of_ne mass_nonnegative (Ne.symm empty)
      rw [exactFiniteFiberLift, same]
      rw [show original outcome -
          target point * original outcome /
            groupedMass projection original point =
          original outcome *
            (groupedMass projection original point - target point) /
              groupedMass projection original point by
            field_simp]
      rw [abs_div, abs_mul,
        abs_of_nonneg (original_nonnegative outcome),
        abs_of_pos mass_positive]
    change
      (∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          projection outcome = point),
        |original outcome -
          exactFiniteFiberLift projection original target outcome|) =
        |groupedMass projection original point - target point|
    calc
      (∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          projection outcome = point),
        |original outcome -
          exactFiniteFiberLift projection original target outcome|) =
        ∑ outcome ∈
          (Finset.univ.filter fun outcome : Ω =>
            projection outcome = point),
          original outcome *
            |groupedMass projection original point - target point| /
              groupedMass projection original point := by
          apply Finset.sum_congr rfl
          exact pointwise
      _ = groupedMass projection original point *
          |groupedMass projection original point - target point| /
            groupedMass projection original point := by
          rw [← Finset.sum_div, ← Finset.sum_mul]
          rfl
      _ = |groupedMass projection original point - target point| := by
          field_simp

theorem exactFiniteFiberLift_totalVariation
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (original_nonnegative : ∀ outcome, 0 ≤ original outcome)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0) :
    finiteTotalVariation original
      (exactFiniteFiberLift projection original target) =
        finiteTotalVariation (groupedMass projection original) target := by
  unfold finiteTotalVariation
  congr 1
  calc
    (∑ outcome : Ω,
      |original outcome -
        exactFiniteFiberLift projection original target outcome|) =
      ∑ point : T,
        groupedMass projection
          (fun outcome =>
            |original outcome -
              exactFiniteFiberLift projection original target outcome|)
          point := by
        simpa using
          (finiteGroupedExpectation_eq_atom_sum projection
            (fun outcome =>
              |original outcome -
                exactFiniteFiberLift
                  projection original target outcome|)
            (fun _ => (1 : ℝ))).symm
    _ = ∑ point : T,
      |groupedMass projection original point - target point| := by
        simp_rw [exactFiniteFiberLift_absolute_groupedMass
          projection original target original_nonnegative supported]

end

noncomputable section

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem existsCommonSupportPreservingRationalApproximations
    {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (base : I) (probability : K → I → ℝ)
    (nonnegative : ∀ index letter, 0 ≤ probability index letter)
    (normalized : ∀ index, (∑ letter, probability index letter) = 1)
    {gamma : ℝ} (gamma_positive : 0 < gamma) :
    ∃ denominator : ℕ, 0 < denominator ∧
      ∃ numerator : K → I → ℕ,
        (∀ index, (∑ letter, numerator index letter) = denominator) ∧
        (∀ index, finiteTotalVariation
          (probability index)
          (fun letter => (numerator index letter : ℝ) / denominator) <
            gamma) ∧
        (∀ index letter,
          0 < probability index letter → 0 < numerator index letter) := by
  classical
  let supportCost : ℝ :=
    ∑ index : K, ∑ letter : I,
      if 0 < probability index letter then
        1 / probability index letter
      else 0
  have cost_nonnegative : 0 ≤ supportCost := by
    dsimp [supportCost]
    apply Finset.sum_nonneg
    intro index _
    apply Finset.sum_nonneg
    intro letter _
    split_ifs with positive
    · exact (one_div_pos.mpr positive).le
    · exact le_rfl
  have cardinal_positive : 0 < (Fintype.card I : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨base⟩ : 0 < Fintype.card I)
  have ratio_positive :
      0 < (Fintype.card I : ℝ) / gamma :=
    div_pos cardinal_positive gamma_positive
  obtain ⟨denominator, denominator_large⟩ :=
    exists_nat_gt ((Fintype.card I : ℝ) / gamma + supportCost)
  have denominator_real_positive : 0 < (denominator : ℝ) :=
    lt_of_lt_of_le
      (lt_of_lt_of_le ratio_positive
        (le_add_of_nonneg_right cost_nonnegative))
      denominator_large.le
  have denominator_positive : 0 < denominator := by
    exact_mod_cast denominator_real_positive
  have approximation_budget :
      (Fintype.card I : ℝ) / denominator < gamma := by
    apply (div_lt_iff₀ denominator_real_positive).mpr
    have reciprocal_bound :
        (Fintype.card I : ℝ) / gamma < (denominator : ℝ) :=
      lt_of_le_of_lt
        (le_add_of_nonneg_right cost_nonnegative)
        denominator_large
    have crossed :=
      (div_lt_iff₀ gamma_positive).mp reciprocal_bound
    nlinarith
  refine ⟨denominator, denominator_positive,
    fun index => distributionRoundedNumerator
      base denominator (probability index), ?_, ?_, ?_⟩
  · intro index
    exact distributionRoundedNumerator_sum
      base denominator (probability index)
      (nonnegative index) (normalized index)
  · intro index
    change finiteTotalVariation
      (probability index)
      (distributionRoundedProbability
        base denominator (probability index)) < gamma
    exact (distributionRoundedProbability_totalVariation_le
      base denominator denominator_positive
      (probability index) (nonnegative index)
      (normalized index)).trans_lt approximation_budget
  · intro index letter genuinely_positive
    have letter_le_inner :
        1 / probability index letter ≤
          ∑ candidate : I,
            if 0 < probability index candidate then
              1 / probability index candidate
            else 0 := by
      have single := Finset.single_le_sum
        (s := (Finset.univ : Finset I))
        (f := fun candidate : I =>
          if 0 < probability index candidate then
            1 / probability index candidate
          else 0)
        (fun candidate _ => by
          split_ifs with positive
          · exact (one_div_pos.mpr positive).le
          · exact le_rfl)
        (Finset.mem_univ letter)
      simpa [genuinely_positive] using single
    have inner_le_cost :
        (∑ candidate : I,
          if 0 < probability index candidate then
            1 / probability index candidate
          else 0) ≤ supportCost := by
      dsimp [supportCost]
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset K))
        (f := fun current : K =>
          ∑ candidate : I,
            if 0 < probability current candidate then
              1 / probability current candidate
            else 0)
        (fun current _ => by
          apply Finset.sum_nonneg
          intro candidate _
          split_ifs with positive
          · exact (one_div_pos.mpr positive).le
          · exact le_rfl)
        (Finset.mem_univ index)
    have reciprocal_lt_denominator :
        1 / probability index letter < (denominator : ℝ) :=
      lt_of_le_of_lt (letter_le_inner.trans inner_le_cost)
        (lt_of_le_of_lt
          (le_add_of_nonneg_left ratio_positive.le)
          denominator_large)
    have mass_exceeds_one :
        (1 : ℝ) ≤ probability index letter * (denominator : ℝ) := by
      have crossed :=
        (div_lt_iff₀ genuinely_positive).mp
          reciprocal_lt_denominator
      nlinarith
    have positive_floor :
        0 < distributionFloorNumerator
          denominator (probability index) letter := by
      unfold distributionFloorNumerator
      exact Nat.floor_pos.mpr mass_exceeds_one
    change
      0 < distributionFloorNumerator denominator
        (probability index) letter +
          if letter = base then
            distributionFloorResidual denominator (probability index)
          else 0
    exact lt_of_lt_of_le positive_floor
      (Nat.le_add_right _ _)

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactLocallySampleableLaw_absolute_continuous_roundedJA
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (history : ExactLocallySampleableTuple X Y A B D) :
    exactLocallySampleableJARounded
      G n D denominator numerator history = 0 →
        exactLocallySampleableLaw G n S D history = 0 := by
  classical
  intro rounded_zero
  apply exactLocallySampleableLaw_absolute_continuous_JA
    G n S D remaining positive base history
  rcases history with ⟨coordinate, x, y, flag⟩
  have card_nonzero :
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (exactRemainingCoordinate_card_pos D remaining))
  have denominator_nonzero : (denominator : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt denominator_positive)
  change
    G.questionWeight x y *
      ((numerator (.inl (coordinate, x)) flag : ℝ) /
        denominator) /
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) = 0
    at rounded_zero
  have product_zero :
      G.questionWeight x y *
        ((numerator (.inl (coordinate, x)) flag : ℝ) /
          denominator) = 0 :=
    (div_eq_zero_iff.mp rounded_zero).resolve_right card_nonzero
  rcases mul_eq_zero.mp product_zero with question_zero | numerator_zero
  · change
      G.questionWeight x y *
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D)
          coordinate x flag /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ) = 0
    simp [question_zero]
  · have cast_zero :
        (numerator (.inl (coordinate, x)) flag : ℝ) = 0 :=
      (div_eq_zero_iff.mp numerator_zero).resolve_right
        denominator_nonzero
    have natural_zero : numerator (.inl (coordinate, x)) flag = 0 := by
      exact_mod_cast cast_zero
    have conditional_nonnegative :
        0 ≤ exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D)
          coordinate x flag :=
      exactAliceLocalConditional_nonneg D base
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableLaw_nonneg G n S D positive)
        coordinate x flag
    have conditional_zero :
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D)
          coordinate x flag = 0 := by
      by_contra nonzero
      have strictly_positive :=
        lt_of_le_of_ne conditional_nonnegative (Ne.symm nonzero)
      have retained := preserves (.inl (coordinate, x)) flag
        strictly_positive
      omega
    change
      G.questionWeight x y *
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D)
          coordinate x flag /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ) = 0
    simp [conditional_zero]

theorem exact_exists_support_preserving_local_shared_permutation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    {gamma : ℝ} (gamma_positive : 0 < gamma) :
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
          (∀ index history,
            uniformPermutationProbability
              (fun permutation : Equiv.Perm
                (ExactHistoryFlag X Y A B D × Fin denominator) =>
                rationalPermutationOutput denominator (numerator index)
                  (nonempty index) permutation = history) =
                (numerator index history : ℝ) / denominator) ∧
          (∀ left right,
            uniformPermutationProbability
              (fun permutation : Equiv.Perm
                (ExactHistoryFlag X Y A B D × Fin denominator) =>
                rationalPermutationOutput denominator (numerator left)
                  (nonempty left) permutation ≠
                rationalPermutationOutput denominator (numerator right)
                  (nonempty right) permutation) ≤
              2 * finiteTotalVariation
                (fun history =>
                  (numerator left history : ℝ) / denominator)
                (fun history =>
                  (numerator right history : ℝ) / denominator)) := by
  obtain ⟨denominator, denominator_positive, numerator,
      normalized, approximation, preserves⟩ :=
    existsCommonSupportPreservingRationalApproximations
      base
      (exactLocalConditionalFamily D base
        (exactLocallySampleableLaw G n S D))
      (exactLocalConditionalFamily_nonneg D base
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableLaw_nonneg G n S D positive))
      (exactLocalConditionalFamily_sum D base
        (exactLocallySampleableLaw G n S D))
      gamma_positive
  refine ⟨denominator, denominator_positive, numerator,
    normalized, approximation, preserves,
    fun index => rationalMarked_nonempty denominator
      (numerator index) (normalized index) denominator_positive,
    ?_, ?_⟩
  · intro index history
    exact rationalPermutationOutput_probability
      denominator (numerator index) (normalized index) _ history
  · intro left right
    exact rationalPermutationOutput_disagreement_le_two_mul_finiteTotalVariation
      denominator denominator_positive
      (numerator left) (numerator right)
      (normalized left) (normalized right) _ _

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

def exactSourceAliceRefinedPOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) :
    POVM A (ExactAliceLocalIndex G n S D r) := by
  classical
  exact purificationAlicePOVM
    (exactAliceRefinedPOVM G n S D r a₀ x)

def exactSourceBobRefinedPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) :
    POVM B (ExactBobLocalIndex G n S D r) :=
  exactBobRefinedPOVM G n S D r b₀ y

def exactSourceJointEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) (a : A) (b : B) :
    Matrix
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) ℂ :=
  (exactSourceAliceRefinedPOVM G n S D r a₀ x).effect a ⊗ₖ
    (exactSourceBobRefinedPOVM G n S D r b₀ y).effect b

def exactSourceWinningEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    Matrix
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true
    then exactSourceJointEffect G n S D r a₀ b₀ x y a b
    else 0

def exactSourceWinningEffectCLM
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    EuclideanSpace ℂ
        (ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r) →L[ℂ]
      EuclideanSpace ℂ
        (ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r) := by
  classical
  exact Matrix.toEuclideanCLM
    (n := ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) (𝕜 := ℂ)
    (exactSourceWinningEffect G n S D r a₀ b₀ x y)

theorem exactSourceJointEffect_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) (a : A) (b : B) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r) (𝕜 := ℂ)
        (exactSourceJointEffect G n S D r a₀ b₀ x y a b))
      (exactUnnormalizedPsi G n S D r x y) =
      bornTracePairing S.state.matrix
        (exactAliceCoordinateFilter
          G n S D r.seed r.history r.aliceAnswer x a)
        (exactBobCoordinateFilter
          G n S D r.seed r.history r.bobAnswer y b) := by
  classical
  simpa [exactSourceJointEffect,
    exactSourceAliceRefinedPOVM,
    exactSourceBobRefinedPOVM, purificationAlicePOVM] using
    (exactRefinedPOVM_quadratic
      G n S D r a₀ b₀ x y a b)

theorem exactSourceWinningEffect_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    quadraticExpectation
      (exactSourceWinningEffectCLM
        G n S D r a₀ b₀ x y)
      (exactUnnormalizedPsi G n S D r x y) =
      ∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          bornTracePairing S.state.matrix
            (exactAliceCoordinateFilter
              G n S D r.seed r.history r.aliceAnswer x a)
            (exactBobCoordinateFilter
              G n S D r.seed r.history r.bobAnswer y b)
        else 0 := by
  classical
  unfold exactSourceWinningEffectCLM
    exactSourceWinningEffect
  rw [sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact exactSourceJointEffect_quadratic
      G n S D r a₀ b₀ x y a b
  · simp [quadraticExpectation]

theorem exactSourceWinningEffect_quadratic_eq_conditional
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D r.seed r.history x y ≠ 0) :
    quadraticExpectation
      (exactSourceWinningEffectCLM
        G n S D r a₀ b₀ x y)
      (exactUnnormalizedPsi G n S D r x y) =
      exactJointConditionalWinningMass
        G n S D r.seed r.history r.aliceAnswer r.bobAnswer x y := by
  rw [exactSourceWinningEffect_quadratic]
  unfold exactJointConditionalWinningMass
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · rw [exactAliceCoordinateFilter_eq_joint
      G n S D r.seed r.history r.aliceAnswer x y a supported,
      exactBobCoordinateFilter_eq_joint
        G n S D r.seed r.history r.bobAnswer x y b supported]
  · rfl

theorem exactSourceNormalizedWinningEffect_eq_conditional
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D r.seed r.history x y ≠ 0) :
    quadraticExpectation
      (exactSourceWinningEffectCLM
        G n S D r a₀ b₀ x y)
      (normalizedPureVector
        (exactUnnormalizedPsi G n S D r x y)) =
      exactJointConditionalWinningMass
        G n S D r.seed r.history r.aliceAnswer r.bobAnswer x y /
        bornTracePairing S.state.matrix
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x)
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y) := by
  rw [quadraticExpectation_normalizedPureVector,
    exactSourceWinningEffect_quadratic_eq_conditional
      G n S D r a₀ b₀ x y supported,
    exactUnnormalizedPsi_norm_sq]

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactSourceAcceptedCoordinateMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  ∑ q : ExactJointOutcome X Y A B D,
    if exactLocallySampleableCode D q = t ∧
      repeatedCoordinateWin G n q.1.coordinate.val q.2 = true then
      exactPostselectedJointLaw G n S D q
    else 0

theorem exactSourceAcceptedCoordinateMass_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    0 ≤ exactSourceAcceptedCoordinateMass G n S D t := by
  unfold exactSourceAcceptedCoordinateMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPostselectedJointLaw_nonneg
      G n S D positive q
  · exact le_rfl

theorem exactSourceAcceptedCoordinateMass_le_law
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    exactSourceAcceptedCoordinateMass G n S D t ≤
      exactLocallySampleableLaw G n S D t := by
  classical
  unfold exactSourceAcceptedCoordinateMass
    exactLocallySampleableLaw exactSourcePushforward
    groupedMass
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro q _
  by_cases history : exactLocallySampleableCode D q = t
  · by_cases winning :
      repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
    · simp [history, winning]
    · simp [history, winning,
        exactPostselectedJointLaw_nonneg
          G n S D positive q]
  · simp [history]

def exactSourceConditionalWinningProbability
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  exactSourceAcceptedCoordinateMass G n S D t /
    exactLocallySampleableLaw G n S D t

theorem exactSourceConditionalWinningProbability_bounds
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    0 ≤ exactSourceConditionalWinningProbability
      G n S D t ∧
    exactSourceConditionalWinningProbability
      G n S D t ≤ 1 := by
  have mass_nonnegative :=
    exactSourceAcceptedCoordinateMass_nonneg
      G n S D positive t
  have mass_le := exactSourceAcceptedCoordinateMass_le_law
    G n S D positive t
  have law_nonnegative := exactLocallySampleableLaw_nonneg
    G n S D positive t
  unfold exactSourceConditionalWinningProbability
  constructor
  · exact div_nonneg mass_nonnegative law_nonnegative
  · by_cases zero : exactLocallySampleableLaw G n S D t = 0
    · simp [zero]
    · exact (div_le_one
        (lt_of_le_of_ne law_nonnegative (Ne.symm zero))).mpr mass_le

theorem exactSourceConditionalWinningProbability_mul_law
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    exactLocallySampleableLaw G n S D t *
        exactSourceConditionalWinningProbability G n S D t =
      exactSourceAcceptedCoordinateMass G n S D t := by
  by_cases zero : exactLocallySampleableLaw G n S D t = 0
  · have nonnegative := exactSourceAcceptedCoordinateMass_nonneg
      G n S D positive t
    have bounded := exactSourceAcceptedCoordinateMass_le_law
      G n S D positive t
    rw [zero] at bounded
    have accepted_zero :
        exactSourceAcceptedCoordinateMass G n S D t = 0 := by
      linarith
    simp [zero, accepted_zero]
  · unfold exactSourceConditionalWinningProbability
    field_simp [zero]

theorem exactSourceAcceptedCoordinateMass_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactSourceAcceptedCoordinateMass G n S D t) =
      ∑ q : ExactJointOutcome X Y A B D,
        if repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
        then exactPostselectedJointLaw G n S D q
        else 0 := by
  classical
  unfold exactSourceAcceptedCoordinateMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases winning :
      repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
  · simp [winning]
  · simp [winning]

theorem exactSourceConditionalWinningProbability_expectation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t *
        exactSourceConditionalWinningProbability G n S D t) =
      ∑ q : ExactJointOutcome X Y A B D,
        if repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
        then exactPostselectedJointLaw G n S D q
        else 0 := by
  simp_rw [exactSourceConditionalWinningProbability_mul_law
    G n S D positive]
  exact exactSourceAcceptedCoordinateMass_sum G n S D

theorem exactRepeatedConditionedCoordinateWin
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : Fin n) :
    (∑ outcome : ExactOutcome X Y A B n,
      if repeatedCoordinateWin G n i outcome = true then
        repeatedConditionedOutcomeLaw G n S D outcome
      else 0) =
    (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) (insert i D)) /
        repeatedPostselectionMass G n S D := by
  classical
  have accepted_as_indicator :
      (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) (insert i D)) =
        ∑ outcome : ExactOutcome X Y A B n,
          if outcome ∈ FiniteEventLaw.winEvent
              (repeatedCoordinateWin G n) (insert i D) then
            (strategyEventLaw (G.repeat n) S).weight outcome
          else 0 := by
    simp [FiniteEventLaw.eventMass]
  rw [accepted_as_indicator]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases winning : repeatedCoordinateWin G n i outcome = true
  · simp [repeatedConditionedOutcomeLaw,
      conditionedEventDistribution,
      repeatedPostselectionMass, postselectionMass,
      FiniteEventLaw.winEvent, winning, ite_div]
  · simp [FiniteEventLaw.winEvent, winning]

theorem exactSourceAcceptedCoordinateMass_sum_eq_remaining_average
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactSourceAcceptedCoordinateMass G n S D t) =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        (∑ i : SourceRemainingCoordinate D,
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent
              (repeatedCoordinateWin G n) (insert i.val D)) /
            repeatedPostselectionMass G n S D) := by
  classical
  rw [exactSourceAcceptedCoordinateMass_sum]
  unfold exactPostselectedJointLaw
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ outcome : ExactOutcome X Y A B n,
      ∑ seed : ExactRemainingSeed D,
        if repeatedCoordinateWin G n seed.coordinate.val outcome = true
        then exactSeedWeight seed *
          repeatedConditionedOutcomeLaw G n S D outcome
        else 0) =
      ∑ outcome : ExactOutcome X Y A B n,
        ∑ seed : ExactRemainingSeed D,
          exactSeedWeight seed *
            (if repeatedCoordinateWin G n seed.coordinate.val outcome = true
             then repeatedConditionedOutcomeLaw G n S D outcome
             else 0) := by
          apply Finset.sum_congr rfl
          intro outcome _
          apply Finset.sum_congr rfl
          intro seed _
          split <;> simp
    _ = ∑ outcome : ExactOutcome X Y A B n,
        ∑ i : SourceRemainingCoordinate D,
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            (if repeatedCoordinateWin G n i.val outcome = true
             then repeatedConditionedOutcomeLaw G n S D outcome
             else 0) := by
          apply Finset.sum_congr rfl
          intro outcome _
          exact exactSeedWeight_coordinate_sum
            (M := SourceRemainingCoordinate D)
            (fun i =>
              if repeatedCoordinateWin G n i.val outcome = true
              then repeatedConditionedOutcomeLaw G n S D outcome
              else 0)
    _ = (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        (∑ i : SourceRemainingCoordinate D,
          ∑ outcome : ExactOutcome X Y A B n,
            if repeatedCoordinateWin G n i.val outcome = true
            then repeatedConditionedOutcomeLaw G n S D outcome
            else 0) := by
          rw [Finset.sum_comm, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact exactRepeatedConditionedCoordinateWin
        G n S D i.val

theorem exactSourceConditionalWinningProbability_eq_accepted_average
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t *
        exactSourceConditionalWinningProbability G n S D t) =
      sourceHistoryAcceptedMass G n S D /
        repeatedPostselectionMass G n S D := by
  rw [exactSourceConditionalWinningProbability_expectation
    G n S D positive,
    ← exactSourceAcceptedCoordinateMass_sum,
    exactSourceAcceptedCoordinateMass_sum_eq_remaining_average,
    sourceHistoryAcceptedMass_eq_remaining_average]
  have cardinality :
      Fintype.card (SourceRemainingCoordinate D) =
        (Finset.univ \ D).card := by
    simpa only [Fintype.card_fin] using Fintype.card_congr
      (Finset.equivFin (Finset.univ \ D))
  push_cast [cardinality]
  rw [← Finset.sum_div]
  ring

theorem exactSource_failure_sum_lt_of_uniform
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    {δ : ℝ}
    (failure : uniformRemainingFailure
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) D < δ) :
    (∑ i ∈ Finset.univ \ D,
      FiniteEventLaw.failureMass
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D i) <
      ((Finset.univ \ D).card : ℝ) *
        (δ * repeatedPostselectionMass G n S D) := by
  have cardinality : 0 < ((Finset.univ \ D).card : ℝ) := by
    exact_mod_cast remaining
  unfold uniformRemainingFailure conditionalCoordinateFailure at failure
  change
    (∑ i ∈ Finset.univ \ D,
      FiniteEventLaw.failureMass
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D i /
        repeatedPostselectionMass G n S D) /
      ((Finset.univ \ D).card : ℝ) < δ at failure
  rw [← Finset.sum_div] at failure
  have first := (div_lt_iff₀ cardinality).mp failure
  have second := (div_lt_iff₀ positive).mp first
  nlinarith

theorem exactSourceConditionalWinningProbability_gt_of_uniform_failure
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    {δ : ℝ}
    (failure : uniformRemainingFailure
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) D < δ) :
    1 - δ <
      ∑ t : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D t *
          exactSourceConditionalWinningProbability G n S D t := by
  rw [exactSourceConditionalWinningProbability_eq_accepted_average
    G n S D positive]
  have numerator := exactSource_failure_sum_lt_of_uniform
    G n S D remaining positive failure
  have accepted := sourceHistoryAcceptedMass_gt_of_greedy
    G n S D remaining numerator
  apply (lt_div_iff₀ positive).mpr
  exact accepted

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B dA dB : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]

def exactSourceAliceFlagCoupling
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty) :
    ExactSourceSharedFlag X Y A B D denominator × (X × Y) → ℝ :=
  exactFiniteFiberLift
    (exactSourceAliceSampleTuple
      D denominator numerator nonempty)
    (flaggedQuestionWeight G
      (exactSourceSharedFlagWeight D denominator))
    (exactLocallySampleableLaw G n S D)

theorem exactSourceAliceFlagCoupling_supported
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (history : ExactLocallySampleableTuple X Y A B D) :
    groupedMass
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty)
        (flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator)) history = 0 →
      exactLocallySampleableLaw G n S D history = 0 := by
  rw [exactSourceAliceSampleTuple_groupedMass
    G n D denominator numerator normalized nonempty]
  exact exactLocallySampleableLaw_absolute_continuous_roundedJA
    G n S D remaining positive base denominator denominator_positive
    numerator preserves history

theorem exactSourceAliceFlagCoupling_expectation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (value : ExactLocallySampleableTuple X Y A B D → ℝ) :
    (∑ outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      exactSourceAliceFlagCoupling
        G n S D denominator numerator nonempty outcome *
        value (exactSourceAliceSampleTuple
          D denominator numerator nonempty outcome)) =
      ∑ history : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D history *
          value history := by
  exact exactFiniteFiberLift_expectation
    (exactSourceAliceSampleTuple
      D denominator numerator nonempty)
    (flaggedQuestionWeight G
      (exactSourceSharedFlagWeight D denominator))
    (exactLocallySampleableLaw G n S D)
    (exactSourceAliceFlagCoupling_supported
      G n S D remaining positive base denominator denominator_positive
      numerator normalized preserves nonempty)
    value

theorem exactSourceAliceFlagCoupling_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty) :
    (∑ outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      exactSourceAliceFlagCoupling
        G n S D denominator numerator nonempty outcome) = 1 := by
  have expectation := exactSourceAliceFlagCoupling_expectation
    G n S D remaining positive base denominator denominator_positive
    numerator normalized preserves nonempty (fun _ => (1 : ℝ))
  simpa [exactLocallySampleableLaw_sum
    G n S D remaining positive] using expectation

theorem exactSourceAliceFlagCoupling_totalVariation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty) :
    finiteTotalVariation
      (flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator))
      (exactSourceAliceFlagCoupling
        G n S D denominator numerator nonempty) =
      finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableLaw G n S D) := by
  change
    finiteTotalVariation
      (flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator))
      (exactFiniteFiberLift
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty)
        (flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator))
        (exactLocallySampleableLaw G n S D)) = _
  rw [exactFiniteFiberLift_totalVariation
    (exactSourceAliceSampleTuple
      D denominator numerator nonempty)
    (flaggedQuestionWeight G
      (exactSourceSharedFlagWeight D denominator))
    (exactLocallySampleableLaw G n S D)
    (flaggedQuestionWeight_nonneg G
      (exactSourceSharedFlagWeight D denominator)
      (exactSourceSharedFlagWeight_nonneg D denominator))
    (exactSourceAliceFlagCoupling_supported
      G n S D remaining positive base denominator denominator_positive
      numerator normalized preserves nonempty)]
  congr 1
  funext history
  exact exactSourceAliceSampleTuple_groupedMass
    G n D denominator numerator normalized nonempty history

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactFairWinningOutcomeBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ outcome : ExactOutcome X Y A B n,
    if exactLocallySampleableCode D (history.seed, outcome) =
        (history.seed.coordinate, x, y, history) ∧
      repeatedCoordinateWin G n history.seed.coordinate.val outcome = true
    then (strategyEventLaw (G.repeat n) S).weight outcome
    else 0

theorem exactSourceAcceptedCoordinateMass_eq_seeded_fair_born
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactSourceAcceptedCoordinateMass G n S D
        (history.seed.coordinate, x, y, history) =
      if exactHistoryAccepted G n D history then
        (exactSeedWeight history.seed *
          exactFairWinningOutcomeBornMass
            G n S D history x y) /
          repeatedPostselectionMass G n S D
      else 0 := by
  classical
  by_cases accepted : exactHistoryAccepted G n D history
  · rw [if_pos accepted]
    unfold exactSourceAcceptedCoordinateMass
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single history.seed]
    · unfold exactFairWinningOutcomeBornMass
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro outcome _
      by_cases code :
          exactLocallySampleableCode D
            (history.seed, outcome) =
              (history.seed.coordinate, x, y, history)
      · by_cases winning :
          repeatedCoordinateWin G n history.seed.coordinate.val
            outcome = true
        · have same_history :
              exactHistoryCode D (history.seed, outcome) =
                history :=
            congrArg
              (fun t : ExactLocallySampleableTuple
                X Y A B D => t.2.2.2) code
          have conditioned :
              outcome ∈ FiniteEventLaw.winEvent
                (repeatedCoordinateWin G n) D := by
            apply (exactHistoryCode_accepted_iff
              G n D (history.seed, outcome)).mp
            rw [same_history]
            exact accepted
          simp [code, winning, exactPostselectedJointLaw,
            repeatedConditionedOutcomeLaw,
            conditionedEventDistribution,
            repeatedPostselectionMass, postselectionMass, conditioned]
          ring
        · simp [code, winning]
      · simp [code]
    · intro seed _ distinct
      apply Finset.sum_eq_zero
      intro outcome _
      have not_code :
          exactLocallySampleableCode D (seed, outcome) ≠
            (history.seed.coordinate, x, y, history) := by
        intro code
        have same := congrArg
          (fun t : ExactLocallySampleableTuple X Y A B D =>
            t.2.2.2.seed) code
        exact distinct same
      simp [not_code]
    · simp
  · rw [if_neg accepted]
    have law_zero :=
      exactLocallySampleableLaw_zero_of_not_accepted
        G n S D history.seed.coordinate x y history accepted
    exact le_antisymm
      (by
        simpa [law_zero] using
          exactSourceAcceptedCoordinateMass_le_law
            G n S D positive
            (history.seed.coordinate, x, y, history))
      (exactSourceAcceptedCoordinateMass_nonneg
        G n S D positive
        (history.seed.coordinate, x, y, history))

theorem exactSourceConditionalWinningProbability_eq_fine_born_ratio
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (history : ExactHistoryFlag X Y A B D)
    (accepted : exactHistoryAccepted G n D history)
    (x : X) (y : Y) :
    exactSourceConditionalWinningProbability G n S D
        (history.seed.coordinate, x, y, history) =
      exactFairWinningOutcomeBornMass G n S D history x y /
        exactFairFullOutcomeBornMass G n S D history x y := by
  have seed_positive : 0 < exactSeedWeight history.seed := by
    unfold exactSeedWeight
    have coordinate_positive :
        0 < Fintype.card (SourceRemainingCoordinate D) :=
      Fintype.card_pos_iff.mpr ⟨history.seed.coordinate⟩
    positivity
  have posterior :
      exactLocallySampleableLaw G n S D
        (history.seed.coordinate, x, y, history) =
        (exactSeedWeight history.seed *
          exactFairFullOutcomeBornMass
            G n S D history x y) /
          repeatedPostselectionMass G n S D := by
    rw [exactLocallySampleableLaw_eq_fair_born,
      if_pos accepted,
      exactFairFullOutcomeBornMass_eq_reveal_question_norm]
    ring
  unfold exactSourceConditionalWinningProbability
  rw [exactSourceAcceptedCoordinateMass_eq_seeded_fair_born
    G n S D positive history x y, if_pos accepted, posterior]
  by_cases mass_zero :
      exactFairFullOutcomeBornMass G n S D history x y = 0
  · simp [mass_zero]
  · field_simp [positive.ne', seed_positive.ne', mass_zero]

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactFineCoordinateWinningBorn_collapse
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (xs : Fin n → X) (ys : Fin n → Y)
    (coordinate : Fin n) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B,
      if G.predicate x y a b = true then
        bornTracePairing S.state.matrix
          (conditionedAliceCoordinateEffect
            G n S D aliceAnswer xs coordinate a)
          (conditionedBobCoordinateEffect
            G n S D bobAnswer ys coordinate b)
      else 0) =
    ∑ aa : Fin n → A, ∑ bb : Fin n → B,
      if
        (∀ (j : Fin n) (member : j ∈ D),
          aa j = aliceAnswer ⟨j, member⟩) ∧
        (∀ (j : Fin n) (member : j ∈ D),
          bb j = bobAnswer ⟨j, member⟩) ∧
        G.predicate x y (aa coordinate) (bb coordinate) = true
      then S.outcomeProbability xs ys aa bb
      else 0 := by
  classical
  simp_rw [conditionedCoordinateEffects_born_expansion G n S D]
  let f : A → B → (Fin n → A) → (Fin n → B) → ℝ :=
    fun a b aa bb =>
      if G.predicate x y a b = true then
        if
          (∀ (j : Fin n) (member : j ∈ D),
            aa j = aliceAnswer ⟨j, member⟩) ∧ aa coordinate = a
        then
          if
            (∀ (j : Fin n) (member : j ∈ D),
              bb j = bobAnswer ⟨j, member⟩) ∧ bb coordinate = b
          then S.outcomeProbability xs ys aa bb
          else 0
        else 0
      else 0
  calc
    (∑ a : A, ∑ b : B,
      if G.predicate x y a b = true then
        ∑ aa : Fin n → A, ∑ bb : Fin n → B,
          if
            (∀ (j : Fin n) (member : j ∈ D),
              aa j = aliceAnswer ⟨j, member⟩) ∧ aa coordinate = a
          then
            if
              (∀ (j : Fin n) (member : j ∈ D),
                bb j = bobAnswer ⟨j, member⟩) ∧ bb coordinate = b
            then S.outcomeProbability xs ys aa bb
            else 0
          else 0
      else 0) =
      ∑ a : A, ∑ b : B,
        ∑ aa : Fin n → A, ∑ bb : Fin n → B, f a b aa bb := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          by_cases wins : G.predicate x y a b = true
          · simp [f, wins]
          · simp [f, wins]
    _ = ∑ aa : Fin n → A, ∑ bb : Fin n → B,
      ∑ a : A, ∑ b : B, f a b aa bb :=
        finite_sum_four_swap f
    _ = ∑ aa : Fin n → A, ∑ bb : Fin n → B,
      if
        (∀ (j : Fin n) (member : j ∈ D),
          aa j = aliceAnswer ⟨j, member⟩) ∧
        (∀ (j : Fin n) (member : j ∈ D),
          bb j = bobAnswer ⟨j, member⟩) ∧
        G.predicate x y (aa coordinate) (bb coordinate) = true
      then S.outcomeProbability xs ys aa bb
      else 0 := by
        apply Finset.sum_congr rfl
        intro aa _
        apply Finset.sum_congr rfl
        intro bb _
        by_cases alice_matches :
          ∀ (j : Fin n) (member : j ∈ D),
            aa j = aliceAnswer ⟨j, member⟩
        · by_cases bob_matches :
            ∀ (j : Fin n) (member : j ∈ D),
              bb j = bobAnswer ⟨j, member⟩
          · rw [Finset.sum_eq_single (aa coordinate)]
            · rw [Finset.sum_eq_single (bb coordinate)]
              · dsimp only [f]
                by_cases wins :
                  G.predicate x y (aa coordinate) (bb coordinate) = true
                · rw [if_pos wins,
                    if_pos ⟨alice_matches, rfl⟩,
                    if_pos ⟨bob_matches, rfl⟩,
                    if_pos ⟨alice_matches, bob_matches, wins⟩]
                · rw [if_neg wins,
                    if_neg (fun h => wins h.2.2)]
              · intro b _ different
                simp [f, Ne.symm different]
              · simp
            · intro a _ different
              simp [f, Ne.symm different]
            · simp
          · simp [f, bob_matches]
        · simp [f, alice_matches]

def exactFairCoordinateRefinedWinningBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
    exactFiberQuestionWeight
        G n D history.seed history.history x y xs ys *
      (∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          bornTracePairing S.state.matrix
            (conditionedAliceCoordinateEffect G n S D
              history.aliceAnswer xs history.seed.coordinate.val a)
            (conditionedBobCoordinateEffect G n S D
              history.bobAnswer ys history.seed.coordinate.val b)
        else 0)

theorem exactFairWinningOutcomeBornMass_eq_refined
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactFairWinningOutcomeBornMass
      G n S D history x y =
        exactFairCoordinateRefinedWinningBornMass
          G n S D history x y := by
  classical
  unfold exactFairWinningOutcomeBornMass
    exactFairCoordinateRefinedWinningBornMass
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  have compatibility :
      (exactAliceQuestionCompatible
        D history.seed history.history x xs ∧
       exactBobQuestionCompatible
        D history.seed history.history y ys) ↔
      exactRevealCode D history.seed (xs, ys) = history.history ∧
        xs history.seed.coordinate.val = x ∧
        ys history.seed.coordinate.val = y :=
    (exactRevealCode_compatible_iff
      D history.seed history.history x y xs ys).symm
  by_cases compatible :
      exactAliceQuestionCompatible
        D history.seed history.history x xs ∧
      exactBobQuestionCompatible
        D history.seed history.history y ys
  · have actual := compatibility.mp compatible
    rw [exactFiberQuestionWeight, if_pos compatible,
      exactFineCoordinateWinningBorn_collapse
        G n S D history.aliceAnswer history.bobAnswer xs ys
        history.seed.coordinate.val x y]
    calc
      (∑ aa : Fin n → A, ∑ bb : Fin n → B,
        if exactLocallySampleableCode D
            (history.seed, (xs, ys, aa, bb)) =
            (history.seed.coordinate, x, y, history) ∧
          repeatedCoordinateWin G n history.seed.coordinate.val
            (xs, ys, aa, bb) = true
        then (strategyEventLaw (G.repeat n) S).weight
          (xs, ys, aa, bb)
        else 0) =
        ∑ aa : Fin n → A, ∑ bb : Fin n → B,
          (G.repeat n).questionWeight xs ys *
            if
              (∀ (j : Fin n) (member : j ∈ D),
                aa j = history.aliceAnswer ⟨j, member⟩) ∧
              (∀ (j : Fin n) (member : j ∈ D),
                bb j = history.bobAnswer ⟨j, member⟩) ∧
              G.predicate x y
                (aa history.seed.coordinate.val)
                (bb history.seed.coordinate.val) = true
            then S.outcomeProbability xs ys aa bb
            else 0 := by
          apply Finset.sum_congr rfl
          intro aa _
          apply Finset.sum_congr rfl
          intro bb _
          have fiber :=
            exactLocallySampleableCode_fixedSeed_fiber_iff
              D history x y (xs, ys, aa, bb)
          have event :
              (exactLocallySampleableCode D
                  (history.seed, (xs, ys, aa, bb)) =
                    (history.seed.coordinate, x, y, history) ∧
                repeatedCoordinateWin G n history.seed.coordinate.val
                  (xs, ys, aa, bb) = true) ↔
              ((∀ (j : Fin n) (member : j ∈ D),
                aa j = history.aliceAnswer ⟨j, member⟩) ∧
               (∀ (j : Fin n) (member : j ∈ D),
                bb j = history.bobAnswer ⟨j, member⟩) ∧
               G.predicate x y
                (aa history.seed.coordinate.val)
                (bb history.seed.coordinate.val) = true) := by
            rw [fiber]
            simp [actual.1, actual.2.1, actual.2.2,
              repeatedCoordinateWin, and_assoc]
          by_cases wins :
              (∀ (j : Fin n) (member : j ∈ D),
                aa j = history.aliceAnswer ⟨j, member⟩) ∧
              (∀ (j : Fin n) (member : j ∈ D),
                bb j = history.bobAnswer ⟨j, member⟩) ∧
              G.predicate x y
                (aa history.seed.coordinate.val)
                (bb history.seed.coordinate.val) = true
          · have selected := event.mpr wins
            rw [if_pos selected, if_pos wins]
            rfl
          · have rejected :
              ¬ (exactLocallySampleableCode D
                    (history.seed, (xs, ys, aa, bb)) =
                  (history.seed.coordinate, x, y, history) ∧
                repeatedCoordinateWin G n history.seed.coordinate.val
                  (xs, ys, aa, bb) = true) := by
              intro selected
              exact wins (event.mp selected)
            rw [if_neg rejected, if_neg wins]
            simp
      _ = (G.repeat n).questionWeight xs ys *
        (∑ aa : Fin n → A, ∑ bb : Fin n → B,
          if
            (∀ (j : Fin n) (member : j ∈ D),
              aa j = history.aliceAnswer ⟨j, member⟩) ∧
            (∀ (j : Fin n) (member : j ∈ D),
              bb j = history.bobAnswer ⟨j, member⟩) ∧
            G.predicate x y
              (aa history.seed.coordinate.val)
              (bb history.seed.coordinate.val) = true
          then S.outcomeProbability xs ys aa bb
          else 0) := by
          simp only [Finset.mul_sum]
  · rw [exactFiberQuestionWeight, if_neg compatible,
      zero_mul]
    apply Finset.sum_eq_zero
    intro aa _
    apply Finset.sum_eq_zero
    intro bb _
    have no_code :
        exactLocallySampleableCode D
          (history.seed, (xs, ys, aa, bb)) ≠
            (history.seed.coordinate, x, y, history) := by
      intro code
      have conditions :=
        (exactLocallySampleableCode_fixedSeed_fiber_iff
          D history x y (xs, ys, aa, bb)).mp code
      exact compatible
        (compatibility.mpr
          ⟨conditions.1, conditions.2.1, conditions.2.2.1⟩)
    simp [no_code]

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactFairWinningOutcomeBornMass_eq_fiber_conditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D history.seed history.history x y ≠ 0) :
    exactFairWinningOutcomeBornMass G n S D history x y =
      exactFiberQuestionMass
          G n D history.seed history.history x y *
        exactJointConditionalWinningMass
          G n S D history.seed history.history
          history.aliceAnswer history.bobAnswer x y := by
  classical
  rw [exactFairWinningOutcomeBornMass_eq_refined,
    exactJointConditionalWinningMass_born
      G n S D history.seed history.history
      history.aliceAnswer history.bobAnswer x y supported]
  unfold exactFairCoordinateRefinedWinningBornMass
  let summand : (Fin n → X) → (Fin n → Y) → A → B → ℝ :=
    fun xs ys a b =>
      if G.predicate x y a b = true then
        exactFiberQuestionWeight
            G n D history.seed history.history x y xs ys *
          bornTracePairing S.state.matrix
            (conditionedAliceCoordinateEffect
              G n S D history.aliceAnswer xs
              history.seed.coordinate.val a)
            (conditionedBobCoordinateEffect
              G n S D history.bobAnswer ys
              history.seed.coordinate.val b)
      else 0
  calc
    (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      exactFiberQuestionWeight
          G n D history.seed history.history x y xs ys *
        (∑ a : A, ∑ b : B,
          if G.predicate x y a b = true then
            bornTracePairing S.state.matrix
              (conditionedAliceCoordinateEffect
                G n S D history.aliceAnswer xs
                history.seed.coordinate.val a)
              (conditionedBobCoordinateEffect
                G n S D history.bobAnswer ys
                history.seed.coordinate.val b)
          else 0)) =
        ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
          ∑ a : A, ∑ b : B, summand xs ys a b := by
            simp only [summand, Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ a : A, ∑ b : B,
          ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
            summand xs ys a b :=
      finite_sum_four_swap summand
    _ = exactFiberQuestionMass
          G n D history.seed history.history x y *
        (∑ a : A, ∑ b : B,
          if G.predicate x y a b = true then
            ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
              exactConditionalQuestionWeight
                  G n D history.seed history.history x y xs ys *
                bornTracePairing S.state.matrix
                  (conditionedAliceCoordinateEffect
                    G n S D history.aliceAnswer xs
                    history.seed.coordinate.val a)
                  (conditionedBobCoordinateEffect
                    G n S D history.bobAnswer ys
                    history.seed.coordinate.val b)
          else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            by_cases wins : G.predicate x y a b = true
            · simp only [if_pos wins]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro xs _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ys _
              dsimp only [summand]
              rw [if_pos wins]
              unfold exactConditionalQuestionWeight
              field_simp [supported]
            · simp [summand, wins]

theorem exactSourceConditionalWinningProbability_eq_normalized_verifier
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (history : ExactHistoryFlag X Y A B D)
    (accepted : exactHistoryAccepted G n D history)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D history.seed history.history x y ≠ 0) :
    exactSourceConditionalWinningProbability G n S D
        (history.seed.coordinate, x, y, history) =
      quadraticExpectation
        (exactSourceWinningEffectCLM
          G n S D history a₀ b₀ x y)
        (normalizedPureVector
          (exactUnnormalizedPsi G n S D history x y)) := by
  rw [exactSourceConditionalWinningProbability_eq_fine_born_ratio
    G n S D positive history accepted x y,
    exactFairWinningOutcomeBornMass_eq_fiber_conditional
      G n S D history x y supported,
    exactFairFullOutcomeBornMass_eq_conditioned,
    exactFairConditionedAnswerBornMass_eq_fiber_norm,
    exactSourceNormalizedWinningEffect_eq_conditional
      G n S D history a₀ b₀ x y supported,
    exactUnnormalizedPsi_norm_sq]
  exact mul_div_mul_left _ _ supported

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactLocallySampleableLaw_coordinate_eq_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    t.1 = t.2.2.2.seed.coordinate := by
  classical
  by_contra different
  apply supported
  unfold exactLocallySampleableLaw
    exactSourcePushforward groupedMass
  apply Finset.sum_eq_zero
  intro q member
  have code :
      exactLocallySampleableCode D q = t := by
    exact ((@Finset.mem_filter
      (ExactJointOutcome X Y A B D)
      (fun a => exactLocallySampleableCode D a = t)
      (fun _ => Classical.propDecidable _)
      Finset.univ q).mp member).2
  have coordinate :=
    congrArg
      (fun u : ExactLocallySampleableTuple X Y A B D =>
        u.1)
      code
  have history_coordinate :=
    congrArg
      (fun u : ExactLocallySampleableTuple X Y A B D =>
        u.2.2.2.seed.coordinate)
      code
  exact False.elim
    (different (coordinate.symm.trans history_coordinate))

theorem exactLocallySampleableLaw_accepted_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    exactHistoryAccepted G n D t.2.2.2 := by
  classical
  by_contra rejected
  exact supported
    (exactLocallySampleableLaw_zero_of_not_accepted
      G n S D t.1 t.2.1 t.2.2.1 t.2.2.2 rejected)

theorem exactLocallySampleableLaw_fiber_ne_zero_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    exactFiberQuestionMass
      G n D t.2.2.2.seed t.2.2.2.history
      t.2.1 t.2.2.1 ≠ 0 := by
  classical
  have coordinate :=
    exactLocallySampleableLaw_coordinate_eq_of_ne_zero
      G n S D t supported
  have accepted :=
    exactLocallySampleableLaw_accepted_of_ne_zero
      G n S D t supported
  intro zero
  have reveal_zero :
      exactRevealMass G n D
          t.2.2.2.seed t.2.2.2.history *
        G.questionWeight t.2.1 t.2.2.1 = 0 := by
    simpa [exactFiberQuestionMass_eq_jointQuestionMass,
      exactJointQuestionMass_eq_reveal_mul_question] using zero
  apply supported
  have source :=
    exactLocallySampleableLaw_eq_fair_born
      G n S D t.2.2.2 t.2.1 t.2.2.1
  have tuple :
      t =
        (t.2.2.2.seed.coordinate, t.2.1, t.2.2.1, t.2.2.2) := by
    rcases t with ⟨i, x, y, r⟩
    simpa using coordinate
  rw [tuple, source, if_pos accepted]
  rw [show
    exactSeedWeight t.2.2.2.seed *
        exactRevealMass G n D
          t.2.2.2.seed t.2.2.2.history *
        G.questionWeight t.2.1 t.2.2.1 =
      exactSeedWeight t.2.2.2.seed *
        (exactRevealMass G n D
          t.2.2.2.seed t.2.2.2.history *
          G.questionWeight t.2.1 t.2.2.1) by ring]
  simp [reveal_zero]

theorem exactLocallySampleableLaw_psi_ne_zero_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    exactUnnormalizedPsi
      G n S D t.2.2.2 t.2.1 t.2.2.1 ≠ 0 := by
  classical
  have coordinate :=
    exactLocallySampleableLaw_coordinate_eq_of_ne_zero
      G n S D t supported
  have accepted :=
    exactLocallySampleableLaw_accepted_of_ne_zero
      G n S D t supported
  intro zero
  apply supported
  have source :=
    exactLocallySampleableLaw_eq_fair_born
      G n S D t.2.2.2 t.2.1 t.2.2.1
  have tuple :
      t =
        (t.2.2.2.seed.coordinate, t.2.1, t.2.2.1, t.2.2.2) := by
    rcases t with ⟨i, x, y, r⟩
    simpa using coordinate
  rw [tuple, source, if_pos accepted, zero]
  simp

def dependentBlockPOVM
    {R C : Type*} [Fintype R] [DecidableEq R] [Fintype C]
    {ι : R → Type*}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (P : (r : R) → POVM C (ι r)) :
    POVM C (Σ r : R, ι r) where
  effect c := Matrix.blockDiagonal' fun r => (P r).effect c
  positive c := by
    apply posSemidef_blockDiagonal'
    intro r
    exact (P r).positive c
  complete := by
    classical
    ext ⟨r, u⟩ ⟨s, v⟩
    by_cases same : r = s
    · subst s
      have completed := congrArg
        (fun M : Matrix (ι r) (ι r) ℂ => M u v)
        (P r).complete
      simpa [Matrix.sum_apply, Matrix.blockDiagonal'_apply,
        Matrix.one_apply] using completed
    · simp [Matrix.sum_apply, Matrix.blockDiagonal'_apply,
        same]

def reindexedPOVM
    {C d e : Type*} [Fintype C]
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (basis : d ≃ e) (P : POVM C d) : POVM C e where
  effect c := (P.effect c).submatrix basis.symm basis.symm
  positive c := (P.positive c).submatrix basis.symm
  complete := by
    classical
    ext i j
    have completed := congrArg
      (fun M : Matrix d d ℂ => M (basis.symm i) (basis.symm j))
      P.complete
    simpa [Matrix.sum_apply, Matrix.one_apply] using completed

def twoBlockPOVM
    {C d e : Type} [Fintype C] [DecidableEq C]
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM C d) (Q : POVM C e) :
    POVM C (d ⊕ e) := by
  classical
  letI : (b : Bool) → Fintype (bif b then e else d)
    | false => inferInstanceAs (Fintype d)
    | true => inferInstanceAs (Fintype e)
  letI : (b : Bool) → DecidableEq (bif b then e else d)
    | false => inferInstanceAs (DecidableEq d)
    | true => inferInstanceAs (DecidableEq e)
  let blocks : (b : Bool) → POVM C (bif b then e else d)
    | false => P
    | true => Q
  exact reindexedPOVM
    (Equiv.sumEquivSigmaBool d e).symm
    (dependentBlockPOVM blocks)

def deterministicOutcomePOVM
    {C d : Type*} [Fintype C] [DecidableEq C]
    [Fintype d] [DecidableEq d] (default : C) : POVM C d where
  effect c := if c = default then 1 else 0
  positive c := by
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  complete := by
    classical
    simp

def pOVMChangeDecidableEq
    {C d : Type*} [Fintype C] [Fintype d]
    (source target : DecidableEq d)
    (P : @POVM C d inferInstance inferInstance source) :
    @POVM C d inferInstance inferInstance target where
  effect c := @POVM.effect C d inferInstance inferInstance source P c
  positive c := @POVM.positive C d
    inferInstance inferInstance source P c
  complete := by
    classical
    ext i j
    have completed := congrArg
      (fun M : Matrix d d ℂ => M i j)
      (@POVM.complete C d inferInstance inferInstance source P)
    simp only [Matrix.sum_apply, Matrix.one_apply] at completed ⊢
    by_cases same : i = j
    · subst j
      simpa using completed
    · simpa [same] using completed

def exactSourceAlicePaddedPOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) :
    POVM A (ExactPaddedLocalIndex G n S D r) := by
  classical
  exact twoBlockPOVM
    (deterministicOutcomePOVM (d := PUnit) a₀)
    (twoBlockPOVM
      (exactSourceAliceRefinedPOVM G n S D r a₀ x)
      (deterministicOutcomePOVM
        (d := ExactBobLocalIndex G n S D r) a₀))

def exactSourceBobPaddedPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) :
    POVM B (ExactPaddedLocalIndex G n S D r) := by
  classical
  exact twoBlockPOVM
    (deterministicOutcomePOVM (d := PUnit) b₀)
    (twoBlockPOVM
      (deterministicOutcomePOVM
        (d := ExactAliceLocalIndex G n S D r) b₀)
      (exactSourceBobRefinedPOVM G n S D r b₀ y))

def exactSourceGlobalAlicePOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (x : X) :
    POVM A (ExactGlobalHistoryLocalIndex G n S D) := by
  classical
  let actual := twoBlockPOVM
    (deterministicOutcomePOVM (d := PUnit) a₀)
    (dependentBlockPOVM
      (fun r : ExactHistoryFlag X Y A B D =>
        exactSourceAlicePaddedPOVM G n S D r a₀ x))
  exact pOVMChangeDecidableEq
    (@instDecidableEqSum PUnit
      (Σ r : ExactHistoryFlag X Y A B D,
        ExactPaddedLocalIndex G n S D r)
      inferInstance inferInstance)
    (Classical.decEq
      (ExactGlobalHistoryLocalIndex G n S D))
    actual

def exactSourceGlobalBobPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (b₀ : B) (y : Y) :
    POVM B (ExactGlobalHistoryLocalIndex G n S D) := by
  classical
  let actual := twoBlockPOVM
    (deterministicOutcomePOVM (d := PUnit) b₀)
    (dependentBlockPOVM
      (fun r : ExactHistoryFlag X Y A B D =>
        exactSourceBobPaddedPOVM G n S D r b₀ y))
  exact pOVMChangeDecidableEq
    (@instDecidableEqSum PUnit
      (Σ r : ExactHistoryFlag X Y A B D,
        ExactPaddedLocalIndex G n S D r)
      inferInstance inferInstance)
    (Classical.decEq
      (ExactGlobalHistoryLocalIndex G n S D))
    actual

def exactSourceGlobalCatalystAlicePOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) (a₀ : A) (x : X) :
    POVM A
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) := by
  classical
  exact reindexedPOVM finProdFinEquiv
    (purificationAlicePOVM (k := Fin e)
      (reindexedPOVM
        (Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D))
        (exactSourceGlobalAlicePOVM G n S D a₀ x)))

def exactSourceGlobalCatalystBobPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) (b₀ : B) (y : Y) :
    POVM B
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) := by
  classical
  exact reindexedPOVM finProdFinEquiv
    (purificationAlicePOVM (k := Fin e)
      (reindexedPOVM
        (Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D))
        (exactSourceGlobalBobPOVM G n S D b₀ y)))

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

@[simp] theorem twoBlockPOVM_effect_inl
    {C d e : Type} [Fintype C] [DecidableEq C]
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM C d) (Q : POVM C e)
    (c : C) (i j : d) :
    (twoBlockPOVM P Q).effect c
      (.inl i) (.inl j) = P.effect c i j := by
  classical
  simp [twoBlockPOVM, reindexedPOVM,
    dependentBlockPOVM, Equiv.sumEquivSigmaBool,
    Matrix.blockDiagonal'_apply]

@[simp] theorem twoBlockPOVM_effect_inr
    {C d e : Type} [Fintype C] [DecidableEq C]
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM C d) (Q : POVM C e)
    (c : C) (i j : e) :
    (twoBlockPOVM P Q).effect c
      (.inr i) (.inr j) = Q.effect c i j := by
  classical
  simp [twoBlockPOVM, reindexedPOVM,
    dependentBlockPOVM, Equiv.sumEquivSigmaBool,
    Matrix.blockDiagonal'_apply]

@[simp] theorem dependentBlockPOVM_effect_same
    {R C : Type*} [Fintype R] [DecidableEq R] [Fintype C]
    {ι : R → Type*}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (P : (r : R) → POVM C (ι r))
    (r : R) (c : C) (i j : ι r) :
    (dependentBlockPOVM P).effect c
      ⟨r, i⟩ ⟨r, j⟩ = (P r).effect c i j := by
  classical
  simp [dependentBlockPOVM,
    Matrix.blockDiagonal'_apply]

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

@[simp] theorem exactSourceGlobalAlicePOVM_effect
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ a : A) (x : X)
    (i j : ExactAliceLocalIndex G n S D r) :
    (exactSourceGlobalAlicePOVM G n S D a₀ x).effect a
      (.inr ⟨r, .inr (.inl i)⟩)
      (.inr ⟨r, .inr (.inl j)⟩) =
      (exactSourceAliceRefinedPOVM G n S D r a₀ x).effect a i j := by
  classical
  simp [exactSourceGlobalAlicePOVM,
    pOVMChangeDecidableEq,
    exactSourceAlicePaddedPOVM]

@[simp] theorem exactSourceGlobalBobPOVM_effect
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (b₀ b : B) (y : Y)
    (i j : ExactBobLocalIndex G n S D r) :
    (exactSourceGlobalBobPOVM G n S D b₀ y).effect b
      (.inr ⟨r, .inr (.inr i)⟩)
      (.inr ⟨r, .inr (.inr j)⟩) =
      (exactSourceBobRefinedPOVM G n S D r b₀ y).effect b i j := by
  classical
  simp [exactSourceGlobalBobPOVM,
    pOVMChangeDecidableEq,
    exactSourceBobPaddedPOVM]

theorem matrixQuadraticExpectation_expand
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℂ) (z : EuclideanSpace ℂ d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) M) z =
      (∑ i : d, (∑ j : d, M i j * z j) * star (z i)).re := by
  simp [quadraticExpectation, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.mulVec, dotProduct]

theorem finiteSum_injective_support
    {d e K : Type*} [Fintype d] [Fintype e] [AddCommMonoid K]
    (f : d → e) (injective : Function.Injective f)
    (g : e → K)
    (supported : ∀ j : e, (∀ i : d, f i ≠ j) → g j = 0) :
    (∑ j : e, g j) = ∑ i : d, g (f i) := by
  classical
  calc
    (∑ j : e, g j) = ∑ j ∈ Finset.univ.image f, g j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ outside
      apply supported j
      intro i same
      exact outside
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, same⟩)
    _ = ∑ i : d, g (f i) := by
      rw [Finset.sum_image]
      intro i _ j _ same
      exact injective same

theorem matrixQuadraticExpectation_injective
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (f : d → e) (injective : Function.Injective f)
    (M : Matrix e e ℂ) (N : Matrix d d ℂ)
    (v : EuclideanSpace ℂ e) (z : EuclideanSpace ℂ d)
    (included : ∀ i : d, v (f i) = z i)
    (supported : ∀ j : e, (∀ i : d, f i ≠ j) → v j = 0)
    (compressed : ∀ i j : d, M (f i) (f j) = N i j) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := e) (𝕜 := ℂ) M) v =
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) N) z := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  congr 1
  rw [finiteSum_injective_support f injective
    (fun i : e => (∑ j : e, M i j * v j) * star (v i))
    (by
      intro i outside
      simp [supported i outside])]
  apply Finset.sum_congr rfl
  intro i _
  rw [included i]
  congr 1
  rw [finiteSum_injective_support f injective
    (fun j : e => M (f i) j * v j)
    (by
      intro j outside
      simp [supported j outside])]
  apply Finset.sum_congr rfl
  intro j _
  rw [compressed i j, included j]

def exactSourceGlobalJointBasis
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    (ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) →
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D)
  | (i, j) =>
    (.inr ⟨r, .inr (.inl i)⟩, .inr ⟨r, .inr (.inr j)⟩)

theorem exactSourceGlobalJointBasis_injective
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    Function.Injective (exactSourceGlobalJointBasis G n S D r) := by
  intro i j same
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  have alice := congrArg Prod.fst same
  have bob := congrArg Prod.snd same
  change
    (Sum.inr ⟨r, .inr (.inl ia)⟩ :
      ExactGlobalHistoryLocalIndex G n S D) =
      Sum.inr ⟨r, .inr (.inl ja)⟩ at alice
  change
    (Sum.inr ⟨r, .inr (.inr ib)⟩ :
      ExactGlobalHistoryLocalIndex G n S D) =
      Sum.inr ⟨r, .inr (.inr jb)⟩ at bob
  have alice_block :
      (Sum.inr (.inl ia) : ExactPaddedLocalIndex G n S D r) =
        Sum.inr (.inl ja) :=
    eq_of_heq (Sigma.mk.inj (Sum.inr.inj alice)).2
  have bob_block :
      (Sum.inr (.inr ib) : ExactPaddedLocalIndex G n S D r) =
        Sum.inr (.inr jb) :=
    eq_of_heq (Sigma.mk.inj (Sum.inr.inj bob)).2
  have alice' : ia = ja :=
    Sum.inl.inj (Sum.inr.inj alice_block)
  have bob' : ib = jb :=
    Sum.inr.inj (Sum.inr.inj bob_block)
  exact Prod.ext alice' bob'

theorem exactSourceGlobalJointBasis_vector
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r))
    (i : ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) :
    exactGlobalHistoryVector G n S D r
        (exactPaddedVector G n S D r z)
        (exactSourceGlobalJointBasis G n S D r i) =
      z i := by
  rcases i with ⟨ia, ib⟩
  change
    (if ha : r = r then
      if hb : r = r then
        exactPaddedVector G n S D r z
          (ha ▸ Sum.inr (Sum.inl ia),
            hb ▸ Sum.inr (Sum.inr ib))
      else 0
    else 0) = z (ia, ib)
  simp only [exactPaddedVector, dite_true]

theorem exactSourceGlobalJointBasis_support
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r))
    (j : ExactGlobalHistoryLocalIndex G n S D ×
      ExactGlobalHistoryLocalIndex G n S D)
    (outside : ∀ i, exactSourceGlobalJointBasis
      G n S D r i ≠ j) :
    exactGlobalHistoryVector G n S D r
      (exactPaddedVector G n S D r z) j = 0 := by
  classical
  rcases j with ⟨u, v⟩
  rcases u with u | ⟨ru, u⟩
  · rfl
  rcases v with v | ⟨rv, v⟩
  · rfl
  change
    (if ha : ru = r then
      if hb : rv = r then
        exactPaddedVector G n S D r z
          (ha ▸ u, hb ▸ v)
      else 0
    else 0) = 0
  by_cases hu : ru = r
  · subst ru
    by_cases hv : rv = r
    · subst rv
      simp only [dite_true]
      rcases u with u | (u | u)
      · rfl
      · rcases v with v | (v | v)
        · rfl
        · rfl
        · exact False.elim
            (outside (u, v)
              (by rfl))
      · rfl
    · simp only [dif_neg hv, dite_true]
  · simp only [dif_neg hu]

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def exactSourceGlobalWinningEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    Matrix
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D)
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (exactSourceGlobalAlicePOVM G n S D a₀ x).effect a ⊗ₖ
        (exactSourceGlobalBobPOVM G n S D b₀ y).effect b
    else 0

theorem exactSourceGlobalWinningEffect_compression
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (i j : ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) :
    exactSourceGlobalWinningEffect G n S D a₀ b₀ x y
      (exactSourceGlobalJointBasis G n S D r i)
      (exactSourceGlobalJointBasis G n S D r j) =
      exactSourceWinningEffect G n S D r a₀ b₀ x y i j := by
  classical
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  simp only [exactSourceGlobalWinningEffect,
    exactSourceWinningEffect, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · simp only [exactSourceGlobalJointBasis,
      exactSourceJointEffect, Matrix.kroneckerMap_apply,
      exactSourceGlobalAlicePOVM_effect,
      exactSourceGlobalBobPOVM_effect]
  · rfl

theorem exactSourceGlobalWinningEffect_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := ExactGlobalHistoryLocalIndex G n S D ×
          ExactGlobalHistoryLocalIndex G n S D)
        (𝕜 := ℂ)
        (exactSourceGlobalWinningEffect G n S D a₀ b₀ x y))
      (exactGlobalHistoryVector G n S D r
        (exactPaddedVector G n S D r z)) =
      quadraticExpectation
        (exactSourceWinningEffectCLM G n S D r a₀ b₀ x y)
        z := by
  classical
  unfold exactSourceWinningEffectCLM
  apply matrixQuadraticExpectation_injective
    (exactSourceGlobalJointBasis G n S D r)
    (exactSourceGlobalJointBasis_injective G n S D r)
  · exact exactSourceGlobalJointBasis_vector G n S D r z
  · exact exactSourceGlobalJointBasis_support G n S D r z
  · exact exactSourceGlobalWinningEffect_compression
      G n S D r a₀ b₀ x y

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

@[simp] theorem reindexedCatalystPOVM_effect
    {C d : Type*} [Fintype C] [Fintype d] [DecidableEq d]
    (P : POVM C d) (e : ℕ) (c : C)
    (i j : d) (k l : Fin e) :
    (reindexedPOVM finProdFinEquiv
      (purificationAlicePOVM (k := Fin e)
        (reindexedPOVM (Fintype.equivFin d) P))).effect c
      (finProdFinEquiv ((Fintype.equivFin d) i, k))
      (finProdFinEquiv ((Fintype.equivFin d) j, l)) =
      P.effect c i j * (if k = l then 1 else 0) := by
  classical
  simp [reindexedPOVM, purificationAlicePOVM,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

@[simp] theorem exactSourceGlobalCatalystBobPOVM_effect
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) (b₀ b : B) (y : Y)
    (i j : ExactGlobalHistoryLocalIndex G n S D)
    (k l : Fin e) :
    (exactSourceGlobalCatalystBobPOVM G n S D e b₀ y).effect b
      (finProdFinEquiv
        (Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D) i, k))
      (finProdFinEquiv
        (Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D) j, l)) =
      (exactSourceGlobalBobPOVM G n S D b₀ y).effect b i j *
        (if k = l then 1 else 0) := by
  classical
  simp [exactSourceGlobalCatalystBobPOVM,
    reindexedPOVM, purificationAlicePOVM,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

end

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

theorem reweightedSeedPrefixEntropyIncrement_eq_actual_atom_sum
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ}
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (k : Fin h) :
    reweightedSeedPrefixEntropyIncrement
        seedLaw G n S D projection default k =
      ∑ point : K × ExactOutcome X Y A B n,
        reweightedSeedPosterior seedLaw G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (groupedMass (exactPrefixNextCode default k)
                (reweightedSeedPrefixJoint
                  seedLaw G n S D projection))
              (finitePrefixMask default k.castSucc
                (((projection point).1,
                  repeatedConditionedAnswerFlag
                    G n S D point.2),
                  (projection point).2)))
            (jointConditional
              (groupedMass (exactPrefixNextCode default k)
                (reweightedSeedPrefixPrior
                  seedLaw G n S D projection))
              (finitePrefixMask default k.castSucc
                (((projection point).1,
                  repeatedConditionedAnswerFlag
                    G n S D point.2),
                  (projection point).2))) := by
  classical
  let joint := reweightedSeedPrefixJoint
    seedLaw G n S D projection
  let prior := reweightedSeedPrefixPrior
    seedLaw G n S D projection
  let posterior := reweightedSeedPosterior
    seedLaw G n S D
  let augmented :
      K × ExactOutcome X Y A B n →
        (Ω × ConditionedAnswerFlag A B D) ×
          (Fin h → V) :=
    fun point =>
      (((projection point).1,
        repeatedConditionedAnswerFlag G n S D point.2),
        (projection point).2)
  let posteriorNext :=
    groupedMass (exactPrefixNextCode default k) joint
  let priorNext :=
    groupedMass (exactPrefixNextCode default k) prior
  let score :
      (Ω × ConditionedAnswerFlag A B D) ×
        (Fin h → V) → ℝ :=
    fun context =>
      finiteRelativeEntropy
        (jointConditional posteriorNext
          (finitePrefixMask default k.castSucc context))
        (jointConditional priorNext
          (finitePrefixMask default k.castSucc context))
  have hjoint : joint = groupedMass augmented posterior := by
    funext target
    exact reweightedSeedPrefixJoint_as_actual_flagged_pushforward
      seedLaw G n S D projection target
  calc
    reweightedSeedPrefixEntropyIncrement
        seedLaw G n S D projection default k =
      ∑ context :
        (Ω × ConditionedAnswerFlag A B D) ×
          (Fin h → V),
        groupedMass
            (finitePrefixMask default k.castSucc)
            joint context *
          finiteRelativeEntropy
            (jointConditional posteriorNext context)
            (jointConditional priorNext context) :=
      reweightedSeedPrefixEntropyIncrement_eq_conditional
        seedLaw G n S D positive projection default k
    _ = ∑ context :
        (Ω × ConditionedAnswerFlag A B D) ×
          (Fin h → V),
        jointFirstMarginal posteriorNext context *
          finiteRelativeEntropy
            (jointConditional posteriorNext context)
            (jointConditional priorNext context) := by
      apply Finset.sum_congr rfl
      intro context _
      congr 1
      convert (congrFun
        (exactPrefixNext_firstMarginal joint default k)
        context).symm using 1
      · exact congrFun
          (exactGroupedMass_decidableEq_irrel _ _
            (finitePrefixMask default k.castSucc) joint)
          context
      · exact congrArg
          (fun law => jointFirstMarginal law context)
          (exactGroupedMass_decidableEq_irrel _ _
            (exactPrefixNextCode default k) joint)
    _ = ∑ target :
        (Ω × ConditionedAnswerFlag A B D) ×
          (Fin h → V),
        joint target * score target := by
      exact finiteNextInformation_eq_atom_sum
        (finitePrefixMask default k.castSucc)
        (fun target :
          (Ω × ConditionedAnswerFlag A B D) ×
            (Fin h → V) => target.2 k)
        joint
        (fun context => jointConditional priorNext context)
    _ = ∑ point : K × ExactOutcome X Y A B n,
        posterior point * score (augmented point) := by
      rw [hjoint]
      exact finiteGroupedExpectation_eq_atom_sum
        augmented posterior score
    _ = _ := rfl

end

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

theorem exactStrategyQuestionCodeGroupedMass
    {C : Type*} [Fintype C] [DecidableEq C]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (code : (Fin n → X) → (Fin n → Y) → C)
    (target : C) :
    groupedMass
        (fun outcome : ExactOutcome X Y A B n =>
          code outcome.1 outcome.2.1)
        (strategyEventLaw (G.repeat n) S).weight target =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        if code xs ys = target then
          (G.repeat n).questionWeight xs ys
        else 0 := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  change
    (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      ∑ answersA : Fin n → A, ∑ answersB : Fin n → B,
        if code xs ys = target then
          (G.repeat n).questionWeight xs ys *
            S.outcomeProbability xs ys answersA answersB
        else 0) = _
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  by_cases compatible : code xs ys = target
  · simp only [if_pos compatible]
    calc
      (∑ answersA : Fin n → A, ∑ answersB : Fin n → B,
        (G.repeat n).questionWeight xs ys *
          S.outcomeProbability xs ys answersA answersB) =
        (G.repeat n).questionWeight xs ys *
          (∑ answersA : Fin n → A, ∑ answersB : Fin n → B,
            S.outcomeProbability xs ys answersA answersB) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro answersA _
              rw [Finset.mul_sum]
      _ = (G.repeat n).questionWeight xs ys := by
        rw [S.outcomeProbability_normalized xs ys]
        ring
  · simp [compatible]

theorem exactRepeatedQuestionWeight_splitAt_bob
    (G : Game X Y A B) (n : ℕ)
    (i : Fin n) (xs : Fin n → X)
    (y : Y) (tail : {j : Fin n // j ≠ i} → Y) :
    (G.repeat n).questionWeight xs
        ((Equiv.funSplitAt i Y).symm (y, tail)) =
      G.questionWeight (xs i) y *
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          G.questionWeight (xs j)
            ((Equiv.funSplitAt i Y).symm (y, tail) j) := by
  classical
  rw [Game.repeat_questionWeight]
  rw [← Finset.mul_prod_erase
    (Finset.univ : Finset (Fin n))
    (fun j : Fin n =>
      G.questionWeight (xs j)
        ((Equiv.funSplitAt i Y).symm (y, tail) j))
    (Finset.mem_univ i)]
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

theorem exactRepeatedQuestionTail_splitAt_bob
    (G : Game X Y A B) (n : ℕ)
    (i : Fin n) (xs : Fin n → X)
    (y y' : Y) (tail : {j : Fin n // j ≠ i} → Y) :
    (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      G.questionWeight (xs j)
        ((Equiv.funSplitAt i Y).symm (y, tail) j)) =
    (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      G.questionWeight (xs j)
        ((Equiv.funSplitAt i Y).symm (y', tail) j)) := by
  classical
  apply Finset.prod_congr rfl
  intro j hj
  have different : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [Equiv.funSplitAt, Equiv.piSplitAt, different]

end

end QuantumParallelRepetition

end
