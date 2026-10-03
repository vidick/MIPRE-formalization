/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Completion.lean, to the models of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.MainTheorem.ProjectiveConsistency.Evaluation
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Orthonormalization
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.ProjectivizationChain.Basic

@[expose] public section

/-!
# Source-boundary role-register handoff: completion lemmas

The completion and line-169 transport lemmas of the two-space tail of the main theorem: the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/SourceRoleRegister/Completion.lean` in the
port of `planning/c6b-plan.md` (milestone M13, section "Port conventions").

**Everything here is two-space.** The vendored state is on `ιA × ιB`, with Alice's measurements on
`ιA` and Bob's on `ιB`. Here it is a bipartite model `M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ` with a unit
vector, `hψ : ‖M.ψ‖ = 1`, and for the three theorems the model `strategy.state` of a two-space
`ProjStrat`, with `strategy.isNormalized`. The translation is that of
`Co/Test/MainTheorem/TwoSpace.lean`:
* the vendored `ConsRel ψ 𝒟 A B δ` is `bipartiteConsError M 𝒟 A B ≤ δ` (M2's two-space defect);
* `SDDRel ψ 𝒟 (leftPlacedSubMeas A) …` is `(TwoSpace.vecState M hψ).SDDRel 𝒟
  (TwoSpace.leftPlacedSubMeas M A) …`, a relation of the vector state on `M.H →L[ℂ] M.H`;
* `ev ψ (leftTensor X)` is `(TwoSpace.vecState M hψ).ev (TwoSpace.placeA M X)`, and the right
  forms likewise through `placeB`.
The same-space lemmas of Co `Preliminaries` (`completion_self_distance`, `constFamily_sdd_unit`,
`questionSDD_triangle`, `question_easyApproxFromApproxDelta`, `right_match_gap_abs_le_sqrt_qSDD`,
`stateDependentDistanceRel_triangle_three`) apply to the placed families as they are, and
`TwoSpace.simeqToApprox_heterogeneous` is the two-space `simeqToApprox_heterogeneous`.

The two matrix bookkeeping lemmas `qSDD_leftPlaced_completeAtOutcome_eq` and
`qSDD_rightPlaced_completeAtOutcome_eq`, entrywise Kronecker computations in the vendored file,
are here the fact that a placement commutes with completion (`placeA M 1 = 1` and `map_sub`).
They take any vector state `V : VecState M.H`, since they use only the placements.

**Departure: completion takes `hM : M.IsFinitePair`.** The vendored
`Preliminaries.completeAtOutcomeProj` needs a C⋆-algebra, and `𝒜`, `ℬ` are abstract star-ordered
`⋆`-algebras; so a projective submeasurement is completed through
`TwoSpace.completeAtOutcomeProjA`/`B`, which complete in the commutant that a finite pair
identifies each algebra with. The lemmas and theorems that complete therefore take
`hM : M.IsFinitePair` (`hM : strategy.state.IsFinitePair` for the theorems), placed right after the
state and, where it is taken, its normalization `hψ`. The completion's submeasurement is `completeAtOutcome P a0`
(`TwoSpace.completeAtOutcomeProjA_toSubMeas`), so nothing else changes.
`completedProjectiveConsistency_ofFullConsistency` completes nothing and takes no `hM`.

**Departure: imports.** The vendored file imports `SourceRoleRegister/Core`; this one imports Co
`Test/MainTheorem/ProjectiveConsistency/Evaluation` (with `TwoSpace`) and the M8 files
`MakingMeasurementsProjective/{Orthonormalization, ProjectivizationChain/Basic}`, which bring the
vendored classical constants `orthonormalizationError` and `orthonormalizeAndCompleteError`. No
declaration of the vendored `Core` is used, so the Co `Core` is not imported.

The constants are the vendored ones: `orthonormalizationError ζ` for the orthonormalization,
`orthonormalizeAndCompleteError ζ` after completion, `ζ + √(orthonormalizationError ζ)` for the
repaired line-169 consistency and `6ζ + 6ζ₂` for the line-156 distance.

## New here

- `bipartiteConsError_constFamily_unit`: the two-space defect of constant `Unit`-indexed families
  is the defect of their members (the two-space form of `Preliminaries.constFamily_sdd_unit`,
  which the vendored proofs unfold by `simp` at every use).

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.ProjStrat

open MIPStarRE.LDT (Parameters FieldModel avgOver avgOver_uniform_const uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.MakingMeasurementsProjective (orthonormalizationError
  orthonormalizeAndCompleteError)
open MIPRE.LIDT.Co.TwoSpace (placeA placeB vecState leftPlacedSubMeas rightPlacedSubMeas
  completeAtOutcomeProjA completeAtOutcomeProjB)

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

section Lemmas

variable (M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ)

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- The completion-distance bound for a placed submeasurement `B` with missing mass at most `ζ`:
`qSDD(B, complete B) = ev((1 − B_total)²) ≤ ev(1 − B_total) ≤ ζ`. -/
private theorem qSDD_completeAtOutcome_le_of_total_gap (V : VecState M.H) {Outcome : Type*}
    [Fintype Outcome] (B : SubMeas Outcome (M.H →L[ℂ] M.H)) (a0 : Outcome) {ζ : ℝ}
    (hgap : 1 - V.ev B.total ≤ ζ) :
    V.qSDD B (Preliminaries.completeAtOutcome B a0).toSubMeas ≤ ζ := by
  rw [Preliminaries.completion_self_distance]
  refine (V.ev_mono _ _ (sq_le_self (sub_nonneg.2 B.total_le_one)
    (sub_le_self _ B.total_nonneg))).trans ?_
  rwa [V.ev_sub, V.ev_one_of_isNormalized]

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- The two-space defect of constant `Unit`-indexed families under the uniform distribution is
the defect of their members. -/
theorem bipartiteConsError_constFamily_unit {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome 𝒜) (B : SubMeas Outcome ℬ) :
    bipartiteConsError M (uniformDistribution Unit) (constSubMeasFamily A)
        (constSubMeasFamily B) =
      qBipartiteConsDefect M A B :=
  avgOver_uniform_const (α := Unit) (qBipartiteConsDefect M A B)

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- Completing after left placement agrees with left placement after completing the local
submeasurement: a placement maps `1` to `1` and commutes with differences.

This is the bookkeeping needed to apply the completion-distance identity on `M.H` while returning
the local completed projective measurement of the paper. -/
theorem qSDD_leftPlaced_completeAtOutcome_eq {Outcome : Type*} [Fintype Outcome]
    (V : VecState M.H) (A B : SubMeas Outcome 𝒜) (a0 : Outcome) :
    V.qSDD (leftPlacedSubMeas M A)
        (Preliminaries.completeAtOutcome (leftPlacedSubMeas M B) a0).toSubMeas =
      V.qSDD (leftPlacedSubMeas M A)
        (leftPlacedSubMeas M (Preliminaries.completeAtOutcome B a0).toSubMeas) := by
  congr 1
  refine SubMeas.ext (fun a => ?_) (map_one (placeA M)).symm
  by_cases ha : a = a0
  · subst ha
    simp [Preliminaries.completeAtOutcome, leftPlacedSubMeas, map_sub]
  · simp [Preliminaries.completeAtOutcome, leftPlacedSubMeas, ha]

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- Completing after right placement agrees with right placement after completing the local
submeasurement. -/
theorem qSDD_rightPlaced_completeAtOutcome_eq {Outcome : Type*} [Fintype Outcome]
    (V : VecState M.H) (A B : SubMeas Outcome ℬ) (a0 : Outcome) :
    V.qSDD (rightPlacedSubMeas M A)
        (Preliminaries.completeAtOutcome (rightPlacedSubMeas M B) a0).toSubMeas =
      V.qSDD (rightPlacedSubMeas M A)
        (rightPlacedSubMeas M (Preliminaries.completeAtOutcome B a0).toSubMeas) := by
  congr 1
  refine SubMeas.ext (fun a => ?_) (map_one (placeB M)).symm
  by_cases ha : a = a0
  · subst ha
    simp [Preliminaries.completeAtOutcome, rightPlacedSubMeas, map_sub]
  · simp [Preliminaries.completeAtOutcome, rightPlacedSubMeas, ha]

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- If the missing left total of a projective submeasurement is small on the state, then its
completion is close to it after left placement. -/
theorem qSDD_completeAtOutcomeProj_leftPlaced_le_of_total_gap {Outcome : Type*}
    [Fintype Outcome] (hψ : ‖M.ψ‖ = 1) (hM : M.IsFinitePair) (P : ProjSubMeas Outcome 𝒜)
    (a0 : Outcome) {ζ : ℝ} (hgap : 1 - (vecState M hψ).ev (placeA M P.toSubMeas.total) ≤ ζ) :
    (vecState M hψ).qSDD (leftPlacedSubMeas M P.toSubMeas)
      (leftPlacedSubMeas M (completeAtOutcomeProjA hM P a0).toSubMeas) ≤ ζ := by
  rw [TwoSpace.completeAtOutcomeProjA_toSubMeas, ← qSDD_leftPlaced_completeAtOutcome_eq]
  exact qSDD_completeAtOutcome_le_of_total_gap M _ _ a0 hgap

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- Right-placement counterpart of `qSDD_completeAtOutcomeProj_leftPlaced_le_of_total_gap`. -/
theorem qSDD_completeAtOutcomeProj_rightPlaced_le_of_total_gap {Outcome : Type*}
    [Fintype Outcome] (hψ : ‖M.ψ‖ = 1) (hM : M.IsFinitePair) (P : ProjSubMeas Outcome ℬ)
    (a0 : Outcome) {ζ : ℝ} (hgap : 1 - (vecState M hψ).ev (placeB M P.toSubMeas.total) ≤ ζ) :
    (vecState M hψ).qSDD (rightPlacedSubMeas M P.toSubMeas)
      (rightPlacedSubMeas M (completeAtOutcomeProjB hM P a0).toSubMeas) ≤ ζ := by
  rw [TwoSpace.completeAtOutcomeProjB_toSubMeas, ← qSDD_rightPlaced_completeAtOutcome_eq]
  exact qSDD_completeAtOutcome_le_of_total_gap M _ _ a0 hgap

/-- A left-placement distance estimate controls the loss in two-space matching mass against a
complete measurement of the second player. -/
theorem qBipartiteMatchMass_ge_sub_sqrt_of_left_sdd_heterogeneous {Outcome : Type*}
    [Fintype Outcome] (hψ : ‖M.ψ‖ = 1) (G : Measurement Outcome 𝒜) (P : SubMeas Outcome 𝒜)
    (B : Measurement Outcome ℬ) {ε : ℝ}
    (hclose : (vecState M hψ).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas M G.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas M P)) ε) :
    qBipartiteMatchMass M P B.toSubMeas ≥
      qBipartiteMatchMass M G.toSubMeas B.toSubMeas - Real.sqrt ε := by
  have hq := hclose.squaredDistanceBound
  rw [Preliminaries.constFamily_sdd_unit] at hq
  have hgap := Preliminaries.question_easyApproxFromApproxDelta (vecState M hψ)
    (leftPlacedSubMeas M G.toSubMeas) (leftPlacedSubMeas M P) (rightPlacedSubMeas M B.toSubMeas)
  rw [TwoSpace.qBipartiteMatchMass_eq M hψ, TwoSpace.qBipartiteMatchMass_eq M hψ]
  unfold VecState.qMatchMass
  linarith [(abs_le.mp hgap).2, Real.sqrt_le_sqrt hq]

/-- A right-placement distance estimate controls the loss in two-space matching mass against a
complete measurement of the first player. -/
theorem qBipartiteMatchMass_ge_sub_sqrt_of_right_sdd_heterogeneous {Outcome : Type*}
    [Fintype Outcome] (hψ : ‖M.ψ‖ = 1) (A : Measurement Outcome 𝒜) (G : Measurement Outcome ℬ)
    (P : SubMeas Outcome ℬ) {ε : ℝ}
    (hclose : (vecState M hψ).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas M G.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas M P)) ε) :
    qBipartiteMatchMass M A.toSubMeas P ≥
      qBipartiteMatchMass M A.toSubMeas G.toSubMeas - Real.sqrt ε := by
  have hq := hclose.squaredDistanceBound
  rw [Preliminaries.constFamily_sdd_unit] at hq
  have hgap := Preliminaries.right_match_gap_abs_le_sqrt_qSDD (vecState M hψ)
    (leftPlacedSubMeas M A.toSubMeas) (rightPlacedSubMeas M G.toSubMeas) (rightPlacedSubMeas M P)
  rw [TwoSpace.qBipartiteMatchMass_eq M hψ, TwoSpace.qBipartiteMatchMass_eq M hψ]
  unfold VecState.qMatchMass
  linarith [(abs_le.mp hgap).2, Real.sqrt_le_sqrt hq]

/-- The two-space matching mass against a complete measurement of the second player is at most
the expectation of the placed total of the other submeasurement. -/
theorem qBipartiteMatchMass_le_left_total_of_measurement_heterogeneous {Outcome : Type*}
    [Fintype Outcome] (hψ : ‖M.ψ‖ = 1) (A : SubMeas Outcome 𝒜) (B : Measurement Outcome ℬ) :
    qBipartiteMatchMass M A B.toSubMeas ≤ (vecState M hψ).ev (placeA M A.total) :=
  calc qBipartiteMatchMass M A B.toSubMeas
      ≤ ∑ a, (vecState M hψ).ev (placeA M (A.outcome a)) :=
        Finset.sum_le_sum fun a _ =>
          TwoSpace.bornProb_le_qform_πA M (A.outcome_pos a) (B.outcome_le_one a)
    _ = (vecState M hψ).ev (placeA M A.total) := by
        rw [← VecState.ev_sum, ← map_sum, A.sum_eq_total]

/-- The two-space matching mass against a complete measurement of the first player is at most
the expectation of the placed total of the other submeasurement. -/
theorem qBipartiteMatchMass_le_right_total_of_measurement_heterogeneous {Outcome : Type*}
    [Fintype Outcome] (hψ : ‖M.ψ‖ = 1) (A : Measurement Outcome 𝒜) (B : SubMeas Outcome ℬ) :
    qBipartiteMatchMass M A.toSubMeas B ≤ (vecState M hψ).ev (placeB M B.total) :=
  calc qBipartiteMatchMass M A.toSubMeas B
      ≤ ∑ a, (vecState M hψ).ev (placeB M (B.outcome a)) :=
        Finset.sum_le_sum fun a _ =>
          TwoSpace.bornProb_le_qform_πB M (A.outcome_le_one a) (B.outcome_pos a)
    _ = (vecState M hψ).ev (placeB M B.total) := by
        rw [← VecState.ev_sum, ← map_sum, B.sum_eq_total]

/-- Completing a projective submeasurement of the first player can only increase its two-space
matching mass against a fixed submeasurement of the second player. -/
theorem completeAtOutcomeProj_left_matchMass_ge_heterogeneous {Outcome : Type*}
    [Fintype Outcome] (hM : M.IsFinitePair) (P : ProjSubMeas Outcome 𝒜) (B : SubMeas Outcome ℬ)
    (a0 : Outcome) :
    qBipartiteMatchMass M (completeAtOutcomeProjA hM P a0).toSubMeas B ≥
      qBipartiteMatchMass M P.toSubMeas B := by
  rw [TwoSpace.completeAtOutcomeProjA_toSubMeas]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : a = a0
  · subst ha
    have hextra := M.bornProb_nonneg (sub_nonneg.2 P.toSubMeas.total_le_one) (B.outcome_pos a)
    have hadd : M.bornProb (P.toSubMeas.outcome a + (1 - P.toSubMeas.total)) (B.outcome a) =
        M.bornProb (P.toSubMeas.outcome a) (B.outcome a) +
          M.bornProb (1 - P.toSubMeas.total) (B.outcome a) := by
      unfold MIPRE.BipartiteModel.bornProb
      rw [map_add, add_mul, M.qform_add]
    simp only [Preliminaries.completeAtOutcome, dite_true, hadd]
    linarith
  · simp [Preliminaries.completeAtOutcome, ha]

/-- Completing a projective submeasurement of the second player can only increase its two-space
matching mass against a fixed submeasurement of the first player. -/
theorem completeAtOutcomeProj_right_matchMass_ge_heterogeneous {Outcome : Type*}
    [Fintype Outcome] (hM : M.IsFinitePair) (A : SubMeas Outcome 𝒜) (P : ProjSubMeas Outcome ℬ)
    (a0 : Outcome) :
    qBipartiteMatchMass M A (completeAtOutcomeProjB hM P a0).toSubMeas ≥
      qBipartiteMatchMass M A P.toSubMeas := by
  rw [TwoSpace.completeAtOutcomeProjB_toSubMeas]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : a = a0
  · subst ha
    have hextra := M.bornProb_nonneg (A.outcome_pos a) (sub_nonneg.2 P.toSubMeas.total_le_one)
    have hadd : M.bornProb (A.outcome a) (P.toSubMeas.outcome a + (1 - P.toSubMeas.total)) =
        M.bornProb (A.outcome a) (P.toSubMeas.outcome a) +
          M.bornProb (A.outcome a) (1 - P.toSubMeas.total) := by
      unfold MIPRE.BipartiteModel.bornProb
      rw [map_add, mul_add, M.qform_add]
    simp only [Preliminaries.completeAtOutcome, dite_true, hadd]
    linarith
  · simp [Preliminaries.completeAtOutcome, ha]

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- For measurements `G_A`, `G_B` consistent at `ζ`, the missing mass is `1 − match ≤ ζ`. -/
private theorem one_sub_matchMass_le_of_consistency (hψ : ‖M.ψ‖ = 1) {Outcome : Type*}
    [Fintype Outcome] {ζ : ℝ} (G_A : Measurement Outcome 𝒜) (G_B : Measurement Outcome ℬ)
    (hpre : bipartiteConsError M (uniformDistribution Unit) (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ≤ ζ) :
    1 - qBipartiteMatchMass M G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
  rw [bipartiteConsError_constFamily_unit] at hpre
  refine le_trans ?_ hpre
  rw [qBipartiteConsDefect, G_A.total_eq_one, G_B.total_eq_one, M.bornProb_one_one hψ]
  exact le_max_right _ _

/-- Combine cross consistency and the first player's orthonormalization closeness into the
completion estimate for the left placement. -/
theorem completedCloseness_left_of_consistency_and_sdd {Outcome : Type*} [Fintype Outcome]
    (hψ : ‖M.ψ‖ = 1) (hM : M.IsFinitePair) (ζ : ℝ) (G_A : Measurement Outcome 𝒜)
    (G_B : Measurement Outcome ℬ) (P_A : ProjSubMeas Outcome 𝒜) (a0 : Outcome)
    (hpre : bipartiteConsError M (uniformDistribution Unit) (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ≤ ζ)
    (horth : (vecState M hψ).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas M G_A.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas M P_A.toSubMeas)) (orthonormalizationError ζ)) :
    (vecState M hψ).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas M G_A.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas M (completeAtOutcomeProjA hM P_A a0).toSubMeas))
      (orthonormalizeAndCompleteError ζ) := by
  have hζ0 : 0 ≤ ζ := (bipartiteConsError_nonneg M _ _ _).trans hpre
  have hmatch_G := one_sub_matchMass_le_of_consistency M hψ G_A G_B hpre
  have hmatch_P := qBipartiteMatchMass_ge_sub_sqrt_of_left_sdd_heterogeneous M hψ G_A
    P_A.toSubMeas G_B horth
  have hmatch_le := qBipartiteMatchMass_le_left_total_of_measurement_heterogeneous M hψ
    P_A.toSubMeas G_B
  have hPP := qSDD_completeAtOutcomeProj_leftPlaced_le_of_total_gap M hψ hM P_A a0
    (ζ := ζ + Real.sqrt (orthonormalizationError ζ)) (by linarith)
  have hGP := horth.squaredDistanceBound
  rw [Preliminaries.constFamily_sdd_unit] at hGP
  refine ⟨?_⟩
  rw [Preliminaries.constFamily_sdd_unit]
  refine (Preliminaries.questionSDD_triangle _ _ (leftPlacedSubMeas M P_A.toSubMeas) _).trans ?_
  unfold orthonormalizeAndCompleteError
  linarith [Real.sqrt_nonneg (orthonormalizationError ζ)]

/-- Second-player counterpart of `completedCloseness_left_of_consistency_and_sdd`. -/
theorem completedCloseness_right_of_consistency_and_sdd {Outcome : Type*} [Fintype Outcome]
    (hψ : ‖M.ψ‖ = 1) (hM : M.IsFinitePair) (ζ : ℝ) (G_A : Measurement Outcome 𝒜)
    (G_B : Measurement Outcome ℬ) (P_B : ProjSubMeas Outcome ℬ) (a0 : Outcome)
    (hpre : bipartiteConsError M (uniformDistribution Unit) (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ≤ ζ)
    (horth : (vecState M hψ).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas M G_B.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas M P_B.toSubMeas)) (orthonormalizationError ζ)) :
    (vecState M hψ).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas M G_B.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas M (completeAtOutcomeProjB hM P_B a0).toSubMeas))
      (orthonormalizeAndCompleteError ζ) := by
  have hζ0 : 0 ≤ ζ := (bipartiteConsError_nonneg M _ _ _).trans hpre
  have hmatch_G := one_sub_matchMass_le_of_consistency M hψ G_A G_B hpre
  have hmatch_P := qBipartiteMatchMass_ge_sub_sqrt_of_right_sdd_heterogeneous M hψ G_A G_B
    P_B.toSubMeas horth
  have hmatch_le := qBipartiteMatchMass_le_right_total_of_measurement_heterogeneous M hψ G_A
    P_B.toSubMeas
  have hPP := qSDD_completeAtOutcomeProj_rightPlaced_le_of_total_gap M hψ hM P_B a0
    (ζ := ζ + Real.sqrt (orthonormalizationError ζ)) (by linarith)
  have hGP := horth.squaredDistanceBound
  rw [Preliminaries.constFamily_sdd_unit] at hGP
  refine ⟨?_⟩
  rw [Preliminaries.constFamily_sdd_unit]
  refine (Preliminaries.questionSDD_triangle _ _ (rightPlacedSubMeas M P_B.toSubMeas) _).trans ?_
  unfold orthonormalizeAndCompleteError
  linarith [Real.sqrt_nonneg (orthonormalizationError ζ)]

/-- The first player's repaired line-169 consistency after completing the projective
submeasurement.

This is the two-space analogue of the paper's `Q^A_g ⊗ I ≃ I ⊗ G^B_g` step, with the checked
repaired loss `ζ + √(orthonormalizationError ζ)`. -/
theorem completedLeftConsistency_of_consistency_and_sdd {Outcome : Type*} [Fintype Outcome]
    (hψ : ‖M.ψ‖ = 1) (hM : M.IsFinitePair) (ζ : ℝ) (G_A : Measurement Outcome 𝒜)
    (G_B : Measurement Outcome ℬ) (P_A : ProjSubMeas Outcome 𝒜) (a0 : Outcome)
    (hpre : bipartiteConsError M (uniformDistribution Unit) (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ≤ ζ)
    (horth : (vecState M hψ).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas M G_A.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas M P_A.toSubMeas)) (orthonormalizationError ζ)) :
    bipartiteConsError M (uniformDistribution Unit)
      (constSubMeasFamily (completeAtOutcomeProjA hM P_A a0).toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ≤
        ζ + Real.sqrt (orthonormalizationError ζ) := by
  have hζ0 : 0 ≤ ζ := (bipartiteConsError_nonneg M _ _ _).trans hpre
  have hmatch_G := one_sub_matchMass_le_of_consistency M hψ G_A G_B hpre
  have hmatch_P := qBipartiteMatchMass_ge_sub_sqrt_of_left_sdd_heterogeneous M hψ G_A
    P_A.toSubMeas G_B horth
  have hmatch_Q := completeAtOutcomeProj_left_matchMass_ge_heterogeneous M hM P_A G_B.toSubMeas a0
  rw [bipartiteConsError_constFamily_unit, qBipartiteConsDefect,
    (completeAtOutcomeProjA hM P_A a0).total_eq_one, G_B.total_eq_one, M.bornProb_one_one hψ]
  exact max_le (add_nonneg hζ0 (Real.sqrt_nonneg _)) (by linarith)

/-- The second player's repaired line-169 consistency after completing the projective
submeasurement: the two-space analogue of the role-reversed relation `G^A_g ⊗ I ≃ I ⊗ Q^B_g`. -/
theorem completedRightConsistency_of_consistency_and_sdd {Outcome : Type*} [Fintype Outcome]
    (hψ : ‖M.ψ‖ = 1) (hM : M.IsFinitePair) (ζ : ℝ) (G_A : Measurement Outcome 𝒜)
    (G_B : Measurement Outcome ℬ) (P_B : ProjSubMeas Outcome ℬ) (a0 : Outcome)
    (hpre : bipartiteConsError M (uniformDistribution Unit) (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ≤ ζ)
    (horth : (vecState M hψ).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas M G_B.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas M P_B.toSubMeas)) (orthonormalizationError ζ)) :
    bipartiteConsError M (uniformDistribution Unit) (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily (completeAtOutcomeProjB hM P_B a0).toSubMeas) ≤
        ζ + Real.sqrt (orthonormalizationError ζ) := by
  have hζ0 : 0 ≤ ζ := (bipartiteConsError_nonneg M _ _ _).trans hpre
  have hmatch_G := one_sub_matchMass_le_of_consistency M hψ G_A G_B hpre
  have hmatch_P := qBipartiteMatchMass_ge_sub_sqrt_of_right_sdd_heterogeneous M hψ G_A G_B
    P_B.toSubMeas horth
  have hmatch_Q := completeAtOutcomeProj_right_matchMass_ge_heterogeneous M hM G_A.toSubMeas P_B a0
  rw [bipartiteConsError_constFamily_unit, qBipartiteConsDefect, G_A.total_eq_one,
    (completeAtOutcomeProjB hM P_B a0).total_eq_one, M.bornProb_one_one hψ]
  exact max_le (add_nonneg hζ0 (Real.sqrt_nonneg _)) (by linarith)

end Lemmas

/-! ### The strategy-level theorems -/

/-- Complete the two projective submeasurements obtained after the line-130 cross-consistency
estimate to projective measurements, with the placed state-dependent-distance estimates the paper
requires.

Paper origin: `references/ldt-paper/inductive_step.tex:143-149`. Consistency bounds the mass
missing from each projective submeasurement once the orthonormalization distance is charged by
Cauchy–Schwarz, and the completion residual contributes at most that mass. -/
theorem completedProjectiveMeasurements_ofTwoSidedSubmeasurements (params : Parameters)
    [FieldModel params.q] (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsFinitePair)
    (G_A : Measurement (MIPStarRE.LDT.Polynomial params) 𝒜)
    (G_B : Measurement (MIPStarRE.LDT.Polynomial params) ℬ)
    (P_A : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝒜)
    (P_B : ProjSubMeas (MIPStarRE.LDT.Polynomial params) ℬ) (ζ : ℝ)
    (hfull : bipartiteConsError strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤ ζ)
    (hleft : (vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas strategy.state G_A.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas strategy.state P_A.toSubMeas))
      (orthonormalizationError ζ))
    (hright : (vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas strategy.state G_B.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas strategy.state P_B.toSubMeas))
      (orthonormalizationError ζ)) :
    ∃ Q_A : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
      ∃ Q_B : ProjMeas (MIPStarRE.LDT.Polynomial params) ℬ,
        (vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas strategy.state G_A.toSubMeas))
          (constSubMeasFamily (leftPlacedSubMeas strategy.state Q_A.toSubMeas))
          (orthonormalizeAndCompleteError ζ) ∧
        (vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
          (constSubMeasFamily (rightPlacedSubMeas strategy.state G_B.toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas strategy.state Q_B.toSubMeas))
          (orthonormalizeAndCompleteError ζ) := by
  let a0 : MIPStarRE.LDT.Polynomial params :=
    ⟨0, fun i => (MvPolynomial.degreeOf_zero i).trans_le (Nat.zero_le _)⟩
  exact ⟨completeAtOutcomeProjA hM P_A a0, completeAtOutcomeProjB hM P_B a0,
    completedCloseness_left_of_consistency_and_sdd _ strategy.isNormalized hM ζ G_A G_B P_A a0
      hfull hleft,
    completedCloseness_right_of_consistency_and_sdd _ strategy.isNormalized hM ζ G_A G_B P_B a0
      hfull hright⟩

/-- Complete the two projective submeasurements and derive the two repaired polynomial line-169
consistency relations.

Paper origin: `references/ldt-paper/inductive_step.tex:167-172`. The paper applies
`triangle-sub` after the completion estimates; the statement here is the checked repaired version,
in which the replacement of `G_A` by `Q_A` and of `G_B` by `Q_B` is charged directly from the
pre-completion orthonormalization distance, giving the error `ζ + √(orthonormalizationError ζ)`. -/
theorem completedProjectiveMeasurementsAndLine169_ofTwoSidedSubmeasurements (params : Parameters)
    [FieldModel params.q] (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (hM : strategy.state.IsFinitePair)
    (G_A : Measurement (MIPStarRE.LDT.Polynomial params) 𝒜)
    (G_B : Measurement (MIPStarRE.LDT.Polynomial params) ℬ)
    (P_A : ProjSubMeas (MIPStarRE.LDT.Polynomial params) 𝒜)
    (P_B : ProjSubMeas (MIPStarRE.LDT.Polynomial params) ℬ) (ζ : ℝ)
    (hfull : bipartiteConsError strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤ ζ)
    (hleft : (vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas strategy.state G_A.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas strategy.state P_A.toSubMeas))
      (orthonormalizationError ζ))
    (hright : (vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas strategy.state G_B.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas strategy.state P_B.toSubMeas))
      (orthonormalizationError ζ)) :
    ∃ Q_A : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝒜,
      ∃ Q_B : ProjMeas (MIPStarRE.LDT.Polynomial params) ℬ,
        (vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas strategy.state G_A.toSubMeas))
          (constSubMeasFamily (leftPlacedSubMeas strategy.state Q_A.toSubMeas))
          (orthonormalizeAndCompleteError ζ) ∧
        (vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
          (constSubMeasFamily (rightPlacedSubMeas strategy.state G_B.toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas strategy.state Q_B.toSubMeas))
          (orthonormalizeAndCompleteError ζ) ∧
        bipartiteConsError strategy.state (uniformDistribution Unit)
          (constSubMeasFamily Q_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤
            ζ + Real.sqrt (orthonormalizationError ζ) ∧
        bipartiteConsError strategy.state (uniformDistribution Unit)
          (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily Q_B.toSubMeas) ≤
            ζ + Real.sqrt (orthonormalizationError ζ) := by
  let a0 : MIPStarRE.LDT.Polynomial params :=
    ⟨0, fun i => (MvPolynomial.degreeOf_zero i).trans_le (Nat.zero_le _)⟩
  exact ⟨completeAtOutcomeProjA hM P_A a0, completeAtOutcomeProjB hM P_B a0,
    completedCloseness_left_of_consistency_and_sdd _ strategy.isNormalized hM ζ G_A G_B P_A a0
      hfull hleft,
    completedCloseness_right_of_consistency_and_sdd _ strategy.isNormalized hM ζ G_A G_B P_B a0
      hfull hright,
    completedLeftConsistency_of_consistency_and_sdd _ strategy.isNormalized hM ζ G_A G_B P_A a0
      hfull hleft,
    completedRightConsistency_of_consistency_and_sdd _ strategy.isNormalized hM ζ G_A G_B P_B a0
      hfull hright⟩

/-- The line-156 projective consistency estimate after completing both polynomial
submeasurements.

Paper origin: `references/ldt-paper/inductive_step.tex:150-157`. The consistency of `G_A`, `G_B`
gives the distance `2ζ` of their placements (`TwoSpace.simeqToApprox_heterogeneous`), which
telescopes through the two completion-distance estimates for `Q_A` and `Q_B`. -/
theorem completedProjectiveConsistency_ofFullConsistency (params : Parameters)
    [FieldModel params.q] (strategy : ProjStrat params 𝒞 𝒜 ℬ)
    (G_A : Measurement (MIPStarRE.LDT.Polynomial params) 𝒜)
    (G_B : Measurement (MIPStarRE.LDT.Polynomial params) ℬ)
    (Q_A : ProjMeas (MIPStarRE.LDT.Polynomial params) 𝒜)
    (Q_B : ProjMeas (MIPStarRE.LDT.Polynomial params) ℬ) (ζ : ℝ)
    (hfull : bipartiteConsError strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas) (constSubMeasFamily G_B.toSubMeas) ≤ ζ)
    (hleftComplete : (vecState strategy.state strategy.isNormalized).SDDRel
      (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas strategy.state G_A.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas strategy.state Q_A.toSubMeas))
      (orthonormalizeAndCompleteError ζ))
    (hrightComplete : (vecState strategy.state strategy.isNormalized).SDDRel
      (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas strategy.state G_B.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas strategy.state Q_B.toSubMeas))
      (orthonormalizeAndCompleteError ζ)) :
    let ζ₂ : ℝ := orthonormalizeAndCompleteError ζ
    (vecState strategy.state strategy.isNormalized).SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas strategy.state Q_A.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas strategy.state Q_B.toSubMeas))
      (6 * ζ + 6 * ζ₂) := by
  intro ζ₂
  set V := vecState strategy.state strategy.isNormalized
  have hmid : V.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas strategy.state G_A.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas strategy.state G_B.toSubMeas)) (2 * ζ) :=
    TwoSpace.simeqToApprox_heterogeneous strategy.state strategy.isNormalized
      (uniformDistribution Unit) (fun _ => G_A) (fun _ => G_B) ζ hfull
  exact Preliminaries.stateDependentDistanceRel_mono V (uniformDistribution Unit) _ _ _ _
    (by ring_nf; exact le_rfl)
    (Preliminaries.stateDependentDistanceRel_triangle_three V (uniformDistribution Unit) _
      (constSubMeasFamily (leftPlacedSubMeas strategy.state G_A.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas strategy.state G_B.toSubMeas)) _ ζ₂ (2 * ζ) ζ₂
      (Preliminaries.sddRel_symm V (uniformDistribution Unit) _ _ ζ₂ hleftComplete) hmid
      hrightComplete)

end MIPRE.LIDT.Co.ProjStrat

end
