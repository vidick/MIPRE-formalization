/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Statements
public import MIPRE.Background.LIDT.Co.Basic.MeasurementLift
public import MIPRE.Background.LIDT.Co.Preliminaries.BipartiteSelfConsistency.Completion
public import MIPRE.Background.LIDT.Co.Preliminaries.CauchySchwarz
public import MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization

@[expose] public section

/-!
# Section 5 — Rounding to projectors, core

The consistency-to-almost-projective step of the rounding-to-projectors chain, with its
Cauchy–Schwarz helpers, and the zero projective submeasurement used in trivial large-error
branches: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean` in the
port of `planning/c6b-plan.md` (milestone M8, section "Port conventions").

**One carrier.** The vendored bipartite lemmas take a state `ψ` on `ιA × ιB`, a measurement on
each factor and named carrier arguments `(ι₂ := ιB)`, `(ι₁ := ιA)`. Here they are narrowed to a
symmetric model `S : SymModel 𝔓 K`, with both measurements local in `𝔓`, as milestone M3 did for
`triangleSub_heterogeneous` ("Departures in M3 and M5"): `leftTensor` is `S.L`, `rightTensor`
is `S.R`, `leftPlacedSubMeas` is `S.leftPlacedSubMeas` and `leftLiftedMeasurement` is
`S.leftLiftedMeasurement`. Each takes the model as an explicit first argument, in the namespace
`MakingMeasurementsProjective`. The two-space use is served separately, by the heterogeneous
lemmas of `Co/MakingMeasurementsProjective/Orthonormalization.lean`
(`one_sub_two_mul_le_sum_norm_sq_πA`/`_πB`,
`orthonormalizationMeasurement_{,right_}of_consistency_from_projectivizationRepair_heterogeneous`),
for milestone M13.

`sourceAlmostProjective_of_ssc` and `sourceAlmostProjective_nonneg` are about a state on one
space and take a vector state `V : VecState K` with a joint measurement in `K →L[ℂ] K`.
`zeroProjSubMeas` mentions no state and is generic over an ordered `⋆`-ring, so that it serves
the local algebra `𝔓` and the joint operators alike. The vendored hypotheses `hψ : ψ.IsNormalized`
of the two `qSDD_*Placed_zeroProjSubMeas_le_one` lemmas are dropped (`S.ev 1 = 1` is a theorem),
and their entrywise matrix step is `map_zero`. The unused vendored instance arguments
`[DecidableEq Outcome]` of `consistencyToAlmostProjective` and its right form are dropped.

The pure real inequality `totalMass_sub_two_defect_le_diagA` and the error function
`consistencyToAlmostProjectiveError` are classical; they are imported from the vendored
`Projectivization.lean` and `Defs.lean` and named through an explicit `open` list.

## Not ported


## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/orthonormalization.tex`
- `blueprint/src/chapter/ch04_projective.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MakingMeasurementsProjective

open MIPStarRE.LDT (avgOver uniformDistribution)
open MIPStarRE.LDT.MakingMeasurementsProjective (consistencyToAlmostProjectiveError)

/-- Lower bound for the `diagA` sum in terms of the overlap and the bipartite consistency defect,
obtained from the Cauchy–Schwarz squared bound. Upstream keeps it `private` since its
Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy. -/
theorem totalMass_sub_two_defect_le_diagA {diagA diagB totalMass defect overlap : ℝ}
    (hdiagA_nonneg : 0 ≤ diagA) (hdefect_nonneg : 0 ≤ defect) (hdefect_eq : defect = totalMass - overlap)
    (hoverlap_sq : overlap ^ 2 ≤ diagA * diagB) (hdiagB_le : diagB ≤ totalMass) :
    totalMass - 2 * defect ≤ diagA := by
  by_cases hsmall : totalMass ≤ defect
  · linarith
  · have hmass_pos : 0 < totalMass := by
      have hdefect_lt : defect < totalMass := lt_of_not_ge hsmall
      linarith
    have hoverlap_eq : overlap = totalMass - defect := by linarith [hdefect_eq]
    have hsquare : (totalMass - defect) ^ 2 ≤ diagA * totalMass := by
      nlinarith [hoverlap_eq, hoverlap_sq, hdiagB_le, hdiagA_nonneg]
    nlinarith [hsquare, hmass_pos]

/-! ### Orthonormalization helper lemmas -/

section Helpers

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `S.L (A_a) * star (S.L (A_a)) = S.L (A_a * A_a)` for the self-adjoint outcomes of a
submeasurement. -/
theorem leftTensor_outcome_mul_conjTranspose_eq {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : SubMeas Outcome 𝔓) (a : Outcome) :
    S.L (A.outcome a) * star (S.L (A.outcome a)) = S.L (A.outcome a * A.outcome a) := by
  rw [S.leftTensor_conjTranspose, A.outcome_hermitian a, S.leftTensor_mul_leftTensor]

/-- The right-placement analogue of `leftTensor_outcome_mul_conjTranspose_eq`:
`star (S.R (B_a)) * S.R (B_a) = S.R (B_a * B_a)`. -/
theorem rightTensor_outcome_conjTranspose_mul_eq {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (B : SubMeas Outcome 𝔓) (a : Outcome) :
    star (S.R (B.outcome a)) * S.R (B.outcome a) = S.R (B.outcome a * B.outcome a) := by
  rw [S.rightTensor_conjTranspose, B.outcome_hermitian a,
    S.rightTensor_mul_rightTensor]

/-- Cauchy–Schwarz bound for the overlap `∑ₐ ⟨Ψ, (A_a ⊗ B_a) Ψ⟩`, in terms of the left and right
diagonal masses. -/
theorem abs_sum_ev_opTensor_le_sqrt_mul_sqrt {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A B : SubMeas Outcome 𝔓) :
    |∑ a, S.ev (S.opTensor (A.outcome a) (B.outcome a))| ≤
      Real.sqrt (∑ a, S.ev (S.L (A.outcome a * A.outcome a))) *
        Real.sqrt (∑ a, S.ev (S.R (B.outcome a * B.outcome a))) := by
  have h := Preliminaries.sum_ev_mul_le_sqrt S.toVecState
    (fun a => S.L (A.outcome a)) (fun a => S.R (B.outcome a))
  simp only [leftTensor_outcome_mul_conjTranspose_eq S A,
    rightTensor_outcome_conjTranspose_mul_eq S B] at h
  exact h

/-- The left diagonal mass `∑ₐ ⟨Ψ, S.L (A_a²) Ψ⟩` is nonnegative. -/
theorem sum_ev_leftTensor_outcome_sq_nonneg {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : SubMeas Outcome 𝔓) :
    0 ≤ ∑ a, S.ev (S.L (A.outcome a * A.outcome a)) :=
  Finset.sum_nonneg fun a _ =>
    S.ev_nonneg_of_psd _ <|
      S.leftTensor_nonneg (IsSelfAdjoint.mul_self_nonneg (A.outcome_hermitian a))

/-- The right diagonal mass `∑ₐ ⟨Ψ, S.R (B_a²) Ψ⟩` is nonnegative. -/
theorem sum_ev_rightTensor_outcome_sq_nonneg {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (B : SubMeas Outcome 𝔓) :
    0 ≤ ∑ a, S.ev (S.R (B.outcome a * B.outcome a)) :=
  Finset.sum_nonneg fun a _ =>
    S.ev_nonneg_of_psd _ <|
      S.rightTensor_nonneg (IsSelfAdjoint.mul_self_nonneg (B.outcome_hermitian a))

/-- The overlap `∑ₐ ⟨Ψ, (A_a ⊗ B_a) Ψ⟩` of two measurements is at most the total mass
`⟨Ψ, Ψ⟩`, since `B_a ≤ 1` and `A` is complete. -/
theorem sum_ev_opTensor_outcome_le_totalMass {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A B : Measurement Outcome 𝔓) :
    ∑ a, S.ev (S.opTensor (A.outcome a) (B.outcome a)) ≤ S.ev 1 :=
  calc ∑ a, S.ev (S.opTensor (A.outcome a) (B.outcome a))
      ≤ ∑ a, S.ev (S.L (A.outcome a)) := Finset.sum_le_sum fun a _ =>
        S.ev_mono _ _ (S.opTensor_le_leftTensor (A.outcome_pos a) (B.outcome_le_one a))
    _ = S.ev 1 := by
        rw [← S.ev_sum, ← map_sum S.L, A.sum_eq_total, A.total_eq_one, S.leftTensor_one]

/-- The common core of the two `qSSCDefect_*PlacedMeasurement_le_two_qBipartiteConsDefect`
lemmas: both diagonal masses are at least `1 − 2 · qBipartiteConsDefect`. -/
private theorem one_sub_two_qBipartiteConsDefect_le_diag {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A B : Measurement Outcome 𝔓) :
    1 - 2 * S.qBipartiteConsDefect A.toSubMeas B.toSubMeas ≤
        ∑ a, S.ev (S.L (A.outcome a * A.outcome a)) ∧
      1 - 2 * S.qBipartiteConsDefect A.toSubMeas B.toSubMeas ≤
        ∑ a, S.ev (S.R (B.outcome a * B.outcome a)) := by
  set diagA := ∑ a, S.ev (S.L (A.outcome a * A.outcome a))
  set diagB := ∑ a, S.ev (S.R (B.outcome a * B.outcome a))
  set overlap := ∑ a, S.ev (S.opTensor (A.outcome a) (B.outcome a)) with hoverlap
  have hdiagA0 : 0 ≤ diagA := sum_ev_leftTensor_outcome_sq_nonneg S A.toSubMeas
  have hdiagB0 : 0 ≤ diagB := sum_ev_rightTensor_outcome_sq_nonneg S B.toSubMeas
  have hdiagA1 : diagA ≤ 1 := by
    simpa only [SymModel.leftPlacedSubMeas_outcome, S.leftTensor_mul_leftTensor] using
      Preliminaries.subMeas_diagMass_le_one S.toVecState (S.leftPlacedSubMeas A.toSubMeas)
  have hdiagB1 : diagB ≤ 1 := by
    simpa only [SymModel.rightPlacedSubMeas_outcome, S.rightTensor_mul_rightTensor] using
      Preliminaries.subMeas_diagMass_le_one S.toVecState (S.rightPlacedSubMeas B.toSubMeas)
  have hoverlap1 : overlap ≤ 1 :=
    (sum_ev_opTensor_outcome_le_totalMass S A B).trans_eq S.ev_one_of_isNormalized
  have hdefect : S.qBipartiteConsDefect A.toSubMeas B.toSubMeas = 1 - overlap := by
    have htot : S.ev (S.opTensor A.total B.total) = 1 := by
      rw [A.total_eq_one, B.total_eq_one, SymModel.opTensor, S.leftTensor_one,
        S.rightTensor_one, mul_one, VecState.ev_one_of_isNormalized]
    change max 0 (S.ev (S.opTensor A.total B.total) - overlap) = 1 - overlap
    rw [htot, max_eq_right (sub_nonneg.2 hoverlap1)]
  have hsq : overlap ^ 2 ≤ diagA * diagB := by
    have h := abs_sum_ev_opTensor_le_sqrt_mul_sqrt S A.toSubMeas B.toSubMeas
    calc overlap ^ 2 = |overlap| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.sqrt diagA * Real.sqrt diagB) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = diagA * diagB := by rw [mul_pow, Real.sq_sqrt hdiagA0, Real.sq_sqrt hdiagB0]
  have hdefect0 := S.qBipartiteConsDefect_nonneg A.toSubMeas B.toSubMeas
  exact ⟨totalMass_sub_two_defect_le_diagA hdiagA0 hdefect0 hdefect hsq hdiagB1,
    totalMass_sub_two_defect_le_diagA hdiagB0 hdefect0 hdefect (by rwa [mul_comm]) hdiagA1⟩

/-- The consistency defect of `(A, B)` controls the strong self-consistency defect of the
left-placed `A`: `qSSCDefect (S.leftPlacedSubMeas A) ≤ 2 · qBipartiteConsDefect A B`. -/
theorem qSSCDefect_leftPlacedMeasurement_le_two_qBipartiteConsDefect {Outcome : Type*}
    [Fintype Outcome] (S : SymModel 𝔓 K) (A B : Measurement Outcome 𝔓) :
    S.qSSCDefect (S.leftPlacedSubMeas A.toSubMeas) ≤
      2 * S.qBipartiteConsDefect A.toSubMeas B.toSubMeas := by
  have h := (one_sub_two_qBipartiteConsDefect_le_diag S A B).1
  have h0 := S.qBipartiteConsDefect_nonneg A.toSubMeas B.toSubMeas
  simp only [VecState.qSSCDefect, SymModel.leftPlacedSubMeas_outcome,
    SymModel.leftPlacedSubMeas_total, A.total_eq_one, S.leftTensor_one,
    VecState.ev_one_of_isNormalized, S.leftTensor_mul_leftTensor]
  exact max_le (by linarith) (by linarith)

/-- The consistency defect of `(A, B)` controls the strong self-consistency defect of the
right-placed `B`: the right-register counterpart of
`qSSCDefect_leftPlacedMeasurement_le_two_qBipartiteConsDefect`, by the same Cauchy–Schwarz
calculation with the two diagonal masses interchanged. -/
theorem qSSCDefect_rightPlacedMeasurement_le_two_qBipartiteConsDefect {Outcome : Type*}
    [Fintype Outcome] (S : SymModel 𝔓 K) (A B : Measurement Outcome 𝔓) :
    S.qSSCDefect (S.rightPlacedSubMeas B.toSubMeas) ≤
      2 * S.qBipartiteConsDefect A.toSubMeas B.toSubMeas := by
  have h := (one_sub_two_qBipartiteConsDefect_le_diag S A B).2
  have h0 := S.qBipartiteConsDefect_nonneg A.toSubMeas B.toSubMeas
  simp only [VecState.qSSCDefect, SymModel.rightPlacedSubMeas_outcome,
    SymModel.rightPlacedSubMeas_total, B.total_eq_one, S.rightTensor_one,
    VecState.ev_one_of_isNormalized, S.rightTensor_mul_rightTensor]
  exact max_le (by linarith) (by linarith)

end Helpers

/-! ### Almost projectivity from strong self-consistency -/

section SameSpace

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A measurement whose strong self-consistency defect is at most `η` has idempotence defect
`∑ₐ ⟨Ψ, (A_a − A_a²) Ψ⟩` at most `η`. -/
theorem sourceAlmostProjective_of_ssc {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A : Measurement Outcome (K →L[ℂ] K)) (η : ℝ)
    (hssc : V.qSSCDefect A.toSubMeas ≤ η) :
    ∑ a, V.ev (A.outcome a - A.outcome a * A.outcome a) ≤ η := by
  simp only [V.ev_sub, Finset.sum_sub_distrib]
  rw [← V.ev_sum, A.sum_eq_total]
  exact (le_max_right _ _).trans hssc

/-- The source idempotence defect `∑ₐ ⟨Ψ, (A_a − A_a²) Ψ⟩` of a measurement is nonnegative. -/
theorem sourceAlmostProjective_nonneg {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A : Measurement Outcome (K →L[ℂ] K)) :
    0 ≤ ∑ a, V.ev (A.outcome a - A.outcome a * A.outcome a) :=
  Finset.sum_nonneg fun a _ => V.ev_nonneg_of_psd _ <|
    sub_nonneg.2 (sq_le_self (A.outcome_pos a) (A.outcome_le_one a))

end SameSpace

/-! ### Consistency implies almost projectivity -/

section Consistency

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The bipartite consistency defect of two measurements, read off a consistency relation at the
single question. -/
private theorem qBipartiteConsDefect_le_of_consRel {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A B : Measurement Outcome 𝔓) (ζ : ℝ)
    (hCons : S.ConsRel (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ) :
    S.qBipartiteConsDefect A.toSubMeas B.toSubMeas ≤ ζ := by
  have h := hCons.offDiagonalBound
  simpa [SymModel.bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using h

/-- A measurement with strong self-consistency defect at most `η ≥ 0` satisfies the conclusion
of the almost-projective step with error `η`. -/
private theorem almostProjMeasStatement_of_qSSCDefect_le {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (A : Measurement Outcome (K →L[ℂ] K)) (η : ℝ) (hη : 0 ≤ η)
    (hssc : V.qSSCDefect A.toSubMeas ≤ η) :
    AlmostProjMeasStatement V A η := by
  refine ⟨⟨?_⟩, ⟨?_⟩, sourceAlmostProjective_of_ssc V A η hssc⟩
  · rw [Preliminaries.constFamily_ssc_unit]
    exact hssc
  · rw [VecState.sddError_self]
    linarith

/-- **Consistency implies almost projective**: if `A` is `ζ`-consistent with `B`, then the
left-lifted `A` is `2ζ`-almost-projective. -/
theorem consistencyToAlmostProjective {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A B : Measurement Outcome 𝔓) (ζ : ℝ) :
    S.ConsRel (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B.toSubMeas) ζ →
      AlmostProjMeasStatement S.toVecState (S.leftLiftedMeasurement A)
        (consistencyToAlmostProjectiveError ζ) := by
  intro hCons
  have hζ := qBipartiteConsDefect_le_of_consRel S A B ζ hCons
  have h0 := S.qBipartiteConsDefect_nonneg A.toSubMeas B.toSubMeas
  refine almostProjMeasStatement_of_qSSCDefect_le _ _ _
    (by unfold consistencyToAlmostProjectiveError; linarith) ?_
  refine (qSSCDefect_leftPlacedMeasurement_le_two_qBipartiteConsDefect S A B).trans ?_
  unfold consistencyToAlmostProjectiveError
  linarith

/-- Right-register form of `consistencyToAlmostProjective`: if `A` and `B` are `ζ`-consistent,
then the right-lifted `B` is `2ζ`-almost-projective. -/
theorem consistencyToAlmostProjective_right {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A B : Measurement Outcome 𝔓) (ζ : ℝ) :
    S.ConsRel (uniformDistribution Unit) (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B.toSubMeas) ζ →
      AlmostProjMeasStatement S.toVecState (S.rightLiftedMeasurement B)
        (consistencyToAlmostProjectiveError ζ) := by
  intro hCons
  have hζ := qBipartiteConsDefect_le_of_consRel S A B ζ hCons
  have h0 := S.qBipartiteConsDefect_nonneg A.toSubMeas B.toSubMeas
  refine almostProjMeasStatement_of_qSSCDefect_le _ _ _
    (by unfold consistencyToAlmostProjectiveError; linarith) ?_
  refine (qSSCDefect_rightPlacedMeasurement_le_two_qBipartiteConsDefect S A B).trans ?_
  unfold consistencyToAlmostProjectiveError
  linarith

end Consistency

/-! ### The zero projective submeasurement -/

/-- The zero family is a projective submeasurement. This supplies trivial large-error branches
where the target error bound is already at least the universal `qSDD ≤ 1` estimate. -/
def zeroProjSubMeas {Outcome : Type*} [Fintype Outcome]
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R] :
    ProjSubMeas Outcome R where
  outcome _ := 0
  total := 0
  outcome_pos _ := le_rfl
  sum_eq_total := Fintype.sum_eq_zero _ fun _ => rfl
  total_le_one := zero_le_one
  proj _ := mul_zero 0

section Zero

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The zero projective submeasurement, placed on the first factor, is within unit `qSDD` of any
left-placed submeasurement. -/
theorem qSDD_leftPlaced_zeroProjSubMeas_le_one {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : SubMeas Outcome 𝔓) :
    S.qSDD (S.leftPlacedSubMeas A)
      (S.leftPlacedSubMeas (zeroProjSubMeas (Outcome := Outcome) (R := 𝔓)).toSubMeas) ≤ 1 := by
  refine le_of_eq_of_le (Finset.sum_congr rfl fun a _ => ?_)
    (Preliminaries.subMeas_diagMass_le_one S.toVecState (S.leftPlacedSubMeas A))
  change S.ev (star (S.L (A.outcome a) - S.L 0) * (S.L (A.outcome a) - S.L 0)) =
    S.ev (S.L (A.outcome a) * S.L (A.outcome a))
  rw [map_zero, sub_zero, S.leftTensor_conjTranspose, A.outcome_hermitian a]

/-- The zero projective submeasurement, placed on the second factor, is within unit `qSDD` of
any right-placed submeasurement. -/
theorem qSDD_rightPlaced_zeroProjSubMeas_le_one {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A : SubMeas Outcome 𝔓) :
    S.qSDD (S.rightPlacedSubMeas A)
      (S.rightPlacedSubMeas (zeroProjSubMeas (Outcome := Outcome) (R := 𝔓)).toSubMeas) ≤ 1 := by
  refine le_of_eq_of_le (Finset.sum_congr rfl fun a _ => ?_)
    (Preliminaries.subMeas_diagMass_le_one S.toVecState (S.rightPlacedSubMeas A))
  change S.ev (star (S.R (A.outcome a) - S.R 0) * (S.R (A.outcome a) - S.R 0)) =
    S.ev (S.R (A.outcome a) * S.R (A.outcome a))
  rw [map_zero, sub_zero, S.rightTensor_conjTranspose, A.outcome_hermitian a]

end Zero

end MIPRE.LIDT.Co.MakingMeasurementsProjective

end
