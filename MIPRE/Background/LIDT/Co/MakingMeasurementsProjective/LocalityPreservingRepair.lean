/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean, to the symmetric model
of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Statements
public import MIPRE.Background.LIDT.Co.MakingMeasurementsProjective.Projectivization
public import MIPRE.Background.LIDT.Co.Doubling.Orthonormalization
public import MIPRE.Background.Orthonormalization.FinitePairOrtho
public import MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair

@[expose] public section

/-!
# Section 5 — Locality-preserving projectivization repair

The repair step of the proof of `thm:orthonormalization`: a measurement of the local algebra whose
left placement is almost projective at the `2ζ` scale is close, with the paper's `84 ζ^{1/4}`
envelope, to a projective submeasurement of the same local algebra. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean`
in the port of `planning/c6b-plan.md` (milestone M8, section "Port conventions"), and the first
site at which the port calls the orthonormalization tier T1.

**A different proof.** The vendored proof passes to the reduced (marginal) density matrix of the
left factor and runs the finite-dimensional `Q/X/X̂/P` route there (spectral truncation, rank
reduction, a positive Gram completion), then transports the estimate back to left placements.
A vector state has no reduced density, and the route is legal only on finite spectrum, so here
the four repair theorems are proved from T1 instead
(`MIPRE.Orthonormalization.povm_orthogonalization_finitePair`), as Theorem G is
(`SymModel.orthonormalization_of_isFinitePair_sddRel`, `Co/Doubling/Orthonormalization.lean`):
`∑ₐ ‖L(Aₐ) Ψ‖² = 1 − ∑ₐ ⟨Ψ, L(Aₐ − Aₐ²) Ψ⟩ ≥ 1 − 2ζ`, hence `> 1 − 3 min(ζ, 1)`
(`Doubling.one_sub_three_mul_min_lt`), so T1 gives a projective measurement `Q` of the local
algebra with `∑ₐ ‖L(Aₐ − Qₐ) Ψ‖² < 27 min(ζ, 1) ≤ 84 ζ^{1/4}`
(`twentySeven_mul_min_le_orthonormalizationMainLemmaError`).

**Shape changes**, in each of the four repair theorems:
- the state `ψ : QuantumState (ιA × ιB)` (or `ι × ι`) is a symmetric model `S : SymModel 𝔓 K`,
  with both measurements local in `𝔓` (the vendored left/right lemmas allow two carriers; here
  they are narrowed to one, as milestone M3 did for `triangleSub_heterogeneous`);
- `hψ : ψ.IsNormalized` is dropped (`S.ev 1 = 1` is a theorem);
- `hS : S.toBipartite.IsFinitePair` and `hA : NoAbelianProj S.toBipartite.opsA`, the hypotheses
  of Theorem G and of T1, are added after `S`;
- `hζ : 0 ≤ ζ` becomes `hζ : 0 < ζ`, the strictness of T1's hypothesis;
  `leftLiftedProjectivizationRepair` had no `hζ` and gains `(hζ : 0 < ζ)` after `ζ`. The case
  `ζ = 0` does not follow from the strict tier and is not needed (`planning/c6b-plan.md`, §5).

The right-register form keeps the hypothesis on the first player's operators and is deduced from
the left one by the swap symmetry (`S.ev_L_eq_ev_R`,
`Preliminaries.qSDDCore_rightTensor_eq_leftTensor_of_permInv`). The bridges
`sddRel_of_leftPlaced_sddOpRel` and `sddRel_of_rightPlaced_sddOpRel` mention no marginal and are
ported; the vendored `ψ` is implicit in them, as is `S` here.

## New here

- `twentySeven_mul_min_le_orthonormalizationMainLemmaError`: `27 min(ζ, 1) ≤ 84 ζ^{1/4}` for
  `ζ ≥ 0`, the arithmetic of T1's error against the vendored envelope.

## Not ported

- `diagBlock`: a diagonal block of a matrix; the model has no reduced density matrix.
- `leftMarginalDensity`: the reduced density matrix of the first factor; no counterpart.
- `leftMarginalDensity_nonneg`: positivity of a reduced density matrix; no counterpart.
- `leftMarginalState`: the reduced state of the first factor; no counterpart.
- `leftTensor_eq_blockDiagonal_const`: a Kronecker identity of matrices; no counterpart.
- `trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock`: a matrix trace identity; no
  counterpart.
- `normalizedTrace_leftMarginalDensity_mul_eq`: the trace of a reduced density matrix; no
  counterpart.
- `leftMarginalState_isNormalized`: normalization of a reduced state; no counterpart.
- `leftMarginal_ev_eq`: expectations in a reduced state; no counterpart.
- `rightDiagBlock`: as `diagBlock`, for the second factor.
- `rightMarginalDensity`: as `leftMarginalDensity`, for the second factor.
- `rightMarginalDensity_nonneg`: as `leftMarginalDensity_nonneg`, for the second factor.
- `rightMarginalState`: as `leftMarginalState`, for the second factor.
- `trace_mul_rightTensor_eq_sum_trace_rightDiagBlock`: a matrix trace identity; no counterpart.
- `normalizedTrace_rightMarginalDensity_mul_eq`: as its left counterpart, for the second factor.
- `rightMarginalState_isNormalized`: as its left counterpart, for the second factor.
- `rightMarginal_ev_eq`: as its left counterpart, for the second factor.
- `matrix_eq_zero_of_rank_eq_zero`: matrix rank; only the dropped route used it.
- `sddOpRel_rightPlaced_of_ev_eq`: transport from a reduced state on one factor; only the dropped
  route used it.
- `projectivizationRepair_small_error_bound`: classical, imported.
- `roundingToProjectiveError_le_orthonormalizationMainLemmaError`: classical, imported.
- `one_le_orthonormalizationMainLemmaError_of_quarter_lt`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/orthonormalization.tex`, lines 534–1194
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MakingMeasurementsProjective

open MIPStarRE.LDT (avgOver uniformDistribution)
open MIPStarRE.LDT.MakingMeasurementsProjective (orthonormalizationMainLemmaError)
open MIPRE.Orthonormalization (povm_orthogonalization_finitePair)

/-- `27 min(ζ, 1) ≤ 84 ζ^{1/4}` for `ζ ≥ 0`: T1's error `9 · 3 min(ζ, 1)` lies under the
vendored repair envelope. -/
theorem twentySeven_mul_min_le_orthonormalizationMainLemmaError {ζ : ℝ} (hζ : 0 ≤ ζ) :
    27 * min ζ 1 ≤ orthonormalizationMainLemmaError ζ := by
  have hpow : min ζ 1 ≤ ζ ^ (1 / 4 : ℝ) := by
    rcases le_total ζ 1 with h | h
    · exact (min_le_left _ _).trans (Real.self_le_rpow_of_le_one hζ h (by norm_num))
    · exact (min_le_right _ _).trans (Real.one_le_rpow h (by norm_num))
  have h0 : 0 ≤ ζ ^ (1 / 4 : ℝ) := Real.rpow_nonneg hζ _
  change 27 * min ζ 1 ≤ 84 * ζ ^ (1 / 4 : ℝ)
  linarith

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A distance bound on left-placed raw families, whose second family has the outcomes of a
projective submeasurement `P`, is a distance bound on the left-placed submeasurements. -/
theorem sddRel_of_leftPlaced_sddOpRel {Outcome : Type*} [Fintype Outcome]
    {S : SymModel 𝔓 K} {A : Measurement Outcome 𝔓} {R : OpFamily Outcome 𝔓}
    {P : ProjSubMeas Outcome 𝔓} {δ : ℝ}
    (hR : ∀ a : Outcome, R.outcome a = P.outcome a)
    (hclose : S.SDDOpRel (uniformDistribution Unit)
      (fun _ => OpFamily.leftPlacedOpFamily S (A.toSubMeas : OpFamily Outcome 𝔓))
      (fun _ => OpFamily.leftPlacedOpFamily S R) δ) :
    S.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (S.leftPlacedSubMeas A.toSubMeas))
      (constSubMeasFamily (S.leftPlacedSubMeas P.toSubMeas)) δ := by
  refine ⟨le_of_eq_of_le ?_ hclose.squaredDistanceBound⟩
  change avgOver _ (fun _ => S.toVecState.qSDDCore (fun a => S.L (A.outcome a))
      (fun a => S.L (P.outcome a))) =
    avgOver _ (fun _ => S.toVecState.qSDDCore (fun a => S.L (A.outcome a))
      (fun a => S.L (R.outcome a)))
  simp only [hR]

/-- The right-placement counterpart of `sddRel_of_leftPlaced_sddOpRel`. -/
theorem sddRel_of_rightPlaced_sddOpRel {Outcome : Type*} [Fintype Outcome]
    {S : SymModel 𝔓 K} {B : Measurement Outcome 𝔓} {R : OpFamily Outcome 𝔓}
    {P : ProjSubMeas Outcome 𝔓} {δ : ℝ}
    (hR : ∀ a : Outcome, R.outcome a = P.outcome a)
    (hclose : S.SDDOpRel (uniformDistribution Unit)
      (fun _ => OpFamily.rightPlacedOpFamily S (B.toSubMeas : OpFamily Outcome 𝔓))
      (fun _ => OpFamily.rightPlacedOpFamily S R) δ) :
    S.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (S.rightPlacedSubMeas B.toSubMeas))
      (constSubMeasFamily (S.rightPlacedSubMeas P.toSubMeas)) δ := by
  refine ⟨le_of_eq_of_le ?_ hclose.squaredDistanceBound⟩
  change avgOver _ (fun _ => S.toVecState.qSDDCore (fun a => S.R (B.outcome a))
      (fun a => S.R (P.outcome a))) =
    avgOver _ (fun _ => S.toVecState.qSDDCore (fun a => S.R (B.outcome a))
      (fun a => S.R (R.outcome a)))
  simp only [hR]

/-- **Locality-preserving repair at the `2ζ` scale**: in a symmetric model whose bipartite reading
is a finite pair without abelian projections in its first player's operators, a measurement `A`
of the local algebra whose left placement has source idempotence defect at most `2ζ`, `ζ > 0`, is
within `orthonormalizationMainLemmaError ζ = 84 ζ^{1/4}` of a projective submeasurement of the
local algebra, in the left placements.

Proved from the orthonormalization tier T1 (`povm_orthogonalization_finitePair`) rather than the
vendored `Q/X/X̂/P` route; `hS`, `hA` are new and `hζ` is strict (module docstring). -/
theorem leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (hS : S.toBipartite.IsFinitePair) (hA : NoAbelianProj S.toBipartite.opsA)
    (A : Measurement Outcome 𝔓) (ζ : ℝ) (hζ : 0 < ζ)
    (hsource :
      ∑ a, S.ev
        ((S.leftLiftedMeasurement A).outcome a -
          (S.leftLiftedMeasurement A).outcome a * (S.leftLiftedMeasurement A).outcome a) ≤
        2 * ζ) :
    ∃ P : ProjSubMeas Outcome 𝔓,
      S.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (S.leftPlacedSubMeas A.toSubMeas))
        (constSubMeasFamily (S.leftPlacedSubMeas P.toSubMeas))
        (orthonormalizationMainLemmaError ζ) := by
  -- the left placement's norms: `∑ ‖L(Aₐ) Ψ‖² = 1 − (source defect) ≥ 1 − 2ζ`
  have hsq : ∀ a, ‖S.L (A.outcome a) S.Ψ‖ ^ 2 = S.ev (S.L (A.outcome a) * S.L (A.outcome a)) :=
    fun a => by
      rw [← VecState.ev_adjoint_self_eq_norm_sq, S.leftTensor_conjTranspose,
        A.outcome_hermitian a]
  have htot : ∑ a, S.ev (S.L (A.outcome a)) = 1 := by
    rw [← S.ev_sum, ← map_sum S.L, A.sum_eq_total, A.total_eq_one, S.leftTensor_one,
      VecState.ev_one_of_isNormalized]
  change ∑ a, S.ev (S.L (A.outcome a) - S.L (A.outcome a) * S.L (A.outcome a)) ≤ 2 * ζ
    at hsource
  simp only [VecState.ev_sub, Finset.sum_sub_distrib, htot, ← hsq] at hsource
  -- the tier at `ε = 3 min(ζ, 1)`
  have hlt := Doubling.one_sub_three_mul_min_lt (by linarith)
    (Finset.sum_nonneg fun a _ => sq_nonneg ‖S.L (A.outcome a) S.Ψ‖) hζ
  obtain ⟨Q, hQ, hQlt⟩ := povm_orthogonalization_finitePair S.toBipartite hS
    S.toBipartite_ψ_norm hA A.toPOVMIn _ hlt
  refine ⟨⟨(ProjMeas.ofIsPVMIn Q hQ).toSubMeas, hQ.idem⟩, ⟨?_⟩⟩
  have hQlt' : ∑ a, ‖S.L (A.outcome a - Q a) S.Ψ‖ ^ 2 < 9 * (3 * min ζ 1) := hQlt
  simp only [map_sub] at hQlt'
  have hmin := twentySeven_mul_min_le_orthonormalizationMainLemmaError hζ.le
  have havg : ∀ f : Unit → ℝ, avgOver (uniformDistribution Unit) f = f () := fun f => by
    simp [avgOver, uniformDistribution]
  rw [VecState.sddError, havg]
  simp only [VecState.qSDD, VecState.qSDDCore, constSubMeasFamily,
    SymModel.leftPlacedSubMeas_outcome, VecState.ev_adjoint_self_eq_norm_sq]
  exact hQlt'.le.trans (by linarith)

/-- **Right-register locality-preserving repair at the `2ζ` scale**: the counterpart of
`leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul` for the right placement,
under the same hypotheses on the first player's operators, deduced from it by the swap symmetry
of the model. -/
theorem rightPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (hS : S.toBipartite.IsFinitePair) (hA : NoAbelianProj S.toBipartite.opsA)
    (B : Measurement Outcome 𝔓) (ζ : ℝ) (hζ : 0 < ζ)
    (hsource :
      ∑ a, S.ev
        ((S.rightLiftedMeasurement B).outcome a -
          (S.rightLiftedMeasurement B).outcome a * (S.rightLiftedMeasurement B).outcome a) ≤
        2 * ζ) :
    ∃ P : ProjSubMeas Outcome 𝔓,
      S.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (S.rightPlacedSubMeas B.toSubMeas))
        (constSubMeasFamily (S.rightPlacedSubMeas P.toSubMeas))
        (orthonormalizationMainLemmaError ζ) := by
  have hleft : ∑ a, S.ev
      ((S.leftLiftedMeasurement B).outcome a -
        (S.leftLiftedMeasurement B).outcome a * (S.leftLiftedMeasurement B).outcome a) ≤
      2 * ζ := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun a _ => ?_) hsource
    change S.ev (S.L (B.outcome a) - S.L (B.outcome a) * S.L (B.outcome a)) =
      S.ev (S.R (B.outcome a) - S.R (B.outcome a) * S.R (B.outcome a))
    rw [S.leftTensor_mul_leftTensor, S.rightTensor_mul_rightTensor, S.leftTensor_sub,
      S.rightTensor_sub, S.ev_L_eq_ev_R]
  obtain ⟨P, ⟨hP⟩⟩ :=
    leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul S hS hA B ζ hζ hleft
  exact ⟨P, ⟨le_of_eq_of_le
    (congrArg (avgOver (uniformDistribution Unit)) (funext fun _ =>
      Preliminaries.qSDDCore_rightTensor_eq_leftTensor_of_permInv S B.outcome P.outcome)) hP⟩⟩

/-- **Locality-preserving repair, in the rounded-statement form**: the conclusion of
`leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul` as a
`RoundedProjMeasStatement` for the left-lifted measurement and the left lift of `P`. -/
theorem leftLiftedProjectivizationRepair_of_sourceAlmostProjective_two_mul
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (hS : S.toBipartite.IsFinitePair) (hA : NoAbelianProj S.toBipartite.opsA)
    (A : Measurement Outcome 𝔓) (ζ : ℝ) (hζ : 0 < ζ)
    (hsource :
      ∑ a, S.ev
        ((S.leftLiftedMeasurement A).outcome a -
          (S.leftLiftedMeasurement A).outcome a * (S.leftLiftedMeasurement A).outcome a) ≤
        2 * ζ) :
    ∃ P : ProjSubMeas Outcome 𝔓,
      RoundedProjMeasStatement S.toVecState (S.leftLiftedMeasurement A)
        (ProjSubMeas.liftLeft S P) (orthonormalizationMainLemmaError ζ) := by
  obtain ⟨P, hP⟩ :=
    leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul S hS hA A ζ hζ hsource
  exact ⟨P, ⟨hP⟩⟩

/-- **Locality-preserving projectivization repair** (`lem:locality-preserving-projectivization`):
from a source idempotence defect at most `ζ > 0` for the left-lifted measurement, a projective
submeasurement of the local algebra whose left lift is within `84 ζ^{1/4}`. -/
theorem leftLiftedProjectivizationRepair
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (hS : S.toBipartite.IsFinitePair) (hA : NoAbelianProj S.toBipartite.opsA)
    (A : Measurement Outcome 𝔓) (ζ : ℝ) (hζ : 0 < ζ)
    (hsource :
      ∑ a, S.ev
        ((S.leftLiftedMeasurement A).outcome a -
          (S.leftLiftedMeasurement A).outcome a * (S.leftLiftedMeasurement A).outcome a) ≤
        ζ) :
    ∃ P : ProjSubMeas Outcome 𝔓,
      RoundedProjMeasStatement S.toVecState (S.leftLiftedMeasurement A)
        (ProjSubMeas.liftLeft S P) (orthonormalizationMainLemmaError ζ) :=
  leftLiftedProjectivizationRepair_of_sourceAlmostProjective_two_mul S hS hA A ζ hζ
    (hsource.trans (by linarith))

end MIPRE.LIDT.Co.MakingMeasurementsProjective

end
