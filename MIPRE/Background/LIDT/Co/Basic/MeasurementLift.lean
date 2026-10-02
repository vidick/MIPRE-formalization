/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Basic/
MeasurementLift.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementFamilies

@[expose] public section

/-!
# Measurement lift infrastructure for the low individual degree test

Measurement-level tensor-factor lifts built from the submeasurement placement API: the
counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/MeasurementLift.lean` in the port of
`planning/c6b-plan.md` (milestone M0, section "Port conventions").

The vendored lifts are Kronecker placements, with completeness from `leftTensor_one`. Here a
measurement on the local algebra `𝔓` is placed on a factor by `Measurement.map` along the
⋆-homomorphism `S.L` or `S.R` of a symmetric model `S`
(`Co/Basic/SubMeasurementCore.lean`), whose completeness is `map_one`. As with
`S.leftPlacedSubMeas`, the lifts are `SymModel` declarations used with dot notation, the model
replacing the vendored named carriers `(ιA := ιA)`, `(ιB := ιB)`.

## New here

`leftLiftedMeasurement_toSubMeas`, `leftLiftedMeasurement_outcome` and their right
counterparts, the projection equations of the lifts (all `rfl`).

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

namespace MIPRE.LIDT.Co

namespace SymModel

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (S : SymModel 𝔓 K)

/-- Lift a measurement to the first tensor factor: each outcome `A_a` becomes `S.L A_a`. -/
noncomputable def leftLiftedMeasurement {α : Type*} [Fintype α] (A : Measurement α 𝔓) :
    Measurement α (K →L[ℂ] K) :=
  A.map S.L

/-- Lift a measurement to the second tensor factor: each outcome `A_a` becomes `S.R A_a`. -/
noncomputable def rightLiftedMeasurement {α : Type*} [Fintype α] (A : Measurement α 𝔓) :
    Measurement α (K →L[ℂ] K) :=
  A.map S.R

/-- The underlying submeasurement of a left-lifted measurement is the left placement. -/
@[simp] theorem leftLiftedMeasurement_toSubMeas {α : Type*} [Fintype α]
    (A : Measurement α 𝔓) :
    (S.leftLiftedMeasurement A).toSubMeas = S.leftPlacedSubMeas A.toSubMeas :=
  rfl

/-- Outcome operators of a left-lifted measurement are left placements. -/
@[simp] theorem leftLiftedMeasurement_outcome {α : Type*} [Fintype α]
    (A : Measurement α 𝔓) (a : α) :
    (S.leftLiftedMeasurement A).outcome a = S.L (A.outcome a) :=
  rfl

/-- The underlying submeasurement of a right-lifted measurement is the right placement. -/
@[simp] theorem rightLiftedMeasurement_toSubMeas {α : Type*} [Fintype α]
    (A : Measurement α 𝔓) :
    (S.rightLiftedMeasurement A).toSubMeas = S.rightPlacedSubMeas A.toSubMeas :=
  rfl

/-- Outcome operators of a right-lifted measurement are right placements. -/
@[simp] theorem rightLiftedMeasurement_outcome {α : Type*} [Fintype α]
    (A : Measurement α 𝔓) (a : α) :
    (S.rightLiftedMeasurement A).outcome a = S.R (A.outcome a) :=
  rfl

end SymModel

end MIPRE.LIDT.Co

end
