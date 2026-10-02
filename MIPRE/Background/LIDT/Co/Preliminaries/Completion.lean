/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/Completion.lean, to the symmetric model of `planning/c6b-plan.md`;
not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichPrep.Core

@[expose] public section

/-!
# Preliminary completion lemmas

Structural completion helpers that stay close to `completeAtOutcome` while
keeping only the light projectivity dependencies from
`SwitchSandwichPrep/Core.lean`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Completion.lean` in the port of
`planning/c6b-plan.md` (milestone M3, section "Port conventions").

The vendored declarations are about matrices `Op ι` and mention no state; here they are stated
for any C*-algebra `R` with its order (local operators in `𝔓`, joint ones in `K →L[ℂ] K`), the
setting of the projective lemmas `ProjSubMeas.outcome_mul_total_eq_outcome` and
`ProjSubMeas.total_proj` (`Co/Basic/SubMeasurementCore.lean`). The self-adjointness of a
positive element is `IsSelfAdjoint.of_nonneg`, in place of the vendored positive
semidefiniteness of matrices.

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

variable {R : Type*} [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]

/-- Completing a projective submeasurement at a distinguished outcome preserves
projectivity. The residual effect `1 - P.total` is a projection orthogonal to
`P.outcome a0`, so the completed effect remains idempotent. -/
noncomputable def completeAtOutcomeProj {Outcome : Type*} [Fintype Outcome]
    (P : ProjSubMeas Outcome R) (a0 : Outcome) : ProjMeas Outcome R where
  toMeasurement := completeAtOutcome P.toSubMeas a0
  proj a := by
    by_cases ha : a = a0
    · subst a
      have hPa_star : IsStarProjection (P.outcome a0) :=
        isStarProjection_iff'.2 ⟨P.proj a0, P.outcome_hermitian a0⟩
      have hT_star : IsStarProjection P.total :=
        isStarProjection_iff'.2
          ⟨projSubMeas_total_proj P, (IsSelfAdjoint.of_nonneg P.toSubMeas.total_nonneg).star_eq⟩
      have hPaR : P.outcome a0 * (1 - P.total) = 0 := by
        rw [mul_sub, mul_one, projSubMeas_outcome_mul_total_eq_outcome, sub_self]
      simpa [completeAtOutcome] using
        (hPa_star.add hT_star.one_sub hPaR).isIdempotentElem.eq
    · simpa [completeAtOutcome, ha] using P.proj a

/-- The underlying measurement of `completeAtOutcomeProj P a0` is `completeAtOutcome`. -/
@[simp] theorem completeAtOutcomeProj_toMeasurement {Outcome : Type*} [Fintype Outcome]
    (P : ProjSubMeas Outcome R) (a0 : Outcome) :
    (completeAtOutcomeProj P a0).toMeasurement = completeAtOutcome P.toSubMeas a0 :=
  rfl

/-- The underlying submeasurement of `completeAtOutcomeProj P a0` is that of
`completeAtOutcome`. -/
@[simp] theorem completeAtOutcomeProj_toSubMeas {Outcome : Type*} [Fintype Outcome]
    (P : ProjSubMeas Outcome R) (a0 : Outcome) :
    (completeAtOutcomeProj P a0).toSubMeas = (completeAtOutcome P.toSubMeas a0).toSubMeas :=
  rfl

end MIPRE.LIDT.Co.Preliminaries

end
