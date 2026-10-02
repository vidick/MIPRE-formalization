/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization/RestrictSome.lean, to the symmetric
model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.SubMeasurementCore

@[expose] public section

/-!
# Section 5 — restriction of completed projective submeasurements

The elementary order algebra used after applying the orthonormalization theorem to the option
completion of a submeasurement: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization/RestrictSome.lean`
in the port of `planning/c6b-plan.md` (milestone M8, section "Port conventions").

The restriction mentions no state and is generic over an ordered `⋆`-ring. It was written in
milestone M2 for Theorem G (`Co/Doubling/Orthonormalization.lean`) and lives here, its vendored
home. Unlike the vendored file, this one does not import `Statements.lean`: the restriction
needs only the submeasurement structures.

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MakingMeasurementsProjective

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
  {Outcome : Type*} [Fintype Outcome]

/-- **The outcomes `some a` of a projective submeasurement on `Option Outcome`**, a projective
submeasurement (the vendored `restrictSomeProjSubMeas`): the fresh outcome `none` is discarded. -/
def restrictSomeProjSubMeas (P : ProjSubMeas (Option Outcome) R) : ProjSubMeas Outcome R where
  outcome a := P.outcome (some a)
  total := ∑ a, P.outcome (some a)
  outcome_pos a := P.outcome_pos (some a)
  sum_eq_total := rfl
  total_le_one := ((le_add_of_nonneg_left (P.outcome_pos none)).trans_eq
    ((Fintype.sum_option P.outcome).symm.trans P.sum_eq_total)).trans P.total_le_one
  proj a := P.proj (some a)

end MIPRE.LIDT.Co.MakingMeasurementsProjective

end
