/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization/RestrictSome.lean
-/
import MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.Statements

-- Vendoring compile fix (Lean v4.33): the vendored tree is built with the pre-v4.33
-- transparency behaviour (`backward.isDefEq.respectTransparency false`), the option
-- Mathlib sets on declarations affected by Lean v4.33's check; see README.md.
set_option backward.isDefEq.respectTransparency false

/-!
# Section 5 — restriction of completed projective submeasurements

This file contains the elementary order algebra used after applying the
orthonormalization theorem to the option completion of a submeasurement.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-- Discard the fresh `none` outcome from an option-indexed projective
submeasurement. The remaining `some a` outcomes still form a projective
submeasurement. -/
noncomputable def restrictSomeProjSubMeas {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas (Option Outcome) ι) :
    ProjSubMeas Outcome ι where
  toSubMeas :=
    { outcome := fun a => P.outcome (some a)
      total := ∑ a : Outcome, P.outcome (some a)
      outcome_pos := fun a => P.outcome_pos (some a)
      sum_eq_total := rfl
      total_le_one :=
        ((le_add_of_nonneg_left (P.outcome_pos none)).trans_eq
          ((Fintype.sum_option P.outcome).symm.trans P.sum_eq_total)).trans P.total_le_one }
  proj := fun a => by simpa using P.proj (some a)

end MIPStarRE.LDT.MakingMeasurementsProjective
