/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryDecisionProgram
import MIPRE.Foundations.Introspection.AuxiliaryPrefixGuardProgram

/-! # Auxiliary decision with both local prefix guards

The guards are applied to all hiding and Read endpoints, including consistency
loops. This is the executable counterpart of `PrefixGuard.guarded` and makes
its completeness and soundness transports available to the final verifier.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryDecision
open Cost Cost.PolyTimeFun AuxiliaryProgram
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]

/-- Validate the image condition for the left endpoint's required prefix. -/
def prefixGuard (U : ClockedUniversalMachine) : PolyTimeFun (Input P 7) Bool :=
  (AuxiliaryPrefixGuard.program U).comp (context.pair (width.pair (leftType.pair leftBits)))

/-- The complete auxiliary kernel, including the local image conditions. -/
def guarded (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) : PolyTimeFun (Input P 7) Bool :=
  andCheck (prefixGuard U) (andCheck ((prefixGuard U).comp swap) (check U X Z project))

theorem guarded_iff (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) (x : Input P 7) :
    guarded U X Z project x = true ↔
      prefixGuard U x = true ∧ prefixGuard U (swap x) = true ∧ check U X Z project x = true := by
  simp only [guarded, andCheck_iff, comp_apply]

/-- Guarding only removes accepting tuples. -/
theorem check_of_guarded (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) (x : Input P 7)
    (h : guarded U X Z project x = true) : check U X Z project x = true :=
  ((guarded_iff U X Z project x).mp h).2.2

end MIPRE.Introspection.AuxiliaryDecision
end
