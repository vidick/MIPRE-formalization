/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveInitialInvariant
import MIPRE.Foundations.Introspection.AdaptiveDecodedInvariant

/-! # The structural invariant used by the actual Introspect induction

The invariant records a projective residual measurement on the actual
remaining register, its exact ambient reconstruction, and support of every
valid reported answer. Malformed answers remain part of the measurement.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {F ι A H : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype H] [DecidableEq H] {ℓ : ℕ}

/-- The concrete prefix invariant, including the support needed to recover
the selected measurement after deterministic answer refinement. -/
structure IntroPrefixInvariant (P : CL.CLFun F ι ℓ) (k : ℕ)
    (N : POVM (Option ((ι → F) × A)) ((ι → F) × H)) where
  residual : (y : ι → F) →
    POVM (Option ((ι → F) × A)) ((stageRemaining P k y → F) × H)
  projective : ∀ y, IsPVM (fun a => ((residual y).mats a).val)
  form : ∀ a, (N.mats a).val =
    ∑ y, prefixResidualOp P k y ((residual y).mats a).val
  support : ∀ y x a, P.outputPrefix k x ≠ y →
    ((residual y).mats (some (x, a))).val = 0

/-- Every projective full-answer measurement supplies the initial
invariant on its original auxiliary space. -/
def initialIntroPrefixInvariant (P : CL.CLFun F ι ℓ)
    (N : POVM (Option ((ι → F) × A)) ((ι → F) × H))
    (hN : IsPVM (fun a => (N.mats a).val)) : IntroPrefixInvariant P 0 N where
  residual := initialResidualPOVM P N
  projective := initialResidualPOVM_isPVM P N hN
  form := initialResidualPOVM_reassembly P N
  support := initialResidualPOVM_some_support P N

end MIPRE.Introspection
end
