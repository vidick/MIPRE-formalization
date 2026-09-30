/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveInitialInvariant
public import MIPRE.Foundations.Introspection.AdaptiveDecodedInvariant

@[expose] public section

/-! # The structural invariant used by the actual Introspect induction

The invariant records a projective residual measurement on the actual
remaining register, its exact ambient reconstruction, and support of every
valid reported answer. Malformed answers remain part of the measurement.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the measurements are POVMs in
the matrices over the registers with entries in an algebra `𝒜`, the first player's algebra of the
auxiliary model, which grows by an ancilla from one stage to the next.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [StarProper 𝒜]

/-- The concrete prefix invariant, including the support needed to recover
the selected measurement after deterministic answer refinement. -/
structure IntroPrefixInvariant (P : CL.CLFun F ι ℓ) (k : ℕ)
    (N : POVMIn (Option ((ι → F) × A)) (Matrix (ι → F) (ι → F) 𝒜)) where
  residual : (y : ι → F) →
    POVMIn (Option ((ι → F) × A)) (Matrix (stageRemaining P k y → F) (stageRemaining P k y → F) 𝒜)
  projective : ∀ y, IsPVMIn (residual y).op
  form : ∀ a, N.op a = ∑ y, prefixResidualOp P k y ((residual y).op a)
  support : ∀ y x a, P.outputPrefix k x ≠ y → (residual y).op (some (x, a)) = 0

/-- Every projective full-answer measurement supplies the initial
invariant on its original auxiliary space. -/
def initialIntroPrefixInvariant (P : CL.CLFun F ι ℓ)
    (N : POVMIn (Option ((ι → F) × A)) (Matrix (ι → F) (ι → F) 𝒜))
    (hN : IsPVMIn N.op) : IntroPrefixInvariant P 0 N where
  residual := initialResidualPOVM P N
  projective := initialResidualPOVM_isPVM P N hN
  form := initialResidualPOVM_reassembly P N
  support := initialResidualPOVM_some_support P N

end MIPRE.Introspection
end

end
