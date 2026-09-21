/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalNormalizer
import MIPRE.Foundations.Introspection.HidingRigidity

/-! # Conditional ideal replacement from an actual tested relation

The conditional approximation is derived from the acceptance probability and
concrete answer maps. It is not an additional rigidity premise.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

variable {H K I O Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- Replace the actual marginal in a tested conditional relation by its ideal
commuting prefix, with constant six on the test's conditional failure. -/
theorem conditional_coarse_ideal_of_test (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (M : POVM I H) (N : POVM O K)
    (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (f : Y → I → Z) (g : O → Y × Z) (test : I → O → Bool)
    (hM : IsPVM (fun i => (M.mats i).val)) (hN : IsPVM (fun o => (N.mats o).val))
    (hP : IsPVM P) (hQ : IsPVM Q) (hc : ∀ y i, Commute (Q y) (P i))
    {δ η ε : ℝ}
    (hfine : ∑ i, xSqNorm ψ (M.mats i).val (P i) ≤ ε)
    (hnorm : ∑ y, snorm ψ
      (bOp ((∑ z, ((N.map g).mats (y, z)).val) - Q y)) ^ 2 ≤ η)
    (hwin : 1 - δ ≤ ∑ i, ∑ o,
      (if test i o = true then (1 : ℝ) else 0) * bornProb ψ (M.mats i).val (N.mats o).val)
    (hcheck : ∀ i o, test i o = true → f (g o).1 i = (g o).2) :
    (∑ p : Y × Z, snorm ψ
      (bOp (((N.map g).mats p).val) - bOp (conditionalIdeal P Q f p)) ^ 2) ≤
      6 * δ + 3 * η + 3 * ε := by
  have hconditional := conditional_coarse_consistency ψ hψ M N hN f g test hwin hcheck
  have hmapped (y : Y) (z : Z) : ((M.map (f y)).mats z).val =
      fibSum (fun i => (M.mats i).val) (f y) z := POVM.map_mats (f y) M z
  have h := conditional_coarse_ideal_replacement ψ hψ
    (fun i => (M.mats i).val) P Q (fun p => ((N.map g).mats p).val) f
    hM hP hQ hc hfine hnorm
    (by simpa only [conditionalCoarseDistance, hmapped] using hconditional)
  linarith

end MIPRE.Introspection
