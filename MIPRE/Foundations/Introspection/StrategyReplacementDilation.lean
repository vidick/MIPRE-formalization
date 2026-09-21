/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.StrategyReplacementRegister

/-! # Conditional residual POVMs produce an actual replacement strategy

Naimark's construction uses the same fixed ancilla for every prefix. The
resulting residual PVMs are assembled with the unchanged prefix projectors,
inserted at the chosen question, and packaged as a legal strategy. The value
loss is `2 sqrt(2 sqrt(delta))`, independent of every outcome cardinality.
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {X Y A B C J I H K : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Conditional projectivization followed by actual strategy reassembly.
Neither the projectors nor the strategy are hypotheses: both are constructed
from the residual POVMs `Q`, and every prefix shares the fixed state `a₀`. -/
theorem exists_conditional_replacement_strategy
    (G : Game X Y A B) (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1) (a₀ : C)
    (MA : X → POVM A (I × H)) (MB : Y → POVM B (I × K)) (q : X)
    (M : POVM (J × C) (I × H)) (f : J × C → A)
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val)
    (hselected : MA q = M.map f) (hM : IsPVM fun c => (M.mats c).val)
    (Z : J → Matrix I I ℂ) (hZ : IsPVM Z) (Q : J → POVM C H) {δ : ℝ}
    (hd : ∑ p : J × C, stateSqNorm (registerState I ξ)
      ((M.mats p).val - Z p.1 ⊗ₖ ((Q p.1).mats p.2).val) ≤ δ) :
    ∃ (P : J → C → Matrix (H × C) (H × C) ℂ) (hP : ∀ j, IsPVM (P j)),
      (∀ j c, (ancillaEmbed H a₀)ᴴ * (P j c * ancillaEmbed H a₀) =
        ((Q j).mats c).val) ∧
      |povmValue G (registerState I ξ) MA MB -
        (registeredReplacementStrategy G ξ hξ a₀ MA MB q
          ((conditionalDilationOp_isPVM Z hZ P hP).toPOVM.map f) hMA hMB
          (isPVM_povm_map (conditionalDilationOp_isPVM Z hZ P hP).toPOVM
            (conditionalDilationOp_isPVM Z hZ P hP) f)).value| ≤
        2*Real.sqrt (2*Real.sqrt δ) := by
  obtain ⟨P, hP, hk, hjoint, _, hdist⟩ :=
    exists_conditional_projective_dilation (J := Unit) (registerState I ξ)
      (registerState_norm ξ (norm_evec_eq_one_of_unit hξ)) a₀
      (fun _ => 1) (fun _ => zero_le_one) (by simp)
      (fun _ => Z) (fun _ => hZ) (fun _ => Q)
      (fun _ p => (M.mats p).val) (fun _ => hM) (δ := δ) (by simpa using hd)
  refine ⟨P (), hP (), hk (), ?_⟩
  apply registeredReplacementStrategy_value_loss G ξ hξ a₀ MA MB q M
    (conditionalDilationOp_isPVM Z hZ (P ()) (hP ())).toPOVM f hMA hMB
    hselected hM (hjoint ())
  simpa only [Fintype.sum_unique, one_mul, IsPVM.toPOVM_mats] using hdist

end MIPRE.Introspection
end
