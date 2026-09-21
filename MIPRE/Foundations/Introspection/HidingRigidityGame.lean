/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HidingRigidityIteration
import MIPRE.Foundations.Introspection.HidingBaseRigidity
import MIPRE.Foundations.Introspection.SamplingRigidity

/-! # Full hiding rigidity from the actual game and extracted Pauli bounds

The X/Hide-zero test supplies the induction base, and the Z/Sample/Introspect
tests supply every prefix estimate. Consequently the final theorem assumes
only the primitive extracted Pauli bounds, actual game success, and the
projectivity needed for the cross-party coarse-grainings. Its bound is uniform
over all hiding levels and includes malformed answer mass.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false

/-- A single explicit Bob budget at every hiding level. -/
def hidingPauliBudget (ℓ : ℕ) (e δX ηZ : ℝ) : ℝ :=
  (6:ℝ)^ℓ * ((94 + 48*(ℓ:ℝ)^2)*e + 2*δX + 24*ηZ)

theorem hidingPauliBudget_eq_uniform (ℓ : ℕ) (e δX ηZ : ℝ) :
    hidingPauliBudget ℓ e δX ηZ =
      hidingUniformBudget ℓ e (4*ηZ+12*e) (4*e+2*δX) := by
  unfold hidingPauliBudget hidingUniformBudget hidingStepBudget
  ring

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

/-- Complete hiding rigidity in the extracted register state. There is no
assumed hiding or prefix conclusion, and no symmetry premise on `DP`.
The two primitive Pauli errors are same-party distances: Alice X and Bob Z. -/
theorem hiding_register_rigidity_of_pauli
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × K))
    {ε δX ηZ : ℝ}
    (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP)
      (registerState (ι → F) ξ) MA MB ≤ ε)
    (qX qZ : κ → ZMod 2)
    (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
    (hPX : IsPVM (fun a => ((MA (QuestionType.pauli X, qX)).mats a).val))
    (hX : ∑ x, stateSqNorm (registerState (ι → F) ξ)
      ((((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).mats x).val -
        (aOp (pauliXReadout x) : Matrix ((ι → F) × H) _ ℂ)) ≤ δX)
    (hZ : ∑ z, snorm (registerState (ι → F) ξ) (bOp
      ((((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).mats z).val -
        (aOp (readout (some : (ι → F) → Option (ι → F)) z) :
          Matrix ((ι → F) × K) _ ℂ)))^2 ≤ ηZ)
    (w : Bool) (hL : (L w).SupportedOn univ)
    (hS : IsPVM (fun a => ((MA (QuestionType.sample w, 0)).mats a).val))
    (hMA : ∀ j : Fin ℓ, IsPVM (fun a => ((MA (QuestionType.hide w j, 0)).mats a).val))
    (hMB : ∀ j : Fin ℓ, IsPVM (fun b => ((MB (QuestionType.hide w j, 0)).mats b).val))
    (j : Fin ℓ) :
    hidingBobError L w hL ξ MB j ≤
      hidingPauliBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δX ηZ ∧
    hidingAliceError L w hL ξ MA j ≤ 4*(TypeGraph.edges E X Z ℓ).card*ε +
      2*hidingPauliBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δX ηZ := by
  have hunit : star (registerState (ι → F) ξ) ⬝ᵥ registerState (ι → F) ξ = 1 := by
    rw [dotProduct_star_self, registerState_norm ξ (norm_evec_eq_one_of_unit hξ)]
    norm_num
  have hε : 0 ≤ ε := by
    apply le_trans ?_ hfail
    rw [one_sub_povmValue_eq]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg ((parsedGame E X Z P L projectPauli D DP).μ_nonneg x y)
        (condFail_nonneg hunit x y)
  have hℓ : 0 < ℓ := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hbase := hiding_first_register_rigidity E X Z P L projectPauli D DP
    ξ hξ MA MB hfail w ⟨0,hℓ⟩ rfl hL qX hqX hPX hX
  have hintro : ∀ k : Fin ℓ, hidingIntroPrefixError L w ξ MB k ≤
      4*ηZ+12*(TypeGraph.edges E X Z ℓ).card*ε := fun k =>
    introspect_prefix_register_rigidity_bob E X Z P L projectPauli D DP
      ξ hξ MA MB hfail qZ hqZ w hL hS hZ k.val
  have h := hiding_register_iteration_uniform E X Z P L projectPauli D DP
    ξ hξ MA MB hε hfail w hL hMA hMB hℓ hbase hintro j
  simpa only [hidingPauliBudget_eq_uniform, mul_assoc] using h

end MIPRE.Introspection.TypedEstimates

end
