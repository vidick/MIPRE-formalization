/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.HidingRigidityIteration
public import MIPRE.Foundations.Introspection.HidingBaseRigidity
public import MIPRE.Foundations.Introspection.SamplingRigidity

@[expose] public section

/-! # Full hiding rigidity from the actual game and extracted Pauli bounds

The X/Hide-zero test supplies the induction base, and the Z/Sample/Introspect
tests supply every prefix estimate. Consequently the final theorem assumes
only the primitive extracted Pauli bounds, actual game success, and the
projectivity needed for the cross-party coarse-grainings. Its bound is uniform
over all hiding levels and includes malformed answer mass.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the extracted register state is
the register model `Ξ.reg (ι → F)` of a normalized auxiliary model `Ξ`, the measurements are POVMs
in its algebras, and the honest Pauli readouts enter as `smulKron 1 _`.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical Honest
set_option linter.unusedSectionVars false

/-- A single explicit Bob budget at every hiding level. -/
def hidingPauliBudget (ℓ : ℕ) (e δX ηZ : ℝ) : ℝ :=
  (6:ℝ)^ℓ * ((94 + 48*(ℓ:ℝ)^2)*e + 2*δX + 24*ηZ)

theorem hidingPauliBudget_eq_uniform (ℓ : ℕ) (e δX ηZ : ℝ) :
    hidingPauliBudget ℓ e δX ηZ =
      hidingUniformBudget ℓ e (4*ηZ+12*e) (4*e+2*δX) := by
  unfold hidingPauliBudget hidingUniformBudget hidingStepBudget
  ring

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- Complete hiding rigidity in the extracted register state. There is no
assumed hiding or prefix conclusion, and no symmetry premise on `DP`.
The two primitive Pauli errors are same-party distances: Alice X and Bob Z. -/
theorem hiding_register_rigidity_of_pauli [StarModule ℂ 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
    [StarProper ℬ]
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (Ξ : BipartiteModel 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    {ε δX ηZ : ℝ}
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (qX qZ : κ → ZMod 2)
    (hqX : ∀ z, (P X).eval z = qX) (hqZ : ∀ z, (P Z).eval z = qZ)
    (hPX : IsPVMIn (MA (QuestionType.pauli X, qX)).op)
    (hX : ∑ x, (Ξ.reg (ι → F)).stateSqNorm
      (((MA (QuestionType.pauli X, qX)).map (pauliProjection projectPauli)).op x -
        smulKron 1 (pauliXReadout x)) ≤ δX)
    (hZ : ∑ z, (Ξ.reg (ι → F)).snorm ((Ξ.reg (ι → F)).πB
      (((MB (QuestionType.pauli Z, qZ)).map (pauliProjection projectPauli)).op z -
        smulKron 1 (readout (some : (ι → F) → Option (ι → F)) z))) ^ 2 ≤ ηZ)
    (w : Bool) (hL : (L w).SupportedOn univ)
    (hS : IsPVMIn (MA (QuestionType.sample w, 0)).op)
    (hMA : ∀ j : Fin ℓ, IsPVMIn (MA (QuestionType.hide w j, 0)).op)
    (hMB : ∀ j : Fin ℓ, IsPVMIn (MB (QuestionType.hide w j, 0)).op)
    (j : Fin ℓ) :
    hidingBobError L w hL Ξ MB j ≤
      hidingPauliBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δX ηZ ∧
    hidingAliceError L w hL Ξ MA j ≤ 4*(TypeGraph.edges E X Z ℓ).card*ε +
      2*hidingPauliBudget ℓ ((TypeGraph.edges E X Z ℓ).card*ε) δX ηZ := by
  have hunit : ‖(Ξ.reg (ι → F)).ψ‖ = 1 := by rw [BipartiteModel.norm_reg_ψ, hΞ]
  have hε : 0 ≤ ε := by
    apply le_trans ?_ hfail
    rw [(Ξ.reg (ι → F)).one_sub_povmValue_eq]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg ((parsedGame E X Z P L projectPauli D DP).μ_nonneg x y)
        ((Ξ.reg (ι → F)).condFail_nonneg hunit x y)
  have hℓ : 0 < ℓ := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hbase := hiding_first_register_rigidity E X Z P L projectPauli D DP
    Ξ hΞ MA MB hfail w ⟨0,hℓ⟩ rfl hL qX hqX hPX hX
  have hintro : ∀ k : Fin ℓ, hidingIntroPrefixError L w Ξ MB k ≤
      4*ηZ+12*(TypeGraph.edges E X Z ℓ).card*ε := fun k =>
    introspect_prefix_register_rigidity_bob E X Z P L projectPauli D DP
      Ξ hΞ MA MB hfail qZ hqZ w hL hS hZ k.val
  have h := hiding_register_iteration_uniform E X Z P L projectPauli D DP
    Ξ hΞ MA MB hε hfail w hL hMA hMB hℓ hbase hintro j
  simpa only [hidingPauliBudget_eq_uniform, mul_assoc] using h

end MIPRE.Introspection.TypedEstimates

end

end
