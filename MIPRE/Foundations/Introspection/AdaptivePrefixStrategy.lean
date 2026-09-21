/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePrefixReplacement

/-! # A legal strategy after one adaptive product-form step

Mixing, one fixed residual ancilla, orthogonal prefix reassembly, and actual
question replacement are composed here. The output is a concrete
`TensorProductStrategy`; its state preserves the original EPR register and
all questions except the selected one retain their old measurements.
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}

/-- Returning from the extension ordering reveals exactly the prefix and
new Z-factor measurement constructed on the new auxiliary space. -/
theorem adaptiveReplacementPOVM_reindex (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z)) :
    (adaptiveReplacementPOVM P hP k D hD).reindex (Equiv.prodAssoc (ι → F) H A) =
      (adaptiveReplacementJointOp_isPVM P hP k D hD).toPOVM := by
  apply POVM.ext'
  intro p
  change registerOp (Equiv.prodAssoc (ι → F) H A).symm
    (registerOp (Equiv.prodAssoc (ι → F) H A) (adaptiveReplacementJointOp P hP k D p)) = _
  exact registerOp_inv _ _

variable {X Y Ans B : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype Ans] [DecidableEq Ans] [Fintype B] [DecidableEq B]

/-- The actual next strategy, including all unchanged questions. -/
def adaptiveReplacementStrategy (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ)
    (G : Game X Y Ans B) (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1) (a₀ : A)
    (MA : X → POVM Ans ((ι → F) × H)) (MB : Y → POVM B ((ι → F) × K)) (q : X)
    (f : AdaptiveStageAnswer P k A → Ans)
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val)
    (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z)) : TensorProductStrategy G :=
  registeredReplacementStrategy G ξ hξ a₀ MA MB q
    ((adaptiveReplacementPOVM P hP k D hD).map f) hMA hMB
    (isPVM_povm_map _ (adaptiveReplacementPOVM_isPVM P hP k D hD) f)

/-- **One complete adaptive replacement step.** The hypotheses are the three
full-carrier mixing errors and the old selected measurement's explicit
prefix form. The residual projectors and resulting legal strategy are
constructed, with a dimension-independent game-value bound. -/
theorem exists_adaptive_replacement_strategy (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (G : Game X Y Ans B) (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1) (a₀ : A)
    (MA : X → POVM Ans ((ι → F) × H)) (MB : Y → POVM B ((ι → F) × K)) (q : X)
    (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val))
    (f : AdaptiveStageAnswer P k A → Ans)
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val)
    (hselected : MA q = (adaptiveOldJointPOVM P hP k M hM).map f)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : prefixStageMarginalError P hP k ξ (fun y p => ((M y).mats p).val) ≤ ε)
    (hZ : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ ε)
    (hX : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) ≤ ε) :
    ∃ (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z)),
      (∑ p, stateSqNorm (extVecA (registerState (ι → F) ξ) a₀)
        (aOp ((adaptiveOldJointPOVM P hP k M hM).mats p).val -
          ((adaptiveReplacementPOVM P hP k D hD).mats p).val)) ≤
        2*Real.sqrt (56*Real.sqrt ε) ∧
      |povmValue G (registerState (ι → F) ξ) MA MB -
        (adaptiveReplacementStrategy P hP k G ξ hξ a₀ MA MB q f hMA hMB D hD).value| ≤
        2*Real.sqrt (2*Real.sqrt (56*Real.sqrt ε)) := by
  obtain ⟨D, hD, hd⟩ := exists_adaptive_prefix_dilation P hP k ξ
    (norm_evec_eq_one_of_unit hξ) a₀ M hM hε0 hε1 hmarg hZ hX
  have hglobal := adaptiveReplacement_distance P hP k ξ a₀ M hM D hD hd
  refine ⟨D, hD, hglobal, ?_⟩
  exact registeredReplacementStrategy_value_loss G ξ hξ a₀ MA MB q
    (adaptiveOldJointPOVM P hP k M hM) (adaptiveReplacementPOVM P hP k D hD) f hMA hMB
    hselected (adaptiveOldJointPOVM_isPVM P hP k M hM)
    (adaptiveReplacementPOVM_isPVM P hP k D hD) hglobal

end MIPRE.Introspection
end
