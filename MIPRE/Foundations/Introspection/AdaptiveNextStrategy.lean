/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveNextInvariant
import MIPRE.Foundations.Introspection.AdaptivePrefixStrategy

/-! # A returned strategy with its constructed next-prefix invariant

The selected measurement is identified with the next-prefix residual PVM,
including its actual coordinate carrier and the one shared new ancilla.
Any answer decoder may then be applied to the pair of next prefix and
retained answer. This composes the exact invariant closure with the existing
dimension-independent game-value estimate.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}

def nextPrefixJointPOVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k H A)
    (hD : ∀ y z, IsPVM (D y z)) : POVM ((ι → F) × A) ((ι → F) × (H × A)) :=
  (nextPrefixJoint_isPVM P hP k a₀ D hD).toPOVM

/-- After coordinate reassociation, the actual replacement measurement is
exactly the constructed next-prefix PVM with its answer retained. -/
theorem adaptiveReplacementPOVM_next (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k H A)
    (hD : ∀ y z, IsPVM (D y z)) :
    ((adaptiveReplacementPOVM P hP k D hD).reindex (Equiv.prodAssoc (ι → F) H A)).map
      (advanceStageAnswer P k) = nextPrefixJointPOVM P hP k a₀ D hD := by
  rw [adaptiveReplacementPOVM_reindex]
  apply POVM.ext'
  intro p
  rw [POVM.map_mats]
  change fibSum (adaptiveReplacementJointOp P hP k D) (advanceStageAnswer P k) p = _
  exact adaptiveReplacementJointOp_next_reassembly P hP k a₀ D p.1 p.2

variable {X Y Ans B : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype Ans] [DecidableEq Ans] [Fintype B] [DecidableEq B]

/-- The next residual measurement on the common decoded answer alphabet. -/
def nextPrefixDecodedPOVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k H A)
    (hD : ∀ y z, IsPVM (D y z)) (g : (ι → F) × A → Ans) (v : ι → F) :
    POVM Ans ((stageRemaining P (k + 1) v → F) × (H × A)) :=
  ((nextPrefixResidual_isPVM P hP k a₀ D hD v).toPOVM).map (fun a => g (v, a))

theorem nextPrefixDecodedPOVM_isPVM (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k H A)
    (hD : ∀ y z, IsPVM (D y z)) (g : (ι → F) × A → Ans) (v : ι → F) :
    IsPVM (fun a => ((nextPrefixDecodedPOVM P hP k a₀ D hD g v).mats a).val) :=
  isPVM_povm_map _ (nextPrefixResidual_isPVM P hP k a₀ D hD v) _

/-- Decoding the actual joint measurement gives exactly the sum of the
decoded residual measurements behind the next-prefix projectors. -/
theorem nextPrefixJointPOVM_map_mats (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (a₀ : A) (D : AdaptiveDilationFamily P k H A)
    (hD : ∀ y z, IsPVM (D y z)) (g : (ι → F) × A → Ans) (b : Ans) :
    (((nextPrefixJointPOVM P hP k a₀ D hD).map g).mats b).val =
      ∑ v, prefixResidualOp P (k + 1) v
        (((nextPrefixDecodedPOVM P hP k a₀ D hD g v).mats b).val) := by
  simp only [nextPrefixJointPOVM, nextPrefixDecodedPOVM, POVM.map_mats,
    IsPVM.toPOVM_mats, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [prefixResidualOp_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : g (v, a) = b
  · simp only [h, if_true]
  · simp only [h, if_false]
    ext i j
    simp [prefixResidualOp, registerOp_apply]

/-- Decoding the retained answer commutes with advancing the concrete
replacement into its next-prefix residual form. -/
theorem adaptiveReplacementPOVM_next_decode (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (a₀ : A)
    (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z))
    (g : (ι → F) × A → Ans) :
    ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => g (advanceStageAnswer P k p))).reindex (Equiv.prodAssoc (ι → F) H A) =
      (nextPrefixJointPOVM P hP k a₀ D hD).map g := by
  rw [POVM.map_reindex, ← POVM.map_map _ (advanceStageAnswer P k) g,
    adaptiveReplacementPOVM_next]

/-- The actual question-indexed strategy family has the constructed next
form at the selected question; the other questions are still supplied by
the existing registered replacement constructor. -/
theorem registeredReplacement_next_at (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (a₀ : A)
    (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z))
    (MA : X → POVM Ans ((ι → F) × H)) (q : X) (g : (ι → F) × A → Ans) :
    registeredReplacement MA q ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => g (advanceStageAnswer P k p))) q =
        (nextPrefixJointPOVM P hP k a₀ D hD).map g := by
  rw [registeredReplacement_at, adaptiveReplacementPOVM_next_decode]

/-- The selected measurement's entries satisfy the next induction invariant
with the constructed decoded residual PVM, on the actual remaining register. -/
theorem registeredReplacement_next_mats (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ) (a₀ : A)
    (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z))
    (MA : X → POVM Ans ((ι → F) × H)) (q : X) (g : (ι → F) × A → Ans) (b : Ans) :
    ((registeredReplacement MA q ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => g (advanceStageAnswer P k p))) q).mats b).val =
      ∑ v, prefixResidualOp P (k + 1) v
        (((nextPrefixDecodedPOVM P hP k a₀ D hD g v).mats b).val) := by
  rw [registeredReplacement_next_at P hP k a₀ D hD MA q g,
    nextPrefixJointPOVM_map_mats]

set_option backward.isDefEq.respectTransparency false in
/-- The same selected-measurement identity in the finite-dimensional
`TensorProductStrategy` packaging, with its explicit basis equivalence. -/
theorem adaptiveReplacementStrategy_next_at (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (G : Game X Y Ans B) (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1) (a₀ : A)
    (MA : X → POVM Ans ((ι → F) × H)) (MB : Y → POVM B ((ι → F) × K)) (q : X)
    (g : (ι → F) × A → Ans)
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val)
    (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z)) :
    (adaptiveReplacementStrategy P hP k G ξ hξ a₀ MA MB q
      (fun p => g (advanceStageAnswer P k p)) hMA hMB D hD).PA.toPOVM q =
      ((nextPrefixJointPOVM P hP k a₀ D hD).map g).reindex
        (Fintype.equivFin ((ι → F) × (H × A))) := by
  apply POVM.ext'
  intro a
  change Matrix.reindex (Fintype.equivFin ((ι → F) × (H × A)))
      (Fintype.equivFin ((ι → F) × (H × A)))
      ((registeredReplacement MA q ((adaptiveReplacementPOVM P hP k D hD).map
        (fun p => g (advanceStageAnswer P k p))) q).mats a).val =
    Matrix.reindex (Fintype.equivFin ((ι → F) × (H × A)))
      (Fintype.equivFin ((ι → F) × (H × A)))
      (((nextPrefixJointPOVM P hP k a₀ D hD).map g).mats a).val
  rw [registeredReplacement_next_at P hP k a₀ D hD MA q g]

/-- One quantitative adaptive step returns the next-prefix residual PVMs
and a legal strategy whose selected measurement has exactly that form.
The only structural input concerns the old selected measurement. -/
theorem exists_adaptive_next_strategy (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (G : Game X Y Ans B) (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1) (a₀ : A)
    (MA : X → POVM Ans ((ι → F) × H)) (MB : Y → POVM B ((ι → F) × K)) (q : X)
    (M : (y : ι → F) → POVM ((Fin (Fintype.card (P.factorOfPrefix k y)) → F) × A)
      ((stageRemaining P k y → F) × H))
    (hM : ∀ y, IsPVM (fun p => ((M y).mats p).val))
    (g : (ι → F) × A → Ans)
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val)
    (hselected : MA q = (adaptiveOldJointPOVM P hP k M hM).map
      (fun p => g (advanceStageAnswer P k p)))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmarg : prefixStageMarginalError P hP k ξ (fun y p => ((M y).mats p).val) ≤ ε)
    (hZ : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wZ) (fun _ => LinearMap.id) ≤ ε)
    (hX : prefixStageCommutatorError P hP k ξ (fun y p => ((M y).mats p).val)
      (fun _ => wX) (fun y => CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) ≤ ε) :
    ∃ (D : AdaptiveDilationFamily P k H A) (hD : ∀ y z, IsPVM (D y z)),
      (∀ v, IsPVM (nextPrefixResidual P hP k a₀ D v)) ∧
      (adaptiveReplacementStrategy P hP k G ξ hξ a₀ MA MB q
        (fun p => g (advanceStageAnswer P k p)) hMA hMB D hD).PA.toPOVM q =
        ((nextPrefixJointPOVM P hP k a₀ D hD).map g).reindex
          (Fintype.equivFin ((ι → F) × (H × A))) ∧
      |povmValue G (registerState (ι → F) ξ) MA MB -
        (adaptiveReplacementStrategy P hP k G ξ hξ a₀ MA MB q
          (fun p => g (advanceStageAnswer P k p)) hMA hMB D hD).value| ≤
        2 * Real.sqrt (2 * Real.sqrt (56 * Real.sqrt ε)) := by
  obtain ⟨D, hD, _, hv⟩ := exists_adaptive_replacement_strategy P hP k G ξ hξ a₀
    MA MB q M hM (fun p => g (advanceStageAnswer P k p)) hMA hMB hselected
    hε0 hε1 hmarg hZ hX
  exact ⟨D, hD, nextPrefixResidual_isPVM P hP k a₀ D hD,
    adaptiveReplacementStrategy_next_at P hP k G ξ hξ a₀ MA MB q g hMA hMB D hD, hv⟩

end MIPRE.Introspection
end
