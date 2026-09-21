/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.StrategyReplacement

/-! # Reassembly in the original EPR-register ordering

The added register belongs to Alice's auxiliary space. The shared state is
exactly the original EPR factor tensored with that extended auxiliary state.
These definitions construct the actual strategy on finite registers and
preserve all nonselected measurements under the displayed reassociation.
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {X Y A B C I H K T : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
  [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]

theorem povm_reindex_refl (M : POVM A H) : M.reindex (Equiv.refl H) = M :=
  POVM.ext' fun _ => rfl

/-- Reassociation places the fresh fixed ancilla entirely in the auxiliary
state and leaves the EPR factor literally unchanged. -/
theorem reindex_extVecA_registerState (ξ : H × K → ℂ) (a₀ : T) :
    reindexVec (Equiv.prodAssoc I H T) (Equiv.refl (I × K))
      (extVecA (registerState I ξ) a₀) = registerState I (extVecA ξ a₀) := by
  rw [extVecA_registerState]
  funext p
  simp only [reindexVec, Function.comp_apply, Equiv.apply_symm_apply]

/-- The new actual question-indexed family in the original register-first
ordering. -/
def registeredReplacement (MA : X → POVM A (I × H)) (q : X)
    (R : POVM A ((I × H) × T)) : X → POVM A (I × (H × T)) :=
  fun x => (replaceExtended MA q R x).reindex (Equiv.prodAssoc I H T)

@[simp] theorem registeredReplacement_at (MA : X → POVM A (I × H)) (q : X)
    (R : POVM A ((I × H) × T)) :
    registeredReplacement MA q R q = R.reindex (Equiv.prodAssoc I H T) := by
  simp only [registeredReplacement, replaceExtended_at]

theorem registeredReplacement_other (MA : X → POVM A (I × H)) (q x : X)
    (R : POVM A ((I × H) × T)) (hx : x ≠ q) :
    registeredReplacement MA q R x = ((MA x).aOp).reindex (Equiv.prodAssoc I H T) := by
  simp only [registeredReplacement, replaceExtended_other MA q x R hx]

theorem registeredReplacement_isPVM (MA : X → POVM A (I × H)) (q : X)
    (R : POVM A ((I × H) × T))
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hR : IsPVM fun a => (R.mats a).val) (x : X) :
    IsPVM (fun a => ((registeredReplacement MA q R x).mats a).val) :=
  registerOp_isPVM (Equiv.prodAssoc I H T).symm (replaceExtended_isPVM MA q R hMA hR x)

/-- The registered replacement and its unreassociated version have exactly
the same value, for every game. -/
theorem registeredReplacement_value_eq (G : Game X Y A B) (ξ : H × K → ℂ) (a₀ : T)
    (MA : X → POVM A (I × H)) (MB : Y → POVM B (I × K)) (q : X)
    (R : POVM A ((I × H) × T)) :
    povmValue G (registerState I (extVecA ξ a₀)) (registeredReplacement MA q R) MB =
      povmValue G (extVecA (registerState I ξ) a₀) (replaceExtended MA q R) MB := by
  have h := povmValue_reindex (Equiv.prodAssoc I H T) (Equiv.refl (I × K)) G
    (extVecA (registerState I ξ) a₀) (replaceExtended MA q R) MB
  change povmValue G (registerState I (extVecA ξ a₀))
    (fun x => (replaceExtended MA q R x).reindex (Equiv.prodAssoc I H T)) MB = _
  simpa only [reindex_extVecA_registerState, povm_reindex_refl] using h

variable [Nonempty I]

/-- The fixed auxiliary extension is normalized, hence gives the actual
normalized EPR-plus-auxiliary state of the next strategy. -/
theorem registerState_extVecA_unit (ξ : H × K → ℂ) (hξ : star ξ ⬝ᵥ ξ = 1) (a₀ : T) :
    star (registerState I (extVecA ξ a₀)) ⬝ᵥ registerState I (extVecA ξ a₀) = 1 := by
  rw [dotProduct_star_self, registerState_norm _ (by
    rw [norm_evec_extVecA]; exact norm_evec_eq_one_of_unit hξ)]
  norm_num

/-- A concrete legal strategy on the new register state. -/
def registeredReplacementStrategy (G : Game X Y A B) (ξ : H × K → ℂ)
    (hξ : star ξ ⬝ᵥ ξ = 1) (a₀ : T)
    (MA : X → POVM A (I × H)) (MB : Y → POVM B (I × K)) (q : X)
    (R : POVM A ((I × H) × T))
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val)
    (hR : IsPVM fun a => (R.mats a).val) : TensorProductStrategy G :=
  TensorProductStrategy.ofPVM G (registerState I (extVecA ξ a₀))
    (registerState_extVecA_unit ξ hξ a₀) (registeredReplacement MA q R) MB
    (registeredReplacement_isPVM MA q R hMA hR) hMB

theorem registeredReplacementStrategy_value (G : Game X Y A B) (ξ : H × K → ℂ)
    (hξ : star ξ ⬝ᵥ ξ = 1) (a₀ : T)
    (MA : X → POVM A (I × H)) (MB : Y → POVM B (I × K)) (q : X)
    (R : POVM A ((I × H) × T))
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val)
    (hR : IsPVM fun a => (R.mats a).val) :
    (registeredReplacementStrategy G ξ hξ a₀ MA MB q R hMA hMB hR).value =
      povmValue G (extVecA (registerState I ξ) a₀) (replaceExtended MA q R) MB := by
  rw [registeredReplacementStrategy, TensorProductStrategy.value_ofPVM,
    registeredReplacement_value_eq]

/-- Quantitative value preservation of the actual registered strategy,
including its finite-dimensional packaging. -/
theorem registeredReplacementStrategy_value_loss (G : Game X Y A B) (ξ : H × K → ℂ)
    (hξ : star ξ ⬝ᵥ ξ = 1) (a₀ : T)
    (MA : X → POVM A (I × H)) (MB : Y → POVM B (I × K)) (q : X)
    (M : POVM C (I × H)) (R : POVM C ((I × H) × T)) (f : C → A)
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val)
    (hselected : MA q = M.map f) (hM : IsPVM fun c => (M.mats c).val)
    (hR : IsPVM fun c => (R.mats c).val) {δ : ℝ}
    (hd : ∑ c, stateSqNorm (extVecA (registerState I ξ) a₀)
      (aOp (M.mats c).val - (R.mats c).val) ≤ δ) :
    |povmValue G (registerState I ξ) MA MB -
      (registeredReplacementStrategy G ξ hξ a₀ MA MB q (R.map f) hMA hMB
        (isPVM_povm_map R hR f)).value| ≤ 2*Real.sqrt δ := by
  rw [registeredReplacementStrategy_value]
  exact replaceExtended_value G (registerState I ξ)
    (registerState_norm ξ (norm_evec_eq_one_of_unit hξ)) a₀ MA MB q M R f
    hselected hM hR hMB hd

end MIPRE.Introspection
end
