/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.StrategyReplacementValue
import MIPRE.Foundations.Introspection.HidingInductionDilation
import MIPRE.Foundations.StrategyDilation
import MIPRE.Foundations.RegisterReindex

/-! # Replacing one measurement on a common ancillary extension

The new family is a function of the actual question. The selected question
uses the supplied projective dilation; every other measurement is the old
measurement tensored with identity. The state extension is independent of
the question and the opposite player is unchanged.
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {X Y A B C H K T : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]

/-- Actual replacement on one common enlarged register. -/
def replaceExtended (MA : X → POVM A H) (q : X) (R : POVM A (H × T)) :
    X → POVM A (H × T) := fun x => if x = q then R else (MA x).aOp

@[simp] theorem replaceExtended_at (MA : X → POVM A H) (q : X) (R : POVM A (H × T)) :
    replaceExtended MA q R q = R := by simp [replaceExtended]

theorem replaceExtended_other (MA : X → POVM A H) (q x : X) (R : POVM A (H × T))
    (hx : x ≠ q) : replaceExtended MA q R x = (MA x).aOp := by
  simp [replaceExtended, hx]

theorem replaceExtended_isPVM (MA : X → POVM A H) (q : X) (R : POVM A (H × T))
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hR : IsPVM fun a => (R.mats a).val) (x : X) :
    IsPVM (fun a => ((replaceExtended MA q R x).mats a).val) := by
  by_cases hx : x = q
  · simpa only [hx, replaceExtended_at] using hR
  · simpa only [replaceExtended_other MA q x R hx, POVM.aOp_mats] using (hMA x).aOp

/-- Adding an inert Alice ancilla preserves the whole game's value exactly. -/
theorem povmValue_extVecA (G : Game X Y A B) (ψ : H × K → ℂ) (a₀ : T)
    (MA : X → POVM A H) (MB : Y → POVM B K) :
    povmValue G (extVecA ψ a₀) (fun x => (MA x).aOp) MB = povmValue G ψ MA MB := by
  unfold povmValue condWin
  simp only [POVM.aOp_mats, bornProb_extVecA, compress_aOp]

/-- Unit normalization of the actual one-sided ancillary extension. -/
theorem extVecA_unit (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (a₀ : T) :
    star (extVecA ψ a₀) ⬝ᵥ extVecA ψ a₀ = 1 := by
  rw [dotProduct_star_self, norm_evec_extVecA, norm_evec_eq_one_of_unit hψ]
  norm_num

/-- Quantitative value preservation for the actual replacement family.
The fine outcomes may be relabelled by any function, including a constructor
in the common parsed-answer alphabet. -/
theorem replaceExtended_value (G : Game X Y A B) (ψ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (a₀ : T)
    (MA : X → POVM A H) (MB : Y → POVM B K)
    (q : X) (M : POVM C H) (R : POVM C (H × T)) (f : C → A)
    (hMA : MA q = M.map f) (hM : IsPVM fun c => (M.mats c).val)
    (hR : IsPVM fun c => (R.mats c).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val) {δ : ℝ}
    (hd : ∑ c, stateSqNorm (extVecA ψ a₀)
      (aOp (M.mats c).val - (R.mats c).val) ≤ δ) :
    |povmValue G ψ MA MB -
      povmValue G (extVecA ψ a₀) (replaceExtended MA q (R.map f)) MB| ≤ 2*Real.sqrt δ := by
  rw [← povmValue_extVecA G ψ a₀ MA MB]
  apply povmValue_stability_at G (extVecA ψ a₀) (by rwa [norm_evec_extVecA])
    (fun x => (MA x).aOp) (replaceExtended MA q (R.map f)) MB q M.aOp R f
  · rw [hMA, POVM.map_aOp]
  · exact replaceExtended_at MA q (R.map f)
  · intro x hx
    exact (replaceExtended_other MA q x (R.map f) hx).symm
  · exact hM.aOp
  · exact hR
  · exact hMB
  · exact hd

/-- The replacement is a concrete legal tensor-product strategy, with local
dimension multiplied by the chosen ancilla cardinality. -/
def replacementStrategy (G : Game X Y A B) (ψ : H × K → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (a₀ : T)
    (MA : X → POVM A H) (MB : Y → POVM B K)
    (q : X) (R : POVM A (H × T))
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val)
    (hR : IsPVM fun a => (R.mats a).val) : TensorProductStrategy G :=
  TensorProductStrategy.ofPVM G (extVecA ψ a₀) (extVecA_unit ψ hψ a₀)
    (replaceExtended MA q R) MB (replaceExtended_isPVM MA q R hMA hR) hMB

theorem replacementStrategy_value (G : Game X Y A B) (ψ : H × K → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (a₀ : T)
    (MA : X → POVM A H) (MB : Y → POVM B K)
    (q : X) (R : POVM A (H × T))
    (hMA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val)
    (hR : IsPVM fun a => (R.mats a).val) :
    (replacementStrategy G ψ hψ a₀ MA MB q R hMA hMB hR).value =
      povmValue G (extVecA ψ a₀) (replaceExtended MA q R) MB :=
  TensorProductStrategy.value_ofPVM _ _ _ _ _ _ _

end MIPRE.Introspection
end
