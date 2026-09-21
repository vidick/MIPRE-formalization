/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingGame

/-! # Same-state soundness of finite-game detyping

Restricting to the fixed graph views gives a strategy for the typed game on
literally the same state. The only loss is conditioning on the valid graph
event. This proves the finite-game core of `types.tex`, `lem:detyping-verifiers`;
the program's answer cutoff and runtime remain separate obligations.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

/-- Conditioning a nonnegative quantity on valid graph seeds costs at most `16 ^ |T|`. -/
theorem valid_average_le (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (f : (Graph.Coord T → ZMod 2) → (ι → ZMod 2) → ℝ) (hf : ∀ g v, 0 ≤ f g v) :
    (∑ g ∈ Graph.validSeeds E, ∑ v, f g v) /
        ((Graph.validSeeds E).card * Fintype.card (ι → ZMod 2)) ≤
      (16 : ℝ) ^ Fintype.card T *
        ((∑ g, ∑ v, f g v) / ((16 : ℝ) ^ Fintype.card T * Fintype.card (ι → ZMod 2))) := by
  have hv : (0 : ℝ) < Fintype.card (ι → ZMod 2) := by exact_mod_cast Fintype.card_pos
  have he : (1 : ℝ) ≤ (Graph.edges E).card := by exact_mod_cast hne.card_pos
  have hp : (16 : ℝ) ^ Fintype.card T ≠ 0 := pow_ne_zero _ (by norm_num)
  have hnonneg : 0 ≤ ∑ g ∈ Graph.validSeeds E, ∑ v, f g v :=
    Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun v _ => hf g v
  have hsub : (∑ g ∈ Graph.validSeeds E, ∑ v, f g v) ≤ ∑ g, ∑ v, f g v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun g _ _ => Finset.sum_nonneg fun v _ => hf g v)
  rw [Graph.card_validSeeds]
  calc
    _ ≤ (∑ g ∈ Graph.validSeeds E, ∑ v, f g v) / Fintype.card (ι → ZMod 2) := by
      apply div_le_div_of_nonneg_left hnonneg hv
      nlinarith
    _ ≤ (∑ g, ∑ v, f g v) / Fintype.card (ι → ZMod 2) :=
      div_le_div_of_nonneg_right hsub hv.le
    _ = _ := by field_simp

/-- Exact identification of the restricted strategy's failure with conditional detyped failure. -/
theorem restrict_failure_eq {A B : Type*} [Fintype A] [Fintype B] {ℓ : ℕ}
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (game E P D)) :
    1 - (restrict E hne P D S).value =
      (∑ g ∈ Graph.validSeeds E, ∑ v : ι → ZMod 2,
        S.failAt ((presentation E false (P false)).eval (Sum.elim g v))
          ((presentation E true (P true)).eval (Sum.elim g v))) /
        ((Graph.validSeeds E).card * Fintype.card (ι → ZMod 2)) := by
  rw [typed_failure, conditional_average E hE P hP hℓ]
  congr 1
  apply Finset.sum_congr rfl
  intro uv huv
  apply Finset.sum_congr rfl
  intro v _
  exact restrict_failAt E hne P D S _ _ (Finset.mem_filter.mp huv).2

/-- The finite-game detyping reduction, with the source's explicit soundness factor. -/
theorem restrict_failure_le {A B : Type*} [Fintype A] [Fintype B] {ℓ : ℕ}
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (game E P D)) :
    1 - (restrict E hne P D S).value ≤ (16 : ℝ) ^ Fintype.card T * (1 - S.value) := by
  rw [restrict_failure_eq E hE hne P hP hℓ D S, failure E P D S]
  exact valid_average_le E hne _ (fun _ _ => S.failAt_nonneg _ _)

/-- A near-perfect detyped strategy yields the claimed same-state typed strategy. -/
theorem restrict_value_ge {A B : Type*} [Fintype A] [Fintype B] {ℓ : ℕ}
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (game E P D))
    {ε : ℝ} (hS : 1 - ε ≤ S.value) :
    1 - (16 : ℝ) ^ Fintype.card T * ε ≤ (restrict E hne P D S).value := by
  have h := restrict_failure_le E hE hne P hP hℓ D S
  have hp : 0 ≤ (16 : ℝ) ^ Fintype.card T := pow_nonneg (by norm_num) _
  nlinarith

end MIPRE.CL.Detyping
