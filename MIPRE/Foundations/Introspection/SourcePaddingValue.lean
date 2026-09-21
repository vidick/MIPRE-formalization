/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SourcePadding

/-! # Removing padding from arbitrary source-game strategies

Canonical zero-extension of questions pulls every padded strategy back with
exactly its state, dimensions, and value. The unused seed coordinates average
out uniformly; this is not restricted to perfect strategies or PCC strategies.
-/

noncomputable section
namespace MIPRE.Introspection.SourcePadding
open Matrix Finset Classical
set_option linter.unusedSectionVars false

variable {F I J A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  {ℓ : ℕ} (e : I ↪ J)

def seedSplit : (J → F) ≃ ((I → F) × ({j : J // j ∉ Set.range e} → F)) where
  toFun x := (CL.pull e x, fun j => x j.val)
  invFun p j := if h : j ∈ Set.range e then p.1 h.choose else p.2 ⟨j,h⟩
  left_inv x := by
    funext j
    dsimp only
    split_ifs with h
    · exact congrArg x h.choose_spec
    · rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      have h : e i ∈ Set.range e := ⟨i,rfl⟩
      simp only [CL.pull, dif_pos h]
      exact congrArg p.1 (e.injective h.choose_spec)
    · funext j
      simp only [dif_neg j.property]

/-- Restricting a uniform seed to an injected set of coordinates is uniform. -/
theorem average_pull (f : (I → F) → ℝ) :
    (∑ x : J → F, f (CL.pull e x)) / Fintype.card (J → F) =
      (∑ y : I → F, f y) / Fintype.card (I → F) := by
  have hs := Equiv.sum_comp (seedSplit (F := F) e) (fun p => f p.1)
  change (∑ x : J → F, f (CL.pull e x)) =
    ∑ p : (I → F) × ({j : J // j ∉ Set.range e} → F), f p.1 at hs
  rw [hs, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  rw [Fintype.card_congr (seedSplit (F := F) e), Fintype.card_prod, Nat.cast_mul]
  have hc : (Fintype.card ({j : J // j ∉ Set.range e} → F) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

variable (L : Bool → CL.CLFun F I ℓ) (D : (I → F) → (I → F) → A → A → Bool)

/-- Ask the padded strategy the canonical extension of the original question. -/
def restrictStrategy (S : TensorProductStrategy (Honest.sourceGame (family e L) (decider e D))) :
    TensorProductStrategy (Honest.sourceGame L D) :=
  S.relabel _ (CL.push e) (CL.push e) (Equiv.refl A) (Equiv.refl A)

theorem restrictStrategy_state
    (S : TensorProductStrategy (Honest.sourceGame (family e L) (decider e D))) :
    (restrictStrategy e L D S).ψ = S.ψ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem restrictStrategy_succAt
    (S : TensorProductStrategy (Honest.sourceGame (family e L) (decider e D)))
    (x y : I → F) :
    (restrictStrategy e L D S).succAt x y = S.succAt (CL.push e x) (CL.push e y) := by
  unfold TensorProductStrategy.succAt TensorProductStrategy.born
  simp only [restrictStrategy, TensorProductStrategy.relabel, ProjectiveMeasurement.reindex_M,
    Equiv.refl_apply, Honest.sourceGame, SampledGame.game, decider, CL.pull_push]

set_option backward.isDefEq.respectTransparency false in
theorem restrictStrategy_value
    (S : TensorProductStrategy (Honest.sourceGame (family e L) (decider e D))) :
    (restrictStrategy e L D S).value = S.value := by
  rw [TensorProductStrategy.value_eq_sum_succAt, TensorProductStrategy.value_eq_sum_succAt]
  change (∑ x, ∑ y, SampledGame.dist (L false).eval (L true).eval x y *
    (restrictStrategy e L D S).succAt x y) =
    ∑ x, ∑ y, SampledGame.dist (family e L false).eval (family e L true).eval x y * S.succAt x y
  rw [SampledGame.sum_dist_mul, SampledGame.sum_dist_mul]
  simp_rw [restrictStrategy_succAt, family, CL.CLFun.eval_embed]
  exact (average_pull e (fun y => S.succAt (CL.push e ((L false).eval y))
    (CL.push e ((L true).eval y)))).symm

/-- Soundness can return from the padded source game to the original game
without losing any value. -/
theorem quantumValue_le :
    quantumValue (Honest.sourceGame (family e L) (decider e D)) ≤
      quantumValue (Honest.sourceGame L D) := by
  refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
  have hh := le_ciSup (TensorProductStrategy.bddAbove_range_value (Honest.sourceGame L D))
    (restrictStrategy e L D S)
  rwa [restrictStrategy_value] at hh

/-- Filling the spectator coordinates inside the existing first factor also
has no soundness cost, since its entire source game is identical. -/
theorem quantumValue_depthFamily_le (hℓ : 0 < ℓ) (hL : ∀ w, (L w).SupportedOn univ) :
    quantumValue (Honest.sourceGame (depthFamily e L) (decider e D)) ≤
      quantumValue (Honest.sourceGame L D) := by
  rw [sourceGame_depthFamily e L D hℓ hL]
  exact quantumValue_le e L D

end MIPRE.Introspection.SourcePadding
end
