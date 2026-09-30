/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.SourcePadding

@[expose] public section

/-! # Removing padding from arbitrary source-game strategies

Canonical zero-extension of questions pulls every padded strategy back, in its
own model, with exactly its value. The unused seed coordinates average out
uniformly; this is not restricted to perfect strategies or PCC strategies.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): a projective strategy
(`BipartiteModel.ProjStrat`) of the padded source game in a model, asked the zero-extension of
each original question (`ProjStrat.restrict`), is a projective strategy of the original source
game in the same model, of the same value (`restrictStrategy`, `restrictStrategy_value`,
`exists_projStrat_value_ge`); the state and the dimensions of the matrix statement are the model
itself. The value comparisons `quantumValue_le` and `quantumValue_depthFamily_le` hold in every
value model approached by the projective strategies of the models it dominates
(`ValueModel.ProjApprox`), which `val*` and `ω_co` are (`ValueModel.tensor_projApprox`,
`ValueModel.commuting_projApprox`); the matrix statements are their instances at
`ValueModel.tensor`.
-/

noncomputable section

namespace MIPRE.ValueModel

/-- **The value model is approached by the projective strategies of the models it dominates**:
below the value of a game, and above `0`, lies the value of a projective strategy for it in a
bipartite model, on a Hilbert space of `Type`, that `ω` dominates. With `ValueModel.Dominates`,
`ω.val G` is then the supremum of the values of these strategies, so two games whose projective
strategies compare model by model have comparable values (`SourcePadding.quantumValue_le`).
`val*` has it through the tensor-product models of tensor-product strategies
(`tensor_projApprox`), `ω_co` through the models of commuting-operator strategies
(`commuting_projApprox`). -/
def ProjApprox (ω : ValueModel) : Prop :=
  ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] (G : Game X Y A B) {t : ℝ},
    0 ≤ t → t < ω.val G →
      ∃ (𝒞 𝒜 ℬ : Type) (_ : Ring 𝒞) (_ : StarRing 𝒞) (_ : Algebra ℂ 𝒞) (_ : Ring 𝒜)
        (_ : StarRing 𝒜) (_ : Algebra ℂ 𝒜) (_ : Ring ℬ) (_ : StarRing ℬ) (_ : Algebra ℂ ℬ)
        (_ : PartialOrder 𝒜) (_ : StarOrderedRing 𝒜) (_ : PartialOrder ℬ)
        (_ : StarOrderedRing ℬ) (M : BipartiteModel.{0} 𝒞 𝒜 ℬ),
        ω.Dominates M ∧ ∃ S : M.ProjStrat G, t < S.value

/-- **`val*` is approached by the projective strategies of the models it dominates**: a
tensor-product strategy near the supremum is a projective strategy of its tensor-product model,
of the same value (`TensorProductStrategy.toModel`), and `val*` dominates that model
(`tensor_dominates`). -/
theorem tensor_projApprox : tensor.ProjApprox := fun G t ht h => by
  rw [tensor_val, quantumValue] at h
  rcases isEmpty_or_nonempty (TensorProductStrategy G) with hG | hG
  · rw [Real.iSup_of_isEmpty] at h
    exact absurd ht (not_le.mpr h)
  obtain ⟨T, hT⟩ := exists_lt_of_lt_ciSup h
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, BipartiteModel.tensor T.ψ,
    @tensor_dominates _ _ T.ψ, T.toModel, by rwa [T.value_toModel]⟩

/-- **`ω_co` is approached by the projective strategies of the models it dominates**: those of
the models of commuting-operator strategies (`exists_projStrat_lt_commutingOperatorValue`), which
`ω_co` dominates (`commuting_dominates`). -/
theorem commuting_projApprox : commuting.ProjApprox := fun G t ht h => by
  obtain ⟨S, R, hR⟩ := exists_projStrat_lt_commutingOperatorValue ht h
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, S.toModel,
    @commuting_dominates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S.toModel, R, hR⟩

end MIPRE.ValueModel

namespace MIPRE.Introspection.SourcePadding
open Matrix Finset Classical
set_option linter.unusedSectionVars false

section Restrict

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
      simp only [CL.pull, dite_eq_left h]
      exact congrArg p.1 (e.injective h.choose_spec)
    · funext j
      simp only [dite_eq_right j.property]

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
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {Ψ : BipartiteModel 𝒞 𝒜 ℬ}

/-- Ask the padded strategy the canonical extension of the original question, in the same
model. -/
def restrictStrategy (S : Ψ.ProjStrat (Honest.sourceGame (family e L) (decider e D))) :
    Ψ.ProjStrat (Honest.sourceGame L D) :=
  S.restrict _ (CL.push e) (CL.push e)

/-- At an original question pair, the restricted strategy wins exactly as the padded strategy
does at the extended pair: the padded decider reads the original questions back. -/
theorem restrictStrategy_succAt
    (S : Ψ.ProjStrat (Honest.sourceGame (family e L) (decider e D))) (x y : I → F) :
    Ψ.condWin (Honest.sourceGame L D) (restrictStrategy e L D S).PA
        (restrictStrategy e L D S).PB x y =
      Ψ.condWin (Honest.sourceGame (family e L) (decider e D)) S.PA S.PB (CL.push e x)
        (CL.push e y) := by
  show ∑ a, ∑ b, (if D x y a b then 1 else 0) *
      Ψ.bornProb ((S.PA (CL.push e x)).op a) ((S.PB (CL.push e y)).op b) =
    ∑ a, ∑ b, (if D (CL.pull e (CL.push e x)) (CL.pull e (CL.push e y)) a b then 1 else 0) *
      Ψ.bornProb ((S.PA (CL.push e x)).op a) ((S.PB (CL.push e y)).op b)
  rw [CL.pull_push, CL.pull_push]

/-- **Restriction keeps the value**: the padded seed's unused coordinates average out
(`average_pull`). -/
theorem restrictStrategy_value
    (S : Ψ.ProjStrat (Honest.sourceGame (family e L) (decider e D))) :
    (restrictStrategy e L D S).value = S.value := by
  change (∑ x, ∑ y, SampledGame.dist (L false).eval (L true).eval x y *
      Ψ.condWin (Honest.sourceGame L D) (restrictStrategy e L D S).PA
        (restrictStrategy e L D S).PB x y) =
    ∑ x, ∑ y, SampledGame.dist (family e L false).eval (family e L true).eval x y *
      Ψ.condWin (Honest.sourceGame (family e L) (decider e D)) S.PA S.PB x y
  rw [SampledGame.sum_dist_mul, SampledGame.sum_dist_mul]
  have hf : ∀ w (x : J → F), (family e L w).eval x = CL.push e ((L w).eval (CL.pull e x)) :=
    fun w x => CL.CLFun.eval_embed e (L w) x
  simp_rw [restrictStrategy_succAt, hf]
  exact (average_pull e (fun y => Ψ.condWin (Honest.sourceGame (family e L) (decider e D)) S.PA
    S.PB (CL.push e ((L false).eval y)) (CL.push e ((L true).eval y)))).symm

/-- **Every padded strategy restricts without loss, in its own model**: the model form of
`quantumValue_le`. -/
theorem exists_projStrat_value_ge
    (S : Ψ.ProjStrat (Honest.sourceGame (family e L) (decider e D))) :
    ∃ R : Ψ.ProjStrat (Honest.sourceGame L D), S.value ≤ R.value :=
  ⟨restrictStrategy e L D S, (restrictStrategy_value e L D S).ge⟩

/-- Filling the spectator coordinates inside the existing first factor gives the same source
game (`sourceGame_depthFamily`), so its strategies restrict without loss too: the model form of
`quantumValue_depthFamily_le`. -/
theorem exists_projStrat_depthFamily_value_ge (hℓ : 0 < ℓ) (hL : ∀ w, (L w).SupportedOn univ)
    (S : Ψ.ProjStrat (Honest.sourceGame (depthFamily e L) (decider e D))) :
    ∃ R : Ψ.ProjStrat (Honest.sourceGame L D), S.value ≤ R.value := by
  revert S
  rw [sourceGame_depthFamily e L D hℓ hL]
  exact exists_projStrat_value_ge e L D

end Restrict

section Value

variable {F I J A : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  {ℓ : ℕ} (e : I ↪ J) (L : Bool → CL.CLFun F I ℓ) (D : (I → F) → (I → F) → A → A → Bool)

/-- Soundness can return from the padded source game to the original game
without losing any value, in every value model approached by the projective strategies of the
models it dominates: each of those strategies restricts, in its model, to one of the original
game of the same value (`restrictStrategy_value`). -/
theorem quantumValue_le {ω : ValueModel} (hω : ω.ProjApprox) :
    ω.val (Honest.sourceGame (family e L) (decider e D)) ≤ ω.val (Honest.sourceGame L D) := by
  refine le_of_forall_lt fun t ht => ?_
  rcases lt_or_ge t 0 with h0 | h0
  · exact h0.trans_le (ω.nonneg _)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, M, hM, S, hS⟩ := hω _ h0 ht
  exact hS.trans_le ((restrictStrategy_value e L D S).symm.le.trans (hM _ _))

/-- Filling the spectator coordinates inside the existing first factor also
has no soundness cost, since its entire source game is identical. -/
theorem quantumValue_depthFamily_le {ω : ValueModel} (hω : ω.ProjApprox) (hℓ : 0 < ℓ)
    (hL : ∀ w, (L w).SupportedOn univ) :
    ω.val (Honest.sourceGame (depthFamily e L) (decider e D)) ≤
      ω.val (Honest.sourceGame L D) := by
  rw [sourceGame_depthFamily e L D hℓ hL]
  exact quantumValue_le e L D hω

end Value

end MIPRE.Introspection.SourcePadding
end

end
