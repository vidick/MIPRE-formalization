/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.GameTransport

/-!
# Restricting a game to the support of its question distribution

The counterpart for questions of `quantumValue_extendAnswers`: a game whose question
distribution is supported on the image of embeddings `X' ↪ X`, `Y' ↪ Y` has the same quantum
value as its restriction to `X' × Y'`, with the distribution and the decision predicate pulled
back (`quantumValue_restrictQuestions`). From the large game to the small one a strategy is
played through the embeddings (`TensorProductStrategy.relabel`, which accepts any question
maps); from the small one to the large one it is played through a retraction
(`Function.invFun`), the questions off the image carrying no weight either way.

The consumer is the class verifier of the polynomial-time halting reduction
(`Halting/Paper/ClassMain.lean`): its game has every string of length at most `B` as a
question, while its sampler only ever produces the strings of length `s(C)` — the compressed
sampler's questions at the fixed level — and the two games have the same value.
-/

namespace MIPRE

open Matrix Kronecker
open scoped ComplexOrder

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

namespace TensorProductStrategy

/-- Playing a strategy of `G` on the restriction `G'` through the embeddings keeps the value,
when `G`'s distribution is supported on the image. -/
theorem value_relabel_of_support {X' Y' : Type*} [Fintype X'] [Fintype Y'] {G : Game X Y A B}
    (S : TensorProductStrategy G) (G' : Game X' Y' A B) (eX : X' ↪ X) (eY : Y' ↪ Y)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hμ0 : ∀ x y, G.μ x y ≠ 0 → (∃ x', eX x' = x) ∧ (∃ y', eY y' = y))
    (hD : ∀ x' y' a b, G'.D x' y' a b = G.D (eX x') (eY y') a b) :
    (S.relabel G' eX eY (Equiv.refl A) (Equiv.refl B)).value = S.value := by
  unfold value
  show (∑ x', ∑ y', ∑ a, ∑ b, G'.μ x' y' * (if G'.D x' y' a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M (eX x') a ⊗ₖ S.PB.M (eY y') b) *ᵥ S.ψ)).re) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re
  symm
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map eX)) ?_, Finset.sum_map]
  swap
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    have h0 : G.μ x y = 0 := by
      by_contra h
      obtain ⟨x', hx'⟩ := (hμ0 x y h).1
      exact hx (Finset.mem_map.2 ⟨x', Finset.mem_univ _, hx'⟩)
    simp [h0]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map eY)) ?_, Finset.sum_map]
  swap
  · intro y _ hy
    have h0 : G.μ (eX x') y = 0 := by
      by_contra h
      obtain ⟨y', hy'⟩ := (hμ0 _ y h).2
      exact hy (Finset.mem_map.2 ⟨y', Finset.mem_univ _, hy'⟩)
    simp [h0]
  refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  rw [hμ, hD]

/-- Playing a strategy of the restriction `G'` on `G` through retractions of the embeddings
keeps the value, when `G`'s distribution is supported on the image. -/
theorem value_relabel_invFun {X' Y' : Type*} [Fintype X'] [Fintype Y'] [Nonempty X']
    [Nonempty Y'] {G' : Game X' Y' A B} (S' : TensorProductStrategy G') (G : Game X Y A B)
    (eX : X' ↪ X) (eY : Y' ↪ Y)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hμ0 : ∀ x y, G.μ x y ≠ 0 → (∃ x', eX x' = x) ∧ (∃ y', eY y' = y))
    (hD : ∀ x' y' a b, G'.D x' y' a b = G.D (eX x') (eY y') a b) :
    (S'.relabel G (Function.invFun eX) (Function.invFun eY) (Equiv.refl A)
      (Equiv.refl B)).value = S'.value := by
  unfold value
  show (∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S'.ψ ⬝ᵥ ((S'.PA.M (Function.invFun eX x) a ⊗ₖ
        S'.PB.M (Function.invFun eY y) b) *ᵥ S'.ψ)).re) =
    ∑ x', ∑ y', ∑ a, ∑ b, G'.μ x' y' * (if G'.D x' y' a b then 1 else 0) *
      (star S'.ψ ⬝ᵥ ((S'.PA.M x' a ⊗ₖ S'.PB.M y' b) *ᵥ S'.ψ)).re
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map eX)) ?_, Finset.sum_map]
  swap
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    have h0 : G.μ x y = 0 := by
      by_contra h
      obtain ⟨x', hx'⟩ := (hμ0 x y h).1
      exact hx (Finset.mem_map.2 ⟨x', Finset.mem_univ _, hx'⟩)
    simp [h0]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map eY)) ?_, Finset.sum_map]
  swap
  · intro y _ hy
    have h0 : G.μ (eX x') y = 0 := by
      by_contra h
      obtain ⟨y', hy'⟩ := (hμ0 _ y h).2
      exact hy (Finset.mem_map.2 ⟨y', Finset.mem_univ _, hy'⟩)
    simp [h0]
  refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  rw [hμ, hD, Function.leftInverse_invFun eX.injective x',
    Function.leftInverse_invFun eY.injective y']

end TensorProductStrategy

/-- **Restriction to the support.** A game whose question distribution is supported on the
image of embeddings `X' ↪ X`, `Y' ↪ Y` has the quantum value of its restriction to
`X' × Y'`: the game `G'` with `G'.μ x' y' = G.μ (eX x') (eY y')` and
`G'.D x' y' = G.D (eX x') (eY y')`. -/
theorem quantumValue_restrictQuestions {X' Y' : Type*} [Fintype X'] [Fintype Y'] [Nonempty X']
    [Nonempty Y'] (G : Game X Y A B) (G' : Game X' Y' A B) (eX : X' ↪ X) (eY : Y' ↪ Y)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hμ0 : ∀ x y, G.μ x y ≠ 0 → (∃ x', eX x' = x) ∧ (∃ y', eY y' = y))
    (hD : ∀ x' y' a b, G'.D x' y' a b = G.D (eX x') (eY y') a b) :
    quantumValue G' = quantumValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S' => ?_) (quantumValue_nonneg _)
    rw [← S'.value_relabel_invFun G eX eY hμ hμ0 hD]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G) _
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    rw [← S.value_relabel_of_support G' eX eY hμ hμ0 hD]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G') _

/-- The restriction of a game along question maps whose images carry the whole distribution:
the same distribution and decision predicate, pulled back. -/
noncomputable def Game.restrict {X' Y' : Type*} [Fintype X'] [Fintype Y'] (G : Game X Y A B)
    (eX : X' → X) (eY : Y' → Y) (h : ∑ x', ∑ y', G.μ (eX x') (eY y') = 1) :
    Game X' Y' A B where
  μ x' y' := G.μ (eX x') (eY y')
  μ_nonneg _ _ := G.μ_nonneg _ _
  μ_sum_one := h
  D x' y' a b := G.D (eX x') (eY y') a b

end MIPRE
