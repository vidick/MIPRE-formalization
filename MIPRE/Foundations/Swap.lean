/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.StateDistance
public import MIPRE.Foundations.POVMValue

@[expose] public section

/-!
# Exchanging the two players

A game whose question distribution and decision predicate are both symmetric in the players is
unchanged by exchanging them, and so is the value of a strategy once the state is swapped
(`povmValue_swapVec_of_symm`). That is what turns a one-sided soundness statement --- one proved
about Alice's measurements, with Bob's only as the other party --- into the statement about
**Bob's**, with no second proof: apply it to `(MB, MA)` on `swapVec ψ`, and read the conclusion
back through `norm_stateVecB`. In a bipartite model the exchange is `BipartiteModel.swap`, and the
statement is proved once there (`BipartiteModel.povmValue_eq_of_bornProb_swap`).

The Pauli basis test is such a game: every rule of its decider is written in both orientations
(`MIPRE.QLD.accepts_symm`) and its sampler draws an *ordered* edge of a symmetric type graph
(`MIPRE.QLD.qldGame_mu_symm`). Its combining stage needs both players' commutation bounds, which
is why this is here.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker

/-! ## In a bipartite model

In a model the exchange of the players is `BipartiteModel.swap`, and the two players' operators
commute, so a Born probability is symmetric with no reindexing at all (`bornProb_swap`). The
value statement is proved once, for any two models whose Born probabilities agree with the
players exchanged (`povmValue_eq_of_bornProb_swap`): the swapped model is one
(`povmValue_swap_of_symm`), and the tensor-product model of the swapped vector is another,
which is the matrix statement below. -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)

variable [PartialOrder 𝒜] [PartialOrder ℬ] {X A : Type*} [Fintype X] [Fintype A]

/-- **The value of a strategy for a symmetric game is unchanged by exchanging the players**, in
any model whose Born probabilities are those of `M` with the players exchanged. Both halves of
the hypothesis on the game are needed: the question distribution is symmetric, and the decider
accepts a swapped question pair with the answers swapped too. -/
theorem povmValue_eq_of_bornProb_swap {𝒞' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞']
    (M' : BipartiteModel 𝒞' ℬ 𝒜) (hM : ∀ a b, M'.bornProb b a = M.bornProb a b)
    {G : Game X X A A} (MA : X → POVMIn A 𝒜) (MB : X → POVMIn A ℬ)
    (hμ : ∀ x y, G.μ x y = G.μ y x) (hD : ∀ x y a b, G.D x y a b = G.D y x b a) :
    M'.povmValue G MB MA = M.povmValue G MA MB := by
  have hterm : ∀ x y : X, G.μ x y * M'.condWin G MB MA x y
      = G.μ y x * M.condWin G MA MB y x := by
    intro x y
    have hcw : M'.condWin G MB MA x y = M.condWin G MA MB y x := by
      have h : ∀ a b : A,
          (if G.D x y a b then (1 : ℝ) else 0) * M'.bornProb ((MB x).op a) ((MA y).op b)
            = (if G.D y x b a then (1 : ℝ) else 0) * M.bornProb ((MA y).op b) ((MB x).op a) := by
        intro a b
        rw [hM, hD x y a b]
      rw [condWin, condWin, Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
        Finset.sum_congr rfl fun b (_ : b ∈ univ) => h a b]
      exact Finset.sum_comm
    rw [hμ x y, hcw]
  rw [povmValue, povmValue, Finset.sum_congr rfl fun x (_ : x ∈ univ) =>
    Finset.sum_congr rfl fun y (_ : y ∈ univ) => hterm x y]
  exact Finset.sum_comm

/-- **Exchanging the players in the model**: the value of a strategy for a symmetric game is the
value of the exchanged strategy in the swapped model. -/
theorem povmValue_swap_of_symm {G : Game X X A A} (MA : X → POVMIn A 𝒜) (MB : X → POVMIn A ℬ)
    (hμ : ∀ x y, G.μ x y = G.μ y x) (hD : ∀ x y a b, G.D x y a b = G.D y x b a) :
    M.swap.povmValue G MB MA = M.povmValue G MA MB :=
  M.povmValue_eq_of_bornProb_swap M.swap M.bornProb_swap MA MB hμ hD

end BipartiteModel

variable {X A dA dB : Type*} [Fintype X] [Fintype A] [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]

omit [DecidableEq dA] [DecidableEq dB] in
/-- **Swapping the state exchanges the two factors of a Born probability.** -/
theorem bornProb_swapVec (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) :
    bornProb (swapVec ψ) EB EA = bornProb ψ EA EB := by
  classical
  have inner : ∀ (i : dA) (j : dB),
      (((EB ⊗ₖ EA) *ᵥ swapVec ψ) (j, i)) = (((EA ⊗ₖ EB) *ᵥ ψ) (i, j)) := by
    intro i j
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
    refine Fintype.sum_equiv (Equiv.prodComm dB dA) _ _ fun q => ?_
    obtain ⟨l, k⟩ := q
    show (EB ⊗ₖ EA) (j, i) (l, k) * (swapVec ψ) (l, k)
        = (EA ⊗ₖ EB) (i, j) (k, l) * ψ (k, l)
    show EB j l * EA i k * ψ (k, l) = EA i k * EB j l * ψ (k, l)
    ring
  have key : star (swapVec ψ) ⬝ᵥ ((EB ⊗ₖ EA) *ᵥ swapVec ψ)
      = star ψ ⬝ᵥ ((EA ⊗ₖ EB) *ᵥ ψ) := by
    rw [dotProduct, dotProduct]
    refine Fintype.sum_equiv (Equiv.prodComm dB dA) _ _ fun p => ?_
    obtain ⟨j, i⟩ := p
    show star (swapVec ψ) (j, i) * (((EB ⊗ₖ EA) *ᵥ swapVec ψ) (j, i))
        = star ψ (i, j) * (((EA ⊗ₖ EB) *ᵥ ψ) (i, j))
    rw [inner i j]
    rfl
  rw [bornProb, bornProb, key]

omit [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB] in
@[simp] theorem swapVec_swapVec (ψ : dA × dB → ℂ) : swapVec (swapVec ψ) = ψ := rfl

/-- **The value of a strategy for a symmetric game is unchanged by exchanging the players.** Both
halves of the hypothesis are needed, and both are properties of the *game*: the question
distribution is symmetric, and the decider accepts a swapped question pair with the answers
swapped too. -/
theorem povmValue_swapVec_of_symm {G : Game X X A A} (ψ : dA × dB → ℂ)
    (MA : X → POVM A dA) (MB : X → POVM A dB)
    (hμ : ∀ x y, G.μ x y = G.μ y x) (hD : ∀ x y a b, G.D x y a b = G.D y x b a) :
    povmValue G (swapVec ψ) MB MA = povmValue G ψ MA MB := by
  rw [povmValue_eq_tensor, povmValue_eq_tensor]
  exact (BipartiteModel.tensor ψ).povmValue_eq_of_bornProb_swap
    (BipartiteModel.tensor (swapVec ψ))
    (fun X Y => by rw [← bornProb_eq_tensor, ← bornProb_eq_tensor, bornProb_swapVec]) _ _ hμ hD

end MIPRE

end

end
