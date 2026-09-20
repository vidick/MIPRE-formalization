/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.StateDistance
import MIPRE.Foundations.POVMValue

/-!
# Exchanging the two players

A game whose question distribution and decision predicate are both symmetric in the players is
unchanged by exchanging them, and so is the value of a strategy once the state is swapped
(`povmValue_swapVec_of_symm`). That is what turns a one-sided soundness statement --- one proved
about Alice's measurements, with Bob's only as the other party --- into the statement about
**Bob's**, with no second proof: apply it to `(MB, MA)` on `swapVec ψ`, and read the conclusion
back through `norm_stateVecB`.

The Pauli basis test is such a game: every rule of its decider is written in both orientations
(`MIPRE.QLD.accepts_symm`) and its sampler draws an *ordered* edge of a symmetric type graph
(`MIPRE.QLD.qldGame_mu_symm`). Its combining stage needs both players' commutation bounds, which
is why this is here.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker

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
  classical
  have hterm : ∀ x y : X, G.μ x y * condWin G (swapVec ψ) MB MA x y
      = G.μ y x * condWin G ψ MA MB y x := by
    intro x y
    have hcw : condWin G (swapVec ψ) MB MA x y = condWin G ψ MA MB y x := by
      have h : ∀ a b : A,
          (if G.D x y a b then (1 : ℝ) else 0)
              * bornProb (swapVec ψ) (((MB x).mats a).val) (((MA y).mats b).val)
            = (if G.D y x b a then (1 : ℝ) else 0)
              * bornProb ψ (((MA y).mats b).val) (((MB x).mats a).val) := by
        intro a b
        rw [bornProb_swapVec, hD x y a b]
      rw [condWin, condWin, Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
        Finset.sum_congr rfl fun b (_ : b ∈ univ) => h a b]
      exact Finset.sum_comm
    rw [hμ x y, hcw]
  rw [povmValue, povmValue, Finset.sum_congr rfl fun x (_ : x ∈ univ) =>
    Finset.sum_congr rfl fun y (_ : y ∈ univ) => hterm x y]
  exact Finset.sum_comm

end MIPRE

end
