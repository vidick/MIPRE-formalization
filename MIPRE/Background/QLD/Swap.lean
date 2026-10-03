/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Expanded
public import MIPRE.Foundations.Swap

@[expose] public section

/-!
# The Pauli basis test is symmetric in the two players

Every rule of `fig:decider_pauli` is written in both orientations and the sampler draws an
*ordered* edge of a symmetric type graph, so exchanging the two players is an automorphism of the
game (`accepts_symm`, `qldGame_mu_symm`). `povmValue_qldGame_swapVec` is the consequence for a
strategy's value, and the two corollaries at the end are what the combining stage actually wants:
the expansion stage's estimates, proved about **Alice's** measurements, hold for **Bob's** as
well, with the same constants and no second proof.

## In a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). Exchanging the players is
`BipartiteModel.swap`: the same state model with the two players' algebras exchanged, so a
statement about the first player of `M.swap` is one about the second player of `M`, with no
reindexing of vectors (the matrix route's `swapVec`). The expanded model of the swapped strategy
is `M.swap.reg (Anc F m)`, whose first player holds the first half of the EPR register; the swap
of the expanded model, `(M.reg (Anc F m)).swap`, gives the second player the second half. The two
read one state, the EPR vector being symmetric, through the local isometry
`BipartiteModel.regSwap` that exchanges the halves (`hatVec_swapVec` and its companions, the model
form of `hatVec (swapVec ψ) = swapVec (hatVec ψ)`).
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}

set_option linter.unusedSectionVars false

/-! ## The decider is symmetric -/

variable [Algebra (ZMod 2) F] [NeZero m]

set_option maxHeartbeats 1000000 in
/-- **Each rule of the decider is stated in both orientations.** The proof is the case analysis
over the two question types and the two answer shapes; every branch of `pairTest` has a mirror
branch written beside it, and the catch-all is symmetric. -/
theorem pairTest_symm (hm : m ∣ Fintype.card F) (x y : Question F m) (a b : Answer F m d) :
    pairTest hm x y a b = pairTest hm y x b a := by
  cases x <;> cases y <;> cases a <;> cases b <;> simp [pairTest]

/-- **The subtests are symmetric.** At equal types the test is the agreement check, which is
symmetric; off the diagonal it is `pairTest`. -/
theorem subtests_symm (hm : m ∣ Fintype.card F) (x y : Question F m) (a b : Answer F m d) :
    subtests hm x y a b = subtests hm y x b a := by
  rw [subtests, subtests]
  by_cases h : x.ty = y.ty
  · rw [if_pos h, if_pos h.symm]
    by_cases hab : a = b
    · rw [hab]
    · rw [decide_eq_false hab, decide_eq_false (Ne.symm hab)]
  · rw [if_neg h, if_neg fun hc => h hc.symm, pairTest_symm]

/-- **The decider is symmetric in the two players.** -/
theorem accepts_symm (hm : m ∣ Fintype.card F) (x y : Question F m) (a b : Answer F m d) :
    accepts hm x y a b = accepts hm y x b a := by
  rw [accepts, accepts, subtests_symm hm x y a b]
  cases hx : x.fmtOk a <;> cases hy : y.fmtOk b <;> simp

/-! ## The sampler is symmetric -/

/-- Exchanging the two endpoints of an ordered edge of the type graph. -/
def TyEdge.swap (e : TyEdge) : TyEdge :=
  ⟨(e.val.2, e.val.1), (adj_symm e.val.2 e.val.1).trans e.2⟩

@[simp] theorem TyEdge.swap_swap (e : TyEdge) : e.swap.swap = e := Subtype.ext rfl

/-- Exchanging the two players' questions, as an involution of the verifier's random choices. -/
def sampleSwap : Sample F m ≃ Sample F m where
  toFun sm := (sm.1.swap, sm.2)
  invFun sm := (sm.1.swap, sm.2)
  left_inv sm := by rw [Prod.mk.injEq]; exact ⟨TyEdge.swap_swap sm.1, rfl⟩
  right_inv sm := by rw [Prod.mk.injEq]; exact ⟨TyEdge.swap_swap sm.1, rfl⟩

/-- **The question distribution is symmetric.** The type graph's adjacency is symmetric, so
exchanging an edge's endpoints is a bijection of the sample space that exchanges the two
players' questions and changes no probability. -/
theorem qldGame_mu_symm (hm : m ∣ Fintype.card F) (x y : Question F m) :
    (qldGame (d := d) hm).μ x y = (qldGame (d := d) hm).μ y x := by
  show (∑ sm : Sample F m, (Fintype.card (Sample F m) : ℝ)⁻¹ *
      if (sm.2.question hm sm.1.val.1, sm.2.question hm sm.1.val.2) = (x, y) then 1 else 0)
    = ∑ sm : Sample F m, (Fintype.card (Sample F m) : ℝ)⁻¹ *
      if (sm.2.question hm sm.1.val.1, sm.2.question hm sm.1.val.2) = (y, x) then 1 else 0
  refine Fintype.sum_equiv sampleSwap _ _ fun sm => ?_
  congr 1
  refine if_congr ?_ rfl rfl
  show ((sm.2.question hm sm.1.val.1, sm.2.question hm sm.1.val.2) = (x, y))
    ↔ ((sm.2.question hm sm.1.val.2, sm.2.question hm sm.1.val.1) = (y, x))
  rw [Prod.mk.injEq, Prod.mk.injEq]
  exact and_comm

/-! ## The value of a swapped strategy -/

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **Exchanging the two players leaves the value of a strategy unchanged**: the exchanged
strategy in the swapped model has the value of the strategy in the model. -/
theorem povmValue_qldGame_swapVec (hm : m ∣ Fintype.card F) (M : BipartiteModel 𝒞 𝒜 ℬ)
    (PA : Question F m → POVMIn (Answer F m d) 𝒜)
    (PB : Question F m → POVMIn (Answer F m d) ℬ) :
    M.swap.povmValue (qldGame hm) PB PA = M.povmValue (qldGame hm) PA PB :=
  M.povmValue_swap_of_symm PA PB (qldGame_mu_symm hm) fun x y a b => accepts_symm hm x y a b

/-- **The expanded model of the swapped strategy reads the expanded state with the players
exchanged**: a second-player operator on the register model of `M` has, as a first-player operator
of the register model of `M.swap`, the same state norm. The model form of
`hatVec (swapVec ψ) = swapVec (hatVec ψ)`: the local isometry exchanging the two halves of the
EPR register carries the one state to the other exactly (`BipartiteModel.regSwap_W_ψ`). -/
theorem hatVec_swapVec (M : BipartiteModel 𝒞 𝒜 ℬ) (Y : Matrix (Anc F m) (Anc F m) ℬ) :
    (M.swap.reg (Anc F m)).stateSqNorm Y = (M.reg (Anc F m)).swap.stateSqNorm Y :=
  M.regSwap.stateSqNorm_of_W_ψ M.regSwap_W_ψ Y

/-- The same reading for a cross-party deviation. -/
theorem hatVec_swapVec_xSqNorm (M : BipartiteModel 𝒞 𝒜 ℬ) (X : Matrix (Anc F m) (Anc F m) 𝒜)
    (Y : Matrix (Anc F m) (Anc F m) ℬ) :
    (M.swap.reg (Anc F m)).xSqNorm Y X = (M.reg (Anc F m)).xSqNorm X Y := by
  rw [← (M.reg (Anc F m)).xSqNorm_swap]
  exact M.regSwap.xSqNorm_of_W_ψ M.regSwap_W_ψ Y X

/-- The same reading for a Born probability. -/
theorem hatVec_swapVec_bornProb (M : BipartiteModel 𝒞 𝒜 ℬ) (X : Matrix (Anc F m) (Anc F m) 𝒜)
    (Y : Matrix (Anc F m) (Anc F m) ℬ) :
    (M.swap.reg (Anc F m)).bornProb Y X = (M.reg (Anc F m)).bornProb X Y := by
  rw [← (M.reg (Anc F m)).bornProb_swap]
  exact M.regSwap.bornProb_of_W_ψ M.regSwap_W_ψ Y X

/-! ## The expansion stage, for the other player -/

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
  {ε : ℝ}

/-- The swapped model has the state of the model. -/
theorem swapVec_unit (hM : ‖M.ψ‖ = 1) : ‖M.swap.ψ‖ = 1 := hM

theorem povmValue_swapped_le (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) :
    1 - M.swap.povmValue (qldGame hm) PB PA ≤ ε := by
  rw [povmValue_qldGame_swapVec]; exact hfail

end MIPRE.QLD

end

end
