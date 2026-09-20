/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Expanded
import MIPRE.Foundations.Swap

/-!
# The Pauli basis test is symmetric in the two players

Every rule of `fig:decider_pauli` is written in both orientations and the sampler draws an
*ordered* edge of a symmetric type graph, so exchanging the two players is an automorphism of the
game (`accepts_symm`, `qldGame_mu_symm`). `povmValue_qldGame_swapVec` is the consequence for a
strategy's value, and the two corollaries at the end are what the combining stage actually wants:
the expansion stage's estimates, proved about **Alice's** measurements, hold for **Bob's** as
well, with the same constants and no second proof.

The device is `swapVec`: a statement about `stateVec (hatVec (swapVec psi))` is one about
`stateVecB (hatVec psi)`, because the expanded state's two halves are exchanged by the swap
(`hatVec_swapVec`, which needs the maximally entangled ancilla to be symmetric ---
`MIPRE.Weyl.swapVec_epr`).
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

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **Exchanging the two players leaves the value of a strategy unchanged.** -/
theorem povmValue_qldGame_swapVec (hm : m ∣ Fintype.card F) (ψ : dA × dB → ℂ)
    (MA : Question F m → POVM (Answer F m d) dA)
    (MB : Question F m → POVM (Answer F m d) dB) :
    povmValue (qldGame hm) (swapVec ψ) MB MA = povmValue (qldGame hm) ψ MA MB :=
  povmValue_swapVec_of_symm ψ MA MB (qldGame_mu_symm hm) fun x y a b => accepts_symm hm x y a b

/-- The expanded state's two halves are exchanged by the swap. -/
theorem hatVec_swapVec (ψ : dA × dB → ℂ) :
    hatVec (F := F) (m := m) (swapVec ψ) = swapVec (hatVec (F := F) (m := m) ψ) := by
  rw [hatVec, hatVec, swapVec_expVec, swapVec_epr]

/-! ## The expansion stage, for the other player -/

variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

theorem swapVec_unit (hψ : star ψ ⬝ᵥ ψ = 1) : star (swapVec ψ) ⬝ᵥ swapVec ψ = 1 := by
  rw [swapVec_dotProduct]; exact hψ

theorem povmValue_swapped_le (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    1 - povmValue (qldGame hm) (swapVec ψ) MB MA ≤ ε := by
  rw [povmValue_qldGame_swapVec]; exact hfail

/-- **The commutation half of `lem:qld-expanded-points` for the other player.** Exactly
`hatObs_commutation`, applied to the swapped strategy on the swapped state. -/
theorem hatObs_commutation_swap (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ‖stateVec (hatVec (F := F) (m := m) (swapVec ψ))
          (hatObs hm MB .X c * hatObs hm MB .Z c
            - hatObs hm MB .Z c * hatObs hm MB .X c)‖ ^ 2
      ≤ 57676416 * ε :=
  hatObs_commutation (MB := MA) (swapVec_unit hψ) (povmValue_swapped_le hfail)

/-- **The self-consistency half for the other player**, which is the same statement: the
cross-party deviation is symmetric under exchanging the two parties. -/
theorem hatPOVM_consistency_swap (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ a : F, xSqNorm (hatVec (F := F) (m := m) (swapVec ψ))
          (((hatPOVM hm MB W c).mats a).val) (((hatPOVM hm MA W c).mats a).val)
      ≤ 172 * ε :=
  hatPOVM_consistency (MB := MA) (swapVec_unit hψ) (povmValue_swapped_le hfail) W

end MIPRE.QLD

end
