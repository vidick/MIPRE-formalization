/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichMain.Completeness
public import MIPRE.Background.LIDT.Co.Test.StrategyCore

@[expose] public section

/-!
# Preliminary comparison theorems: bipartite self-consistency (core)

Core building blocks for bipartite self-consistency: reflexivity of the state-dependent
distance, the swap of placements inside `qSDDCore`, and `prop:two-notions-of-self-consistency`.
This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Core.lean` in the
port of `planning/c6b-plan.md` (milestone M3, section "Port conventions").

The bipartite statements take a symmetric model `S : SymModel 𝔓 K` in place of the state
`ψ : QuantumState (ι × ι)`, and local families in `𝔓`; `sddError_self` is about a state on one
space and takes a vector state `V : VecState K`. Each takes the model or the vector state as an
explicit first argument, in the namespace `Preliminaries`, as the vendored lemmas do.

The vendored swap hypotheses are dropped: `hperm : PermInvState ψ` from
`qSDDCore_rightTensor_eq_leftTensor_of_permInv` and
`qSDD_liftLeft_liftRight_le_two_qBipartiteSSCDefect`, and the conjunct `PermInvState ψ` of the
hypothesis of `twoNotionsOfSelfConsistency`. Each use of `PermInvState.swap_ev` is the model's
`S.ev_L_eq_ev_R` (`Co/Basic/QuantumState.lean`). The vendored
`qSDDCore_rightTensor_eq_leftTensor_of_permInv` took the state implicitly, determined by
`hperm`; with `hperm` gone the model is explicit.

## New here

- `ev_adjoint_self_leftTensor_sub_rightTensor`: the expansion
  `ev((L X - R X)^* (L X - R X)) = 2 (ev L(X²) - ev(L X R X))` for self-adjoint `X`, which the
  vendored file proves inline (`h_expand`) and `BipartiteSelfConsistency/Local.lean` repeats;
  here it is the case `X = Y` of `ev_star_L_sub_R_mul_self` (`SwitchSandwichMain/RightTransfer`)
  with the swap.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`, `prop:two-notions-of-self-consistency`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_mono avgOver_const_mul)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The self-distance `sddError 𝒟 A A` is zero. -/
theorem sddError_self {Question Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome (K →L[ℂ] K)) :
    V.sddError 𝒟 A A = 0 :=
  V.sddError_self 𝒟 A

/-- The `qSDDCore` distance between right placements of two local operator families equals the
distance between their left placements.

The vendored lemma asks for a permutation-invariant state; here swap symmetry is the model's
`S.ev_L_eq_ev_R`, applied to `(A_a - B_a)^* (A_a - B_a)`. -/
theorem qSDDCore_rightTensor_eq_leftTensor_of_permInv {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (A B : Outcome → 𝔓) :
    S.qSDDCore (fun a => S.R (A a)) (fun a => S.R (B a)) =
      S.qSDDCore (fun a => S.L (A a)) (fun a => S.L (B a)) :=
  Finset.sum_congr rfl fun a _ => by
    rw [S.rightTensor_sub, S.leftTensor_sub, S.rightTensor_conjTranspose,
      S.leftTensor_conjTranspose, S.rightTensor_mul_rightTensor, S.leftTensor_mul_leftTensor,
      S.ev_L_eq_ev_R]

/-- For a self-adjoint local operator `X`,
`ev((L X - R X)^* (L X - R X)) = 2 (ev L(X²) - ev(L X R X))`: the case `X = Y` of
`ev_star_L_sub_R_mul_self` (`SwitchSandwichMain/RightTransfer.lean`), the two squares having the
same expectation by swap symmetry (`S.ev_L_eq_ev_R`). -/
theorem ev_adjoint_self_leftTensor_sub_rightTensor (S : SymModel 𝔓 K) {X : 𝔓}
    (hX : IsSelfAdjoint X) :
    S.ev (star (S.L X - S.R X) * (S.L X - S.R X)) =
      2 * (S.ev (S.L (X * X)) - S.ev (S.opTensor X X)) := by
  rw [ev_star_L_sub_R_mul_self S hX hX, ← S.ev_L_eq_ev_R]
  unfold SymModel.opTensor
  ring

/-- The squared distance between the left and right lifts of a submeasurement is at most twice
its bipartite strong self-consistency defect. The vendored lemma asks for a
permutation-invariant state. -/
theorem qSDD_liftLeft_liftRight_le_two_qBipartiteSSCDefect {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (M : SubMeas Outcome 𝔓) :
    S.qSDD (M.liftLeft S) (M.liftRight S) ≤ 2 * S.qBipartiteSSCDefect M := by
  have hpt : ∀ a, S.ev (star (S.L (M.outcome a) - S.R (M.outcome a)) *
      (S.L (M.outcome a) - S.R (M.outcome a))) ≤
        2 * (S.ev (S.L (M.outcome a)) - S.ev (S.opTensor (M.outcome a) (M.outcome a))) := by
    intro a
    rw [ev_adjoint_self_leftTensor_sub_rightTensor S (.of_nonneg (M.outcome_pos a))]
    have := S.ev_mono _ _ (S.leftTensor_mono (sq_le_self (M.outcome_pos a) (M.outcome_le_one a)))
    linarith
  have hsum : S.qSDD (M.liftLeft S) (M.liftRight S) ≤
      2 * (S.ev (S.L M.total) - ∑ a, S.ev (S.opTensor (M.outcome a) (M.outcome a))) := by
    refine (Finset.sum_le_sum fun a _ => hpt a).trans_eq ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← S.ev_sum, S.leftTensor_finset_sum,
      M.sum_eq_total]
  exact hsum.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) zero_le_two)

/-- `prop:two-notions-of-self-consistency`.

If `A` is bipartite strongly self-consistent (`∑ₐ ev(Aₐ ⊗ I) − ∑ₐ ev(Aₐ ⊗ Aₐ) ≤ δ` on
average), then its left and right lifts are `2δ`-close. The vendored hypothesis is
`PermInvState ψ ∧ BipartiteSSCRel ψ 𝒟 A δ`; the first conjunct is a theorem of the model. -/
theorem twoNotionsOfSelfConsistency {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓) (δ : ℝ) :
    S.BipartiteSSCRel 𝒟 A δ →
      S.SDDRel 𝒟 (IdxSubMeas.liftLeft S A) (IdxSubMeas.liftRight S A) (2 * δ) := fun ⟨hssc⟩ =>
  ⟨calc S.sddError 𝒟 (IdxSubMeas.liftLeft S A) (IdxSubMeas.liftRight S A)
        ≤ avgOver 𝒟 (fun q => 2 * S.qBipartiteSSCDefect (A q)) :=
          avgOver_mono 𝒟 _ _ fun q =>
            qSDD_liftLeft_liftRight_le_two_qBipartiteSSCDefect S (A q)
      _ = 2 * S.bipartiteSSCError 𝒟 A := avgOver_const_mul 𝒟 2 _
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hssc zero_le_two⟩

end MIPRE.LIDT.Co.Preliminaries

end
