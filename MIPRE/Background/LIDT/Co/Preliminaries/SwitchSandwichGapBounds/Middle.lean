/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/SwitchSandwichGapBounds/Middle.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichGapBounds.Core

@[expose] public section

/-!
# Switch-sandwich gap bounds: middle gap

The middle gap estimate `question_switchSandwich_middle_gap`, bounding the question-level middle
gap of the switch-sandwich argument: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SwitchSandwichGapBounds/Middle.lean` in the
port of `planning/c6b-plan.md` (milestone M3, section "Port conventions").

The state `ψ : QuantumState (ι × ι)` becomes a symmetric model `S : SymModel 𝔓 K`, the
placements `leftTensor`, `rightTensor` become `S.L`, `S.R`, and the lifts
`A.toSubMeas.liftLeft`, `A.toSubMeas.liftRight` take the model, `A.toSubMeas.liftLeft S`. The
vendored normalization hypothesis `hψ : ψ.IsNormalized` is dropped: it is a theorem of the model
(`ev_one_of_isNormalized`), used through `subMeas_diagMass_le_one`. The proof is the vendored
one; the Kronecker identities it uses become the commutation of the placements
(`S.L_comm_R`) and the multiplicativity of `S.R` (`S.rightTensor_mul_rightTensor`).

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The question-level middle gap of the switch sandwich:
`|∑ₐ ev(Aₐ B ⊗ Aₐ) - ∑ₐ ev(B ⊗ Aₐ)| ≤ √(qSDD (A ⊗ 1) (1 ⊗ A))` for a projective
sub-measurement `A` and `0 ≤ B ≤ 1`. -/
theorem question_switchSandwich_middle_gap
    {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A : ProjSubMeas Outcome 𝔓)
    (B : 𝔓) (hB : OpBounded01 B) :
    |(∑ a : Outcome, S.ev (S.L (A.outcome a) * S.L B * S.R (A.outcome a))) -
      ∑ a : Outcome, S.ev (S.L B * S.R (A.outcome a))| ≤
      Real.sqrt (S.qSDD (A.toSubMeas.liftLeft S) (A.toSubMeas.liftRight S)) := by
  have hLB := leftTensor_opBounded01 S hB
  have hLA : ∀ a, star (S.L (A.outcome a)) = S.L (A.outcome a) := fun a =>
    (IsSelfAdjoint.of_nonneg (S.leftTensor_nonneg (A.outcome_pos a))).star_eq
  have hRA : ∀ a, star (S.R (A.outcome a)) = S.R (A.outcome a) := fun a =>
    (IsSelfAdjoint.of_nonneg (S.rightTensor_nonneg (A.outcome_pos a))).star_eq
  have hD : ∀ a, star (S.L (A.outcome a) - S.R (A.outcome a)) =
      S.L (A.outcome a) - S.R (A.outcome a) := fun a => by
    rw [star_sub, hLA, hRA]
  have hrewrite :
      (∑ a : Outcome, S.ev (S.L (A.outcome a) * S.L B * S.R (A.outcome a))) -
        ∑ a : Outcome, S.ev (S.L B * S.R (A.outcome a)) =
      ∑ a : Outcome,
        S.ev ((S.L (A.outcome a) - S.R (A.outcome a)) * (S.L B * S.R (A.outcome a))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← S.ev_sub, sub_mul, ← mul_assoc (S.R _), ← (S.L_comm_R B (A.outcome a)).eq,
      mul_assoc (S.L B), S.rightTensor_mul_rightTensor, A.proj a, mul_assoc]
  have hdiag : ∑ a : Outcome, S.ev (star (S.R (A.outcome a)) * S.R (A.outcome a)) ≤ 1 := by
    simp only [hRA]
    exact subMeas_diagMass_le_one S.toVecState (A.toSubMeas.liftRight S)
  rw [hrewrite]
  refine (sum_ev_mul_leftBounded_le_of_leftHermitian S.toVecState (S.L B)
    (fun a => S.L (A.outcome a) - S.R (A.outcome a)) (fun a => S.R (A.outcome a))
    (opBounded01_hermitian hLB) (opBounded01_sq_le_one hLB) hD hRA).trans ?_
  refine (mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr hdiag)).trans_eq ?_
  show _ = Real.sqrt (∑ a : Outcome,
    S.ev (star (S.L (A.outcome a) - S.R (A.outcome a)) * (S.L (A.outcome a) - S.R (A.outcome a))))
  simp only [hD]

end MIPRE.LIDT.Co.Preliminaries

end
