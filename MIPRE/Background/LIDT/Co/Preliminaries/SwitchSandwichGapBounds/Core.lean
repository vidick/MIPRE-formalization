/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/SwitchSandwichGapBounds/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichPrep.Core

@[expose] public section

/-!
# Switch-sandwich gap bounds: Cauchy–Schwarz core

Shared Cauchy–Schwarz contraction used in both the left and middle gap estimates of the
switch-sandwich argument: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SwitchSandwichGapBounds/Core.lean` in the port
of `planning/c6b-plan.md` (milestone M3, section "Port conventions").

The lemma uses a single state and joint operators, so it takes a vector state `V : VecState K`
(a symmetric model is accepted through its coercion) and operators in `K →L[ℂ] K`; `ᴴ` becomes
`star`. The proof is the vendored one: Cauchy–Schwarz termwise (`V.ev_abs_mul_le_sqrt`), then
over the outcomes (`Real.sum_sqrt_mul_sqrt_le`), and the contraction `LB * LB ≤ 1` conjugated by
`Y a` (`IsSelfAdjoint.conjugate_le_conjugate`, then `V.ev_mono`).

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Cauchy-Schwarz contraction used in both switch-sandwich gap estimates:
`|∑ₐ ev (Xₐ LB Yₐ)| ≤ √(∑ₐ ev (Xₐ Xₐ)) √(∑ₐ ev (Yₐ* Yₐ))` for self-adjoint `Xₐ`, `Yₐ` and a
self-adjoint contraction `LB`. -/
theorem sum_ev_mul_leftBounded_le_of_leftHermitian
    {Outcome : Type*} [Fintype Outcome]
    (V : VecState K)
    (LB : K →L[ℂ] K)
    (X Y : Outcome → K →L[ℂ] K)
    (hLB_herm : star LB = LB)
    (hLB_sq_le_one : LB * LB ≤ 1)
    (hXherm : ∀ a, star (X a) = X a)
    (hYherm : ∀ a, star (Y a) = Y a) :
    |∑ a : Outcome, V.ev (X a * (LB * Y a))| ≤
      Real.sqrt (∑ a : Outcome, V.ev (X a * X a)) *
        Real.sqrt (∑ a : Outcome, V.ev (star (Y a) * Y a)) := by
  have hX : ∀ a, 0 ≤ V.ev (X a * X a) := fun a => by
    simpa only [hXherm a] using V.ev_adjoint_self_nonneg (X a)
  have hLY : ∀ a, V.ev (star (LB * Y a) * (LB * Y a)) ≤ V.ev (star (Y a) * Y a) := fun a => by
    have hsand : Y a * (LB * LB) * Y a ≤ Y a * 1 * Y a :=
      IsSelfAdjoint.conjugate_le_conjugate hLB_sq_le_one (hYherm a)
    rw [star_mul, hLB_herm, hYherm a]
    simpa only [mul_assoc, one_mul] using V.ev_mono _ _ hsand
  calc
    |∑ a : Outcome, V.ev (X a * (LB * Y a))|
      ≤ ∑ a : Outcome, |V.ev (X a * (LB * Y a))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Outcome,
          Real.sqrt (V.ev (X a * X a)) * Real.sqrt (V.ev (star (Y a) * Y a)) :=
        Finset.sum_le_sum fun a _ => by
          have h := V.ev_abs_mul_le_sqrt (X a) (LB * Y a)
          rw [hXherm a] at h
          exact h.trans
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hLY a)) (Real.sqrt_nonneg _))
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le _ hX fun a => V.ev_adjoint_self_nonneg (Y a)

end MIPRE.LIDT.Co.Preliminaries

end
