/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/LeftTransfer.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichGapBounds.Left
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichGapBounds.Middle
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichPrep.InnerProduct

@[expose] public section

/-!
# Switch-sandwich main: left-to-middle transfer

The left-to-middle transfer estimate used in `prop:switch-sandwich`, bounding the gap between
the left and middle expressions via the Cauchy–Schwarz-based gap bounds: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/LeftTransfer.lean` in the
port of `planning/c6b-plan.md` (milestone M3, section "Port conventions").

The state `ψ : QuantumState (ι × ι)` becomes a symmetric model `S : SymModel 𝔓 K` and the
placements `leftTensor`, `rightTensor` become `S.L`, `S.R`. The vendored normalization
hypothesis `hψ : ψ.IsNormalized` is dropped: it is a theorem of the model
(`ev_one_of_isNormalized`), and the gap bounds `question_switchSandwich_left_gap` and
`question_switchSandwich_middle_gap` no longer take it. The proof is the vendored one: both gaps
through the intermediate term `E_x ∑ₐ ev(Aₐ B ⊗ Aₐ)`, each averaged by
`avgOver_abs_le_sqrt_of_pointwise`, and the triangle inequality.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_sub)
open MIPStarRE.LDT.Preliminaries (avgOver_abs_le_sqrt_of_pointwise)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Left-to-middle transfer estimate used in the switch-sandwich theorem:
`|E_x ∑ₐ ev(Aₐ B Aₐ ⊗ I) - E_x ∑ₐ ev(B ⊗ Aₐ)| ≤ 2√δ` when `A ⊗ I ≈_δ I ⊗ A`. -/
theorem switchSandwich_leftTransfer
    {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxProjSubMeas Question Outcome 𝔓)
    (B : 𝔓) (hB : OpBounded01 B)
    (δ : ℝ) :
    BipartiteSDDRel S 𝒟
      (IdxProjSubMeas.toIdxSubMeas A)
      (IdxProjSubMeas.toIdxSubMeas A) δ →
    |leftSandwichExpectation S 𝒟 A B -
      middleSandwichExpectation S 𝒟 A B| ≤
      2 * Real.sqrt δ := by
  intro happrox
  have hδ :
      avgOver 𝒟
        (fun q => S.qSDD ((A q).toSubMeas.liftLeft S) ((A q).toSubMeas.liftRight S)) ≤ δ :=
    happrox.leftRightSquaredDistanceBound
  have hsdd : ∀ q, 0 ≤ S.qSDD ((A q).toSubMeas.liftLeft S) ((A q).toSubMeas.liftRight S) :=
    fun q => S.qSDD_nonneg _ _
  have hleft_gap :
      |leftSandwichExpectation S 𝒟 A B -
        avgOver 𝒟 (fun q => ∑ a, S.ev (S.L ((A q).outcome a) * S.L B * S.R ((A q).outcome a)))|
        ≤ Real.sqrt δ := by
    rw [leftSandwichExpectation, ← avgOver_sub]
    exact (avgOver_abs_le_sqrt_of_pointwise 𝒟 _ _
      (fun q => question_switchSandwich_left_gap S (A q) B hB) hsdd h𝒟).trans
      (Real.sqrt_le_sqrt hδ)
  have hmiddle_gap :
      |avgOver 𝒟 (fun q => ∑ a, S.ev (S.L ((A q).outcome a) * S.L B * S.R ((A q).outcome a))) -
        middleSandwichExpectation S 𝒟 A B| ≤ Real.sqrt δ := by
    rw [middleSandwichExpectation, ← avgOver_sub]
    exact (avgOver_abs_le_sqrt_of_pointwise 𝒟 _ _
      (fun q => question_switchSandwich_middle_gap S (A q) B hB) hsdd h𝒟).trans
      (Real.sqrt_le_sqrt hδ)
  exact (abs_sub_le _ _ _).trans ((add_le_add hleft_gap hmiddle_gap).trans_eq (two_mul _).symm)

end MIPRE.LIDT.Co.Preliminaries

end
