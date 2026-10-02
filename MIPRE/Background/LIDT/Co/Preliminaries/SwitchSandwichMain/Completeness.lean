/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/Completeness.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichMain.LeftTransfer
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichMain.RightTransfer
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichPrep.ApproxDelta

@[expose] public section

/-!
# Switch-sandwich main: completeness estimate

`prop:switch-sandwich` assembled from the left and right transfer steps, and
`prop:completeness-transfer-projective-P`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/Completeness.lean` in the
port of `planning/c6b-plan.md` (milestone M3, section "Port conventions").

`switchSandwich` takes a symmetric model `S : SymModel 𝔓 K` in place of the state
`ψ : QuantumState (ι × ι)`. The completeness transfer is about a state on a single space
(`ψ : QuantumState ι`), so `completenessTransfer_core` and `completenessTransferProjectiveP`
take a vector state `V : VecState K` (a symmetric model is accepted through its coercion) and
families of joint operators in `K →L[ℂ] K`, as `CompTransferStmt` does in
`Co/Preliminaries/Defs.lean`. All three drop the vendored normalization hypothesis
`hψ : ψ.IsNormalized`, a theorem of the vector state (`ev_one_of_isNormalized`); the
subprobability hypothesis `h𝒟` stays.

The proofs are the vendored ones. Per question, the mass gap of `A` against the projective `P`
is at most the diagonal gap `∑ₐ ev(Pₐ²) - ∑ₐ ev(Aₐ²)` (`projSubMeas_diagMass_eq_mass`,
`subMeas_diagMass_le_mass`), which the two overlap gaps (`question_overlap_gap_left`,
`question_overlap_gap_right`) bound by `2 √(qSDD A P)`; the average of the square roots is at
most the square root of the average (`avgOver_abs_le_sqrt_of_pointwise`).

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`,
  `prop:completeness-transfer-projective-P`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_sub avgOver_mono avgOver_const_mul)
open MIPStarRE.LDT.Preliminaries (avgOver_abs_le_sqrt_of_pointwise)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `prop:switch-sandwich`.

The paper proof assumes a normalized state and a probability distribution (weights summing to
`≤ 1`). Normalization is a theorem of the model; the distribution hypothesis is `h𝒟`. -/
theorem switchSandwich {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxProjSubMeas Question Outcome 𝔓)
    (B : 𝔓) (hB : OpBounded01 B)
    (δ : ℝ) :
    BipartiteSDDRel S 𝒟
      (IdxProjSubMeas.toIdxSubMeas A)
      (IdxProjSubMeas.toIdxSubMeas A) δ →
    SwitchSandwichStmt S 𝒟 A B δ := fun happrox =>
  { leftSandwichTransfer := switchSandwich_leftTransfer S 𝒟 h𝒟 A B hB δ happrox
    rightSandwichTransfer := switchSandwich_rightTransfer S 𝒟 h𝒟 A B hB δ happrox }

/-- Core of `prop:completeness-transfer-projective-P`: if `A ≈_ε P` with `P` projective, the
mass of `A` is at least that of `P` minus `2 √ε`. -/
theorem completenessTransfer_core {Question Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome (K →L[ℂ] K))
    (P : IdxProjSubMeas Question Outcome (K →L[ℂ] K)) (ε : ℝ) :
    V.sddError 𝒟 A
        (IdxProjSubMeas.toIdxSubMeas P) ≤ ε →
    V.idxSubMeasMass 𝒟 A ≥
      V.idxSubMeasMass 𝒟
        (IdxProjSubMeas.toIdxSubMeas P)
        - 2 * Real.sqrt ε := by
  intro hε
  have hgap : ∀ q, V.subMeasMass (P q).toSubMeas - V.subMeasMass (A q) ≤
      2 * Real.sqrt (V.qSDD (A q) (P q).toSubMeas) := by
    intro q
    have hP := projSubMeas_diagMass_eq_mass V (P q)
    have hA := subMeas_diagMass_le_mass V (A q)
    have hl := (abs_le.mp (question_overlap_gap_left V (A q) (P q).toSubMeas)).1
    have hr := (abs_le.mp (question_overlap_gap_right V (A q) (P q).toSubMeas)).1
    show V.ev (P q).total - V.ev (A q).total ≤ _
    linarith
  have hsqrt :
      avgOver 𝒟 (fun q => Real.sqrt (V.qSDD (A q) (P q).toSubMeas)) ≤
        Real.sqrt (V.sddError 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) :=
    (le_abs_self _).trans (avgOver_abs_le_sqrt_of_pointwise 𝒟 _ _
      (fun q => (abs_of_nonneg (Real.sqrt_nonneg _)).le) (fun q => V.qSDD_nonneg _ _) h𝒟)
  have htotal :
      V.idxSubMeasMass 𝒟 (IdxProjSubMeas.toIdxSubMeas P) - V.idxSubMeasMass 𝒟 A ≤
        2 * Real.sqrt ε := by
    show avgOver 𝒟 (fun q => V.subMeasMass (P q).toSubMeas) -
      avgOver 𝒟 (fun q => V.subMeasMass (A q)) ≤ _
    rw [← avgOver_sub]
    calc
      _ ≤ avgOver 𝒟 (fun q => 2 * Real.sqrt (V.qSDD (A q) (P q).toSubMeas)) :=
          avgOver_mono 𝒟 _ _ hgap
      _ = 2 * avgOver 𝒟 (fun q => Real.sqrt (V.qSDD (A q) (P q).toSubMeas)) :=
          avgOver_const_mul 𝒟 2 _
      _ ≤ 2 * Real.sqrt ε :=
          mul_le_mul_of_nonneg_left (hsqrt.trans (Real.sqrt_le_sqrt hε)) zero_le_two
  linarith

/-- `prop:completeness-transfer-projective-P`.

The paper proof uses a normalized state and a probability distribution. Normalization is a
theorem of the vector state; the distribution hypothesis is `h𝒟`. -/
theorem completenessTransferProjectiveP {Question Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome (K →L[ℂ] K))
    (P : IdxProjSubMeas Question Outcome (K →L[ℂ] K)) (ε : ℝ) :
    V.SDDRel 𝒟 A
        (IdxProjSubMeas.toIdxSubMeas P) ε →
      CompTransferStmt V 𝒟 A P ε := fun ⟨hε⟩ =>
  { completenessTransfer := completenessTransfer_core V 𝒟 h𝒟 A P ε hε }

end MIPRE.LIDT.Co.Preliminaries

end
