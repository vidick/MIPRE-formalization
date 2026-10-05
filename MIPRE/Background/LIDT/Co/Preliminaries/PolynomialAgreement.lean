/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/PolynomialAgreement.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.TensorPlacement
public import MIPStarRE.LDT.Preliminaries.PolynomialAgreement

@[expose] public section

/-!
# Polynomial agreement bound (Step 5 hammer)

The tensor-form Schwartz–Zippel collision bound used in the `mainFormal` self-consistency
cascade and in `comMain`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/PolynomialAgreement.lean` in the port of
`planning/c6b-plan.md` (milestone M3, section "Port conventions").

The classical half of the vendored file, the transport between coded points and the scalar
model and the scalar Schwartz–Zippel bounds `polynomialAgreement_avg_le_mdq` and
`axisLinePolynomialAgreement_avg_le_mdq`, is not ported: this file imports the vendored file and
names those declarations through an explicit `open MIPStarRE.LDT.Preliminaries (…)` list.

The declarations live in `MIPRE.LIDT.Co.Preliminaries`, as in `Co/Preliminaries/Defs.lean`, with
the symmetric model `S : SymModel 𝔓 K` an ordinary explicit argument in place of the vendored
state `ψ : QuantumState (ιA × ιB)`. Both registers carry the local algebra `𝔓`, so the vendored
carriers `ιA`, `ιB` become `𝔓`, and the vendored placements `leftTensor (ι₂ := ιB)`,
`rightTensor (ι₁ := ιA)` are `S.L`, `S.R`. The normalization hypothesis `hnorm : ψ.IsNormalized`
is dropped: it is a theorem of the model (`VecState.ev_one_of_isNormalized`), and the residual
bound `SymModel.sandwichTensor_residual_sum_le_one` of `Co/Basic/TensorPlacement.lean` does not
take it.

## Not ported

- `pointScalarEquiv`: classical, imported.
- `polynomialAgreement_avg_eq_scalarDomain`: classical, imported.
- `polynomialAgreement_avg_le_mdq`: classical, imported.
- `axisLinePolynomialAgreement_avg_eq_scalarDomain`: classical, imported.
- `axisLinePolynomialAgreement_avg_le_mdq`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`, lines 119–133
- `references/ldt-paper/commutativity-G.tex`
- `references/ldt-paper/preliminaries.tex`, Section 3
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Parameters FieldModel Point avgOver uniformDistribution)
open MIPStarRE.LDT.Preliminaries (polynomialAgreement_avg_le_mdq)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open Classical in
/-- Tensor-form Schwartz-Zippel collision bound.

For each off-diagonal pair of polynomial outcomes, the point-collision
coefficient is bounded by `params.m * params.d / params.q` via
`polynomialAgreement_avg_le_mdq`. The remaining tensor residual is bounded by
`1` using `sandwichTensor_residual_sum_le_one`, so the whole nonnegative
collision sum has the same `m d / q` bound (the vendored hypothesis `hnorm : ψ.IsNormalized`
is a theorem of the model). -/
theorem polynomialCollision_sandwichTensor_le_mdq {β : Type*} [Fintype β]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (Outer : SubMeas β 𝔓)
    (Inner : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (Right : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ gg : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params, ∑ o : β,
        (if gg.1 = gg.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : ℝ) else 0)) *
          S.ev
            (S.L (Outer.outcome o * Inner.outcome gg.1 * Outer.outcome o) *
              S.R (Right.outcome gg.2))) ≤
      (params.m * params.d : ℝ) / params.q := by
  set δ : ℝ := (params.m * params.d : ℝ) / params.q
  have hδ_nonneg : 0 ≤ δ := by positivity
  have hcoef_le (gg : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params) :
      (if gg.1 = gg.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : ℝ) else 0)) ≤ δ := by
    split_ifs with hEq
    · exact hδ_nonneg
    · exact polynomialAgreement_avg_le_mdq params gg.1 gg.2 hEq
  calc
    _ ≤ ∑ gg : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params, ∑ o : β,
          δ * S.ev
            (S.L (Outer.outcome o * Inner.outcome gg.1 * Outer.outcome o) *
              S.R (Right.outcome gg.2)) :=
        Finset.sum_le_sum fun gg _ => Finset.sum_le_sum fun o _ =>
          mul_le_mul_of_nonneg_right (hcoef_le gg)
            (S.sandwichTensorSummand_nonneg Outer Inner Right o gg.1 gg.2)
    _ = δ * (∑ gg : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
          ∑ o : β,
            S.ev
              (S.L (Outer.outcome o * Inner.outcome gg.1 * Outer.outcome o) *
                S.R (Right.outcome gg.2))) := by
        simp only [Finset.mul_sum]
    _ ≤ δ * 1 :=
        mul_le_mul_of_nonneg_left (S.sandwichTensor_residual_sum_le_one Outer Inner Right)
          hδ_nonneg
    _ = δ := mul_one δ

open Classical in
/-- The off-diagonal polynomial-collision mass used in `mainFormal` Step 5.

This is the weighted collision term in `inductive_step.tex` lines 122--127:
for every distinct pair of full polynomial outcomes `(g, h)`, the coefficient is
`Pr_u[g(u) = h(u)]`, and the quantum weight is the fixed cross-register mass
`⟨ψ | G^A_g ⊗ G^B_h | ψ⟩`, here `S.ev (S.opTensor (G^A_g) (G^B_h))`. -/
noncomputable def polynomialCollisionMass
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (Left Right : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : ℝ :=
  ∑ gg : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
    (if gg.1 = gg.2 then 0 else
      avgOver (uniformDistribution (Point params))
        (fun u => if gg.1 u = gg.2 u then (1 : ℝ) else 0)) *
      S.ev (S.opTensor (Left.outcome gg.1) (Right.outcome gg.2))

/-- `mainFormal` Step 5's tensor-valued Schwartz--Zippel loss.

This is the specialization of `polynomialCollision_sandwichTensor_le_mdq` with
no outer sandwich. It supplies exactly the paper's line-126 estimate for the
collision term after the evaluated self-consistency defect has been expanded (the vendored
hypothesis `hnorm : ψ.IsNormalized` is a theorem of the model). -/
theorem polynomialCollisionMass_le_mdq
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (Left Right : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    polynomialCollisionMass params S Left Right ≤
      (params.m * params.d : ℝ) / params.q := by
  have h := polynomialCollision_sandwichTensor_le_mdq params S
    (SubMeas.singleOutcome (1 : 𝔓) zero_le_one le_rfl) Left Right
  simpa only [polynomialCollisionMass, SubMeas.singleOutcome_outcome, one_mul, mul_one,
    Fintype.sum_unique] using h

end MIPRE.LIDT.Co.Preliminaries

end
