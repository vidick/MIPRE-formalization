/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/ScalarApproximation/PaperChainBasic/Reindexing.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Scaffold.Products
public import MIPRE.Background.LIDT.Co.CommutativityPoints.Approximation

@[expose] public section

/-!
# Section 11 commutativity: reindexing utilities for the evaluated-slice paper chain

Finite-reindexing and evaluated-family identities used by the paper-faithful scalar
approximation chain: the counterpart of
`Commutativity/ScalarApproximation/PaperChainBasic/Reindexing.lean` under
`MIPRE/Background/LIDT/MIPStarRE/LDT/` in the port of `planning/c6b-plan.md` (milestone M7,
section "Port conventions").

The two evaluated-family identities are state-free and hold over any C*-algebra `𝔓` with its
order. `ev_leftTensor_mul_middle_finset_sum` takes the symmetric model `S` where the vendored
lemma takes the state `ψ`, in the same position, and is stated with `S.L` and `S.R`; its proof is
the keystone's `leftTensor_finset_sum` and `ev_finset_sum`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq appendPoint pointHeight)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The evaluated point family has the same total as the underlying slice
measurement `G` at the sampled height.

This unfolds `evaluatedPointFamily` as postprocessing of `family.meas y`; the
postprocessing total is unchanged, and `hG` identifies the slice with `G y`. -/
lemma evaluatedPointFamily_total_eq_G_total
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (u : Point params.next) :
    ((evaluatedPointFamily params family u).total) =
      (G (pointHeight params u)).total := by
  rw [hG]
  rfl

/-- Expand a finite sum in the middle factor of a left-register sandwich:
`⟨L(A (∑_x B_x) C R) R(D)⟩ = ∑_x ⟨L(A B_x C R) R(D)⟩`. -/
lemma ev_leftTensor_mul_middle_finset_sum
    {α : Type*} (s : Finset α)
    (S : SymModel 𝔓 K)
    (A C R D : 𝔓)
    (B : α → 𝔓) :
    S.ev (S.L (((A * (∑ x ∈ s, B x) * C) * R)) * S.R D) =
      ∑ x ∈ s, S.ev (S.L (((A * B x * C) * R)) * S.R D) := by
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, ← S.leftTensor_finset_sum, Finset.sum_mul,
    S.ev_finset_sum]

/-- Evaluating the slice family at an appended point is postprocessing the slice
measurement by the fiber `{g | g u = a}`. -/
lemma evaluatedPointFamily_appendPoint_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓)
    (G : Fq params → SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (u : Point params) (a : Fq params) :
    (evaluatedPointFamily params family (appendPoint params u x)).outcome a =
      ∑ g ∈ Finset.univ.filter (fun g : MIPStarRE.LDT.Polynomial params => g u = a),
        (G x).outcome g := by
  rw [hG]
  simp only [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
    SubMeas.postprocess_outcome, MIPStarRE.LDT.truncatePoint_appendPoint,
    MIPStarRE.LDT.pointHeight_appendPoint]

end MIPRE.LIDT.Co.Commutativity

end
