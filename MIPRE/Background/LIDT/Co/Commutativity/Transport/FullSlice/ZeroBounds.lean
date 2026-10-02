/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Transport/FullSlice/ZeroBounds.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Averages

@[expose] public section

/-!
# Zero-family bounds on the full-slice product

Pointwise `qSDDOp` bounds and averaged `SDDOpRel` bounds for the ordered `fullSliceProductLeft`
and reversed `fullSliceProductRight` factors against the zero family, each at most 1: the
counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/FullSlice/ZeroBounds.lean` in the
port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The vendored proofs repeat, once per factor order, a Kronecker computation of
`∑ (B_b A_a ⊗ I)^* (B_b A_a ⊗ I)` as the placed total of the sandwich `A_a B_b A_a`. Here
it is proved once in the local algebra and placed by `S.L`, as
`sum_ev_adjoint_self_leftTensor_mul_le_one` below, which the evaluated-slice bounds of
`Co/Commutativity/Main/Auxiliary/HEvalTransport.lean` use as well. The vendored hypothesis
`hnorm : strategy.state.IsNormalized` is dropped: it is a theorem of the model
(`VecState.ev_one_of_isNormalized`).

## New here

`sum_ev_adjoint_self_leftTensor_mul_le_one`: for submeasurements `A`, `B` of `𝔓` with `B`
projective, `∑_{a,b} ev((B_b A_a ⊗ I)^* (B_b A_a ⊗ I)) ≤ 1`.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel avgOver_uniform_le_const uniformDistribution)
open MIPStarRE.LDT.Commutativity (EvaluatedSliceQuestion FullSliceQuestion
  fullSliceQuestionOfEvaluatedSlice)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- For submeasurements `A`, `B` of the local algebra with `B` projective, the placed products
`B_b A_a ⊗ I` have total squared norm on the state at most `1`: the sum
`∑_{a,b} (B_b A_a)^* (B_b A_a)` is the total `∑_a A_a (∑_b B_b) A_a` of the sandwich
`sandwichByOuterSubMeas A B`, which is at most `1`. -/
theorem sum_ev_adjoint_self_leftTensor_mul_le_one {α β : Type*} [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (A : SubMeas α 𝔓) (B : SubMeas β 𝔓)
    (hB : ∀ b, B.outcome b * B.outcome b = B.outcome b) :
    ∑ a, ∑ b, S.ev (star (S.L (B.outcome b * A.outcome a)) * S.L (B.outcome b * A.outcome a))
      ≤ 1 := by
  have hsum : ∑ a, ∑ b,
      S.ev (star (S.L (B.outcome b * A.outcome a)) * S.L (B.outcome b * A.outcome a)) =
        S.ev (S.L (∑ ab : α × β, A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1)) := by
    rw [← S.leftTensor_finset_sum, S.ev_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [S.leftTensor_conjTranspose, S.leftTensor_mul_leftTensor, star_mul, A.outcome_hermitian,
      B.outcome_hermitian, mul_assoc, ← mul_assoc (B.outcome b), hB, ← mul_assoc]
  rw [hsum]
  exact (S.ev_mono _ _ (S.leftTensor_le_one ((sandwichByOuterSubMeas_sum_outcome A B).trans_le
    (sandwichByOuterSubMeas A B).total_le_one))).trans_eq S.ev_one_of_isNormalized

/-- Questionwise, the ordered full-slice product has squared distance at most `1`
from the zero family. -/
lemma fullSliceProductLeft_qSDDOp_zero_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : FullSliceQuestion params) :
    strategy.state.qSDDOp
      (fullSliceProductLeft params strategy family q)
      (zeroFullSliceOpFamily (R := K →L[ℂ] K) params) ≤ 1 := by
  let A := fullSliceFirstFactor params family q
  let B := fullSliceSecondFactor params family q
  refine le_of_eq_of_le ?_ (sum_ev_adjoint_self_leftTensor_mul_le_one strategy.state B A
    (family.meas q.1).proj)
  change ∑ gh : _ × _, strategy.state.ev
      (star (strategy.state.L (A.outcome gh.1 * B.outcome gh.2) - 0) *
        (strategy.state.L (A.outcome gh.1 * B.outcome gh.2) - 0)) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [sub_zero]

/-- Questionwise, the reversed full-slice product has squared distance at most `1`
from the zero family. -/
lemma zero_qSDDOp_fullSliceProductRight_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (q : FullSliceQuestion params) :
    strategy.state.qSDDOp
      (zeroFullSliceOpFamily (R := K →L[ℂ] K) params)
      (fullSliceProductRight params strategy family q) ≤ 1 := by
  let A := fullSliceFirstFactor params family q
  let B := fullSliceSecondFactor params family q
  refine le_of_eq_of_le ?_ (sum_ev_adjoint_self_leftTensor_mul_le_one strategy.state A B
    (family.meas q.2).proj)
  change ∑ gh : _ × _, strategy.state.ev
      (star (0 - strategy.state.L (B.outcome gh.2 * A.outcome gh.1)) *
        (0 - strategy.state.L (B.outcome gh.2 * A.outcome gh.1))) = _
  rw [Fintype.sum_prod_type]
  simp only [zero_sub, star_neg, neg_mul_neg]

/-- Averaging the ordered full-slice product against zero costs at most `1`. -/
lemma fullSliceProductLeft_to_zero_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) :
    strategy.state.SDDOpRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => fullSliceProductLeft params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (fun _ => zeroFullSliceOpFamily (R := K →L[ℂ] K) params)
      1 :=
  ⟨avgOver_uniform_le_const _ 1 fun q => fullSliceProductLeft_qSDDOp_zero_le_one params strategy
    family (fullSliceQuestionOfEvaluatedSlice params q)⟩

/-- Averaging zero against the reversed full-slice product costs at most `1`. -/
lemma zero_to_fullSliceProductRight_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (family : IdxPolyFamily params 𝔓) :
    strategy.state.SDDOpRel
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun _ => zeroFullSliceOpFamily (R := K →L[ℂ] K) params)
      (fun q => fullSliceProductRight params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      1 :=
  ⟨avgOver_uniform_le_const _ 1 fun q => zero_qSDDOp_fullSliceProductRight_le_one params strategy
    family (fullSliceQuestionOfEvaluatedSlice params q)⟩

end MIPRE.LIDT.Co.Commutativity

end
