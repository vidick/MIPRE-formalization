/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/Transport/FullSlice/Machinery/Marginalization/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Transport.FullSlice.Averages
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery.Marginalization.Core

@[expose] public section

/-!
# Full-slice tensor marginalization core

Collision residuals, postprocessing expansions, and tensor marginalization core bounds for the
`BABA` and `ABAB` full-slice tensor averages: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Core.lean`
in the port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

The residuals and averages are real expectations `strategy.state.ev …` on the symmetric model of
a strategy `strategy : SymStrat params.next 𝔓 K`, the vendored `leftTensor (ι₂ := ι)` and
`rightTensor (ι₁ := ι)` being `strategy.state.L` and `strategy.state.R`. The vendored hypothesis
`hnorm : strategy.state.IsNormalized` is a theorem of the model and is dropped from
`fullSliceBABAxCollisionFactored_le_mdq`, `fullSliceABAByCollisionFactored_le_mdq`, the two
averaged collision bounds and `fullSliceBABA_tensor_marginalize_x`. The three finite-sum
expansions take the model `(S : SymModel 𝔓 K)` where the vendored ones take
`ψ : QuantumState (ι × ι)`, with the same argument order.

The two scalar finite-sum identities of the vendored file (the postprocessed indicator sum and
the diagonal pair sum) are classical and imported from the vendored file, which this file
imports alongside its mirrored import. The tensor-form machinery is internal to the
scalar/tensor comparison recorded upstream in `docs/decisions/713-scalar-tensor-decision.md`;
downstream code should use the scalar API of the full-slice transport theorems.

## Not ported

- `postprocess_collision_coeff_sum`: classical, imported.
- `diagonal_pair_sum`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver avgOver_congr avgOver_add avgOver_sum
  avgOver_mul_const avgOver_nonneg avgOver_uniform_const avgOver_uniform_le_const
  uniformDistribution)
open MIPStarRE.LDT.Commutativity (FullSliceQuestion postprocess_collision_coeff_sum
  diagonal_pair_sum)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Factored collision residual for the x-marginalization tensor step.

After expanding the first evaluated family in paper `eq:gcom4-diff`, the remaining
error is this nonnegative sum over pairs of distinct polynomial outcomes whose
values collide at the sampled point `u`. -/
noncomputable def fullSliceBABAxCollisionFactored
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (xy : FullSliceQuestion params) : ℝ :=
  let A : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 := (family.meas xy.1).toSubMeas
  let B : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 := (family.meas xy.2).toSubMeas
  ∑ gg : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
    ∑ h : MIPStarRE.LDT.Polynomial params,
      (if gg.1 = gg.2 then 0 else
        avgOver (uniformDistribution (Point params))
          (fun u => if gg.1 u = gg.2 u then (1 : ℝ) else 0)) *
        strategy.state.ev
          (strategy.state.L (B.outcome h * A.outcome gg.1 * B.outcome h) *
            strategy.state.R (A.outcome gg.2))

/-- The Schwartz-Zippel/PSD bound for the x-marginalization collision residual (the vendored
hypothesis `hnorm : strategy.state.IsNormalized` is a theorem of the model).

This is the proved hard estimate used by the staged x-marginalization tensor
lemma below.  The algebraic expansion identifies the x-evaluated tensor-average
difference with this residual averaged over `x,y`. -/
lemma fullSliceBABAxCollisionFactored_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (xy : FullSliceQuestion params) :
    fullSliceBABAxCollisionFactored params strategy family xy ≤
      (params.m * params.d : ℝ) / params.q :=
  Preliminaries.polynomialCollision_sandwichTensor_le_mdq params strategy.state
    (family.meas xy.2).toSubMeas (family.meas xy.1).toSubMeas (family.meas xy.1).toSubMeas

/-- Factored collision residual for the y-marginalization tensor step.

Here the outer sandwich is the already x-evaluated family
`G^x_[g(u)=a]`, while the colliding polynomial pair is on the `y` side. -/
noncomputable def fullSliceABAByCollisionFactored
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (u : Point params) (xy : FullSliceQuestion params) : ℝ :=
  let A : SubMeas (Fq params) 𝔓 := evaluateAt params u ((family.meas xy.1).toSubMeas)
  let B : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓 := (family.meas xy.2).toSubMeas
  ∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params, ∑ a : Fq params,
    (if hh.1 = hh.2 then 0 else
      avgOver (uniformDistribution (Point params))
        (fun v => if hh.1 v = hh.2 v then (1 : ℝ) else 0)) *
      strategy.state.ev
        (strategy.state.L (A.outcome a * B.outcome hh.1 * A.outcome a) *
          strategy.state.R (B.outcome hh.2))

/-- The Schwartz-Zippel/PSD bound for the y-marginalization collision residual (the vendored
hypothesis `hnorm : strategy.state.IsNormalized` is a theorem of the model).

This is the proved hard estimate used by the staged y-marginalization tensor
lemma below; the postprocessing expansion identifies the data-ordered evaluated
tensor-average difference with `fullSliceABAByCollisionFactored`. -/
lemma fullSliceABAByCollisionFactored_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (u : Point params) (xy : FullSliceQuestion params) :
    fullSliceABAByCollisionFactored params strategy family u xy ≤
      (params.m * params.d : ℝ) / params.q :=
  Preliminaries.polynomialCollision_sandwichTensor_le_mdq params strategy.state
    (evaluateAt params u ((family.meas xy.1).toSubMeas)) (family.meas xy.2).toSubMeas
    (family.meas xy.2).toSubMeas

/-- Averaged x-collision bound in the form consumed by
`fullSliceBABA_tensor_marginalize_x` (the vendored hypothesis `hnorm` is a theorem of the
model). -/
lemma fullSliceBABA_tensor_marginalize_x_collision_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) ≤
      (params.m * params.d : ℝ) / params.q :=
  avgOver_uniform_le_const _ _ fun xy =>
    fullSliceBABAxCollisionFactored_le_mdq params strategy family xy

/-- Averaged y-collision bound in the form consumed by
`fullSliceABAB_tensor_marginalize_y` (the vendored hypothesis `hnorm` is a theorem of the
model). This is the y-side analogue of `fullSliceBABA_tensor_marginalize_x_collision_bound`. -/
lemma fullSliceABAB_tensor_marginalize_y_collision_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) ≤
      (params.m * params.d : ℝ) / params.q :=
  avgOver_uniform_le_const _ _ fun ux =>
    fullSliceABAByCollisionFactored_le_mdq params strategy family ux.1 ux.2

/-- Expand the expectation of a tensor sandwich whose inner/right family is an
indicator-restricted finite sum. -/
lemma ev_sandwichTensor_indicator_expand
    {α : Type*} [Fintype α]
    (S : SymModel 𝔓 K) (B : 𝔓) (A : α → 𝔓)
    (p : α → Prop) [DecidablePred p] :
    S.ev
      (S.L (B * (∑ a : α, if p a then A a else 0) * B) *
        S.R (∑ a : α, if p a then A a else 0)) =
      ∑ aa : α × α,
        (if p aa.1 then if p aa.2 then (1 : ℝ) else 0 else 0) *
          S.ev (S.L (B * A aa.1 * B) * S.R (A aa.2)) := by
  have hleft : S.L (B * (∑ a : α, if p a then A a else 0) * B) =
      ∑ a : α, if p a then S.L (B * A a * B) else 0 := by
    have hloc : B * (∑ a : α, if p a then A a else 0) * B =
        ∑ a : α, if p a then B * A a * B else 0 := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Fintype.sum_congr _ _ fun a => by split_ifs <;> simp only [mul_zero, zero_mul]
    rw [hloc, ← S.leftTensor_finset_sum]
    exact Fintype.sum_congr _ _ fun a => by split_ifs; exacts [rfl, S.L.map_zero]
  have hright : S.R (∑ a : α, if p a then A a else 0) =
      ∑ a : α, if p a then S.R (A a) else 0 := by
    rw [← S.rightTensor_finset_sum]
    exact Fintype.sum_congr _ _ fun a => by split_ifs; exacts [rfl, S.R.map_zero]
  rw [hleft, hright, Finset.sum_mul_sum, S.ev_sum, Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun a₁ => ?_
  rw [S.ev_sum]
  refine Fintype.sum_congr _ _ fun a₂ => ?_
  split_ifs
  · rw [one_mul]
  all_goals simp only [mul_zero, zero_mul, S.ev_zero]

/-- Expand a postprocessed tensor sandwich into the pair-collision expression for
one fixed sample. -/
lemma postprocess_sandwichTensor_expand
    {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ] [DecidableEq κ]
    (S : SymModel 𝔓 K)
    (A : SubMeas α 𝔓) (B : SubMeas β 𝔓) (f : α → κ) :
    (∑ k : κ, ∑ b : β,
      S.ev
        (S.L (B.outcome b * (postprocess A f).outcome k * B.outcome b) *
          S.R ((postprocess A f).outcome k))) =
    (∑ aa : α × α, ∑ b : β,
      (if f aa.1 = f aa.2 then (1 : ℝ) else 0) *
        S.ev (S.L (B.outcome b * A.outcome aa.1 * B.outcome b) * S.R (A.outcome aa.2))) := by
  have hpost (k : κ) :
      (postprocess A f).outcome k = ∑ a : α, if f a = k then A.outcome a else 0 := by
    rw [SubMeas.postprocess_outcome, Finset.sum_filter]
  calc
    _ = ∑ b : β, ∑ aa : α × α, ∑ k : κ,
          (if f aa.1 = k then if f aa.2 = k then (1 : ℝ) else 0 else 0) *
            S.ev (S.L (B.outcome b * A.outcome aa.1 * B.outcome b) *
              S.R (A.outcome aa.2)) := by
        rw [Finset.sum_comm]
        refine Fintype.sum_congr _ _ fun b => ?_
        rw [Finset.sum_comm]
        refine Fintype.sum_congr _ _ fun k => ?_
        rw [hpost]
        exact ev_sandwichTensor_indicator_expand S (B.outcome b) A.outcome (fun a => f a = k)
    _ = _ := by
        rw [Finset.sum_comm]
        refine Fintype.sum_congr _ _ fun aa => Fintype.sum_congr _ _ fun b => ?_
        rw [← Finset.sum_mul, postprocess_collision_coeff_sum f aa.1 aa.2]

/-- Expand one postprocessed tensor sandwich and split the resulting pair sum into
its diagonal part and off-diagonal collision residual.

This is the common finite-sum identity behind both tensor marginalization steps.
The outcome family `A` is postprocessed by the sample-dependent map `eval s`; the
outer sandwich family `B` is not postprocessed. -/
lemma avg_postprocess_sandwichTensor_eq_diag_add_collision
    {α β σ κ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β]
    [Fintype σ] [DecidableEq σ] [Nonempty σ]
    [Fintype κ] [DecidableEq κ]
    (S : SymModel 𝔓 K)
    (A : SubMeas α 𝔓) (B : SubMeas β 𝔓) (eval : σ → α → κ) :
    avgOver (uniformDistribution σ)
        (fun s => ∑ k : κ, ∑ b : β,
          S.ev
            (S.L (B.outcome b * (postprocess A (eval s)).outcome k * B.outcome b) *
              S.R ((postprocess A (eval s)).outcome k))) =
      (∑ a : α, ∑ b : β,
          S.ev (S.L (B.outcome b * A.outcome a * B.outcome b) * S.R (A.outcome a))) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else
            avgOver (uniformDistribution σ)
              (fun s => if eval s aa.1 = eval s aa.2 then (1 : ℝ) else 0)) *
            S.ev
              (S.L (B.outcome b * A.outcome aa.1 * B.outcome b) * S.R (A.outcome aa.2)) := by
  let T : α × α → β → ℝ := fun aa b =>
    S.ev (S.L (B.outcome b * A.outcome aa.1 * B.outcome b) * S.R (A.outcome aa.2))
  let c : α × α → ℝ := fun aa =>
    avgOver (uniformDistribution σ) (fun s => if eval s aa.1 = eval s aa.2 then (1 : ℝ) else 0)
  calc
    _ = avgOver (uniformDistribution σ) (fun s => ∑ aa : α × α, ∑ b : β,
          (if eval s aa.1 = eval s aa.2 then (1 : ℝ) else 0) * T aa b) :=
        avgOver_congr _ _ _ fun s => postprocess_sandwichTensor_expand S A B (eval s)
    _ = ∑ aa : α × α, ∑ b : β, c aa * T aa b := by
        rw [avgOver_sum]
        refine Fintype.sum_congr _ _ fun aa => ?_
        rw [avgOver_sum]
        exact Fintype.sum_congr _ _ fun b => avgOver_mul_const _ _ _
    _ = (∑ aa : α × α, ∑ b : β, (if aa.1 = aa.2 then (1 : ℝ) else 0) * T aa b) +
          ∑ aa : α × α, ∑ b : β, (if aa.1 = aa.2 then 0 else c aa) * T aa b := by
        simp only [← Finset.sum_add_distrib, ← add_mul]
        refine Fintype.sum_congr _ _ fun aa => Fintype.sum_congr _ _ fun b => ?_
        obtain ⟨a₁, a₂⟩ := aa
        by_cases h : a₁ = a₂
        · subst h
          simp [c, avgOver_uniform_const]
        · simp [h]
    _ = _ := by rw [diagonal_pair_sum]

/-- The x-collision residual is nonnegative term-by-term. -/
lemma fullSliceBABAxCollisionFactored_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (xy : FullSliceQuestion params) :
    0 ≤ fullSliceBABAxCollisionFactored params strategy family xy :=
  Finset.sum_nonneg fun gg _ => Finset.sum_nonneg fun h _ =>
    mul_nonneg
      (by
        split_ifs
        · exact le_rfl
        · exact avgOver_nonneg _ _ fun u => by split_ifs <;> norm_num)
      (strategy.state.sandwichTensorSummand_nonneg (family.meas xy.2).toSubMeas
        (family.meas xy.1).toSubMeas (family.meas xy.1).toSubMeas h gg.1 gg.2)

/-- The y-collision residual is nonnegative term-by-term. -/
lemma fullSliceABAByCollisionFactored_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (u : Point params) (xy : FullSliceQuestion params) :
    0 ≤ fullSliceABAByCollisionFactored params strategy family u xy :=
  Finset.sum_nonneg fun hh _ => Finset.sum_nonneg fun a _ =>
    mul_nonneg
      (by
        split_ifs
        · exact le_rfl
        · exact avgOver_nonneg _ _ fun v => by split_ifs <;> norm_num)
      (strategy.state.sandwichTensorSummand_nonneg
        (evaluateAt params u ((family.meas xy.1).toSubMeas)) (family.meas xy.2).toSubMeas
        (family.meas xy.2).toSubMeas a hh.1 hh.2)

/-- Exact x-side postprocessing identity: the x-evaluated `BAB ⊗ A` tensor
average is the full tensor average plus the x-collision residual. -/
lemma fullSliceBABAtensor_xEvaluation_eq_full_add_collision
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    xEvaluatedSliceBABAtensorAvg params strategy family =
      fullSliceBABAtensorAvg params strategy family +
        avgOver (uniformDistribution (FullSliceQuestion params))
          (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) := by
  rw [fullSliceBABAtensorAvg, ← avgOver_add]
  refine avgOver_congr _ _ _ fun xy => ?_
  refine (avg_postprocess_sandwichTensor_eq_diag_add_collision strategy.state
    (family.meas xy.1).toSubMeas (family.meas xy.2).toSubMeas
    (fun (u : Point params) (g : MIPStarRE.LDT.Polynomial params) => g u)).trans ?_
  exact congrArg (· + _) (Fintype.sum_prod_type' _).symm

/-- X-side tensor marginalization bound for paper `eq:gcom4-diff` (the vendored hypothesis
`hnorm : strategy.state.IsNormalized` is a theorem of the model).

This staged statement compares the full `BAB ⊗ A` tensor average to the
intermediate where only the `x` polynomial outcome has been evaluated at `u`.
It is the Lean-local tensor form of the Schwartz-Zippel step labelled
`eq:gcom4-diff` in the proof of blueprint theorem `thm:com-main`. -/
lemma fullSliceBABA_tensor_marginalize_x
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K) (family : IdxPolyFamily params 𝔓) :
    |fullSliceBABAtensorAvg params strategy family -
        xEvaluatedSliceBABAtensorAvg params strategy family| ≤
      (params.m * params.d : ℝ) / params.q := by
  rw [fullSliceBABAtensor_xEvaluation_eq_full_add_collision, sub_add_cancel_left, abs_neg,
    abs_of_nonneg (avgOver_nonneg _ _ fun xy =>
      fullSliceBABAxCollisionFactored_nonneg params strategy family xy)]
  exact fullSliceBABA_tensor_marginalize_x_collision_bound params strategy family

end MIPRE.LIDT.Co.Commutativity

end
