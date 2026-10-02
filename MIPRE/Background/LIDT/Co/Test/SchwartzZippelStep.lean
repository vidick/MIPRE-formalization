/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Test/SchwartzZippelStep.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Test.Defs
public import MIPRE.Background.LIDT.Co.Preliminaries.PolynomialAgreement

@[expose] public section

/-!
# `mainFormal` Step 5 — Schwartz--Zippel self-consistency handoff

The paper's Step 5 bridge (`references/ldt-paper/inductive_step.tex`, lines 119--133): the
algebraic expansion and reindexing from evaluated consistency to the full-polynomial
consistency defect, the genuinely Schwartz--Zippel part being the tensor bound
`Preliminaries.polynomialCollisionMass_le_mdq`. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/SchwartzZippelStep.lean` in the port of
`planning/c6b-plan.md` (milestone M4, section "Port conventions").

The declarations live in `MIPRE.LIDT.Co.Test`, with the symmetric model `S : SymModel 𝔓 K` an
ordinary explicit argument in place of the vendored state `ψ : QuantumState (ιA × ιB)`, as in
`Co/Preliminaries/PolynomialAgreement.lean`; the bipartite quantities are the `SymModel`
declarations of `Co/Test/Defs.lean` (`S.qBipartiteMatchMass`, `S.qBipartiteConsDefect`,
`S.bipartiteConsError`, `S.ConsRel`). Both registers carry the local algebra `𝔓`, so the vendored
carriers `ιA`, `ιB` become `𝔓`. The normalization hypothesis `hnorm : ψ.IsNormalized` of the two
Step 5 theorems is dropped: it is a theorem of the model, and
`Preliminaries.polynomialCollisionMass_le_mdq` does not take it.

`mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous` is therefore narrowed to one
carrier, and has the type of `mainFormalStep5_selfConsistency_ofExpansionBound`. Its vendored
caller, on the two-space `ProjStrat` of `Test/MainTheorem/SourceRoleRegister/Core.lean`, is left
to M13 and M14 (`planning/c6b-plan.md`, "Same-space and bipartite quantities"), as for the
heterogeneous triangle lemmas of `Co/Preliminaries/Triangles`.

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

namespace Test

open MIPStarRE.LDT (Parameters FieldModel Point avgOver uniformDistribution avgOver_add
  avgOver_mono avgOver_sum avgOver_mul_const avgOver_congr avgOver_zero avgOver_uniform_const)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open Classical in
/-- The matching mass of two postprocessed submeasurements, expanded as a sum over pairs of
original outcomes `(a, a')` whose readouts agree. -/
theorem qBipartiteMatchMass_postprocess_eq_pair_sum
    {α β : Type*} [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (A B : SubMeas α 𝔓) (f : α → β) :
    S.qBipartiteMatchMass (postprocess A f) (postprocess B f) =
      ∑ aa : α × α,
        if f aa.1 = f aa.2 then
          S.ev (S.opTensor (A.outcome aa.1) (B.outcome aa.2))
        else 0 := by
  unfold SymModel.qBipartiteMatchMass
  simp only [postprocess, S.opTensor_sum_left_finset, S.opTensor_sum_right_finset,
    S.ev_finset_sum, Finset.sum_filter]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h0 : ∀ X : 𝔓, S.ev (S.opTensor 0 X) = 0 ∧ S.ev (S.opTensor X 0) = 0 := fun X => by
    simp only [SymModel.opTensor, map_zero, zero_mul, mul_zero, S.ev_zero, and_self]
  by_cases h : f a = f x
  · rw [Finset.sum_eq_single (f a) (fun b _ hb => by simp [Ne.symm hb, h0]) (by simp)]
    simp [h]
  · exact (Finset.sum_eq_zero fun b _ => by
      by_cases ha : f a = b
      · subst ha; simp [Ne.symm h, h0]
      · simp [ha, h0]).trans (by simp [h])

open Classical in
/-- The off-diagonal collision mass of `A` and `B` under the readout `f`: the pairs of distinct
outcomes with the same readout, weighted by `⟨Ψ, (A_a ⊗ B_{a'}) Ψ⟩`. -/
noncomputable def localCollisionMass
    {α β : Type*} [Fintype α]
    (S : SymModel 𝔓 K) (A B : SubMeas α 𝔓) (f : α → β) : ℝ :=
  ∑ aa : α × α,
    (if aa.1 = aa.2 then 0 else if f aa.1 = f aa.2 then (1 : ℝ) else 0) *
      S.ev (S.opTensor (A.outcome aa.1) (B.outcome aa.2))

/-- Postprocessing adds exactly the collision mass to the matching mass. -/
theorem qBipartiteMatchMass_postprocess_eq_add_localCollision
    {α β : Type*} [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (A B : SubMeas α 𝔓) (f : α → β) :
    S.qBipartiteMatchMass (postprocess A f) (postprocess B f) =
      S.qBipartiteMatchMass A B + localCollisionMass S A B f := by
  classical
  have hdiag :
      S.qBipartiteMatchMass A B =
        ∑ aa : α × α,
          if aa.1 = aa.2 then S.ev (S.opTensor (A.outcome aa.1) (B.outcome aa.2)) else 0 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ =>
      (Fintype.sum_ite_eq a fun y => S.ev (S.opTensor (A.outcome a) (B.outcome y))).symm
  rw [qBipartiteMatchMass_postprocess_eq_pair_sum, hdiag, localCollisionMass,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun aa _ => ?_
  by_cases hEq : aa.1 = aa.2
  · simp [hEq]
  · by_cases hf : f aa.1 = f aa.2 <;> simp [hEq, hf]

/-- The consistency defect is at most that of the postprocessed pair plus the collision mass. -/
theorem qBipartiteConsDefect_le_postprocess_add_localCollision
    {α β : Type*} [Fintype α] [Fintype β]
    (S : SymModel 𝔓 K) (A B : SubMeas α 𝔓) (f : α → β) :
    S.qBipartiteConsDefect A B ≤
      S.qBipartiteConsDefect (postprocess A f) (postprocess B f) +
        localCollisionMass S A B f := by
  classical
  have hc : 0 ≤ localCollisionMass S A B f :=
    Finset.sum_nonneg fun aa _ => mul_nonneg (by split_ifs <;> norm_num)
      (S.ev_nonneg_of_psd _ (S.opTensor_nonneg (A.outcome_pos aa.1) (B.outcome_pos aa.2)))
  have hmatch := qBipartiteMatchMass_postprocess_eq_add_localCollision S A B f
  unfold SymModel.qBipartiteConsDefect
  simp only [postprocess_total, hmatch]
  exact max_le (add_nonneg (le_max_left 0 _) hc)
    (by linarith [le_max_right (0 : ℝ) (S.ev (S.opTensor A.total B.total) -
      (S.qBipartiteMatchMass A B + localCollisionMass S A B f))])

/-- Averaging the collision mass of the point evaluations over a uniform point gives the
polynomial collision mass. -/
theorem avg_localCollisionMass_eval_eq_polynomialCollisionMass
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (Left Right : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params))
      (fun u => localCollisionMass S Left Right
        (fun g : MIPStarRE.LDT.Polynomial params => g u)) =
      Preliminaries.polynomialCollisionMass params S Left Right := by
  classical
  unfold localCollisionMass Preliminaries.polynomialCollisionMass
  rw [avgOver_sum]
  refine Finset.sum_congr rfl fun gg _ => ?_
  by_cases hEq : gg.1 = gg.2
  · simp [hEq, avgOver_zero]
  · simp only [hEq, ite_false]
    rw [avgOver_mul_const]
    congr 1
    exact avgOver_congr _ _ _ fun u => by by_cases h : gg.1 u = gg.2 u <;> simp [h]

/-- The exact algebraic expansion/reindexing statement used in `mainFormal` Step 5.

Paper origin: `references/ldt-paper/inductive_step.tex:119-130`
(`\label{eq:G-self-consistency}`), with the collision estimate supplied by the
Schwartz--Zippel lemma.

Paper lines 119--128 compare the evaluated consistency defect

`E_u ∑_{a ≠ b} ⟨ψ| G^A_[g(u)=a] ⊗ G^B_[h(u)=b] |ψ⟩`

with the full-polynomial consistency defect

`∑_{g ≠ h} ⟨ψ| G^A_g ⊗ G^B_h |ψ⟩`.

The paper reuses `g` as the bound name in the Alice and Bob sums; Lean writes
these independently-bound polynomial outcomes as `g` and `h` to make the
independence explicit.

After expanding the postprocessed outcomes and separating the colliding pairs
`g(u)=h(u)`, the only extra term is the collision mass bounded by
Schwartz--Zippel in `Preliminaries.polynomialCollisionMass_le_mdq`.  This
predicate records precisely that expansion step, without bundling the
Schwartz--Zippel estimate itself into an unproved hypothesis. -/
def MainFormalStep5ExpansionBound
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (Left Right : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) : Prop :=
  S.bipartiteConsError (uniformDistribution Unit)
      (constSubMeasFamily Left) (constSubMeasFamily Right) ≤
    S.bipartiteConsError (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Left)
      (polynomialEvaluationFamily params Right) +
    Preliminaries.polynomialCollisionMass params S Left Right

/-- The algebraic Step 5 expansion bound: the full-polynomial consistency
error is bounded by the evaluated consistency error plus the collision mass. -/
theorem mainFormalStep5_expansionBound
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (Left Right : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    MainFormalStep5ExpansionBound params S Left Right := by
  classical
  unfold MainFormalStep5ExpansionBound
  calc
    S.bipartiteConsError (uniformDistribution Unit)
        (constSubMeasFamily Left) (constSubMeasFamily Right)
      = S.qBipartiteConsDefect Left Right := by
          simp [SymModel.bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    _ = avgOver (uniformDistribution (Point params))
          (fun _ : Point params => S.qBipartiteConsDefect Left Right) :=
          (avgOver_uniform_const (α := Point params)
            (c := S.qBipartiteConsDefect Left Right)).symm
    _ ≤ avgOver (uniformDistribution (Point params))
          (fun u =>
            S.qBipartiteConsDefect (evaluateAt params u Left) (evaluateAt params u Right) +
              localCollisionMass S Left Right
                (fun g : MIPStarRE.LDT.Polynomial params => g u)) :=
          avgOver_mono _ _ _ fun u =>
            qBipartiteConsDefect_le_postprocess_add_localCollision S Left Right
              (fun g : MIPStarRE.LDT.Polynomial params => g u)
    _ = S.bipartiteConsError (uniformDistribution (Point params))
          (polynomialEvaluationFamily params Left)
          (polynomialEvaluationFamily params Right) +
        Preliminaries.polynomialCollisionMass params S Left Right := by
          rw [avgOver_add, avg_localCollisionMass_eval_eq_polynomialCollisionMass]
          rfl

/-- Heterogeneous Step 5 packaging for `mainFormal` using the proved algebraic
expansion bound.

Given evaluated consistency at error `ζ` (paper line 116) and the exact
line-122--125 expansion recorded by `MainFormalStep5ExpansionBound`, the
proved tensor Schwartz--Zippel bound contributes the paper's `md/q` loss and
returns full-polynomial consistency at error `ζ + md/q` (paper lines 126--133).

In the symmetric model both registers carry `𝔓`, so this is
`mainFormalStep5_selfConsistency_ofExpansionBound`; the vendored hypothesis
`hnorm : ψ.IsNormalized` is a theorem of the model. -/
theorem mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (Left Right : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (ζ : ℝ)
    (hevaluated : S.ConsRel (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Left)
      (polynomialEvaluationFamily params Right) ζ) :
    S.ConsRel (uniformDistribution Unit)
      (constSubMeasFamily Left) (constSubMeasFamily Right)
      (ζ + (params.m * params.d : ℝ) / params.q) := by
  have hexp : _ ≤ _ := mainFormalStep5_expansionBound params S Left Right
  exact ⟨by linarith [hevaluated.offDiagonalBound,
    Preliminaries.polynomialCollisionMass_le_mdq params S Left Right]⟩

/-- Step 5 packaging for `mainFormal` using the proved algebraic expansion bound.

Given evaluated consistency at error `ζ` (paper line 116) and the exact
line-122--125 expansion recorded by `MainFormalStep5ExpansionBound`, the
proved tensor Schwartz--Zippel bound contributes the paper's `md/q` loss and
returns full-polynomial consistency at error `ζ + md/q` (paper lines 126--133).

This is the source-labelled same-space statement (the vendored hypothesis
`hnorm : ψ.IsNormalized` is a theorem of the model). -/
theorem mainFormalStep5_selfConsistency_ofExpansionBound
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (Left Right : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (ζ : ℝ)
    (hevaluated : S.ConsRel (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Left)
      (polynomialEvaluationFamily params Right) ζ) :
    S.ConsRel (uniformDistribution Unit)
      (constSubMeasFamily Left) (constSubMeasFamily Right)
      (ζ + (params.m * params.d : ℝ) / params.q) :=
  mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous params S Left Right ζ hevaluated

end Test

end MIPRE.LIDT.Co

end
