/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
MainInductionStep/Theorems/AvgSliceErrors/Core.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.InductionParameterBounds.Averaging
public import MIPRE.Background.LIDT.Co.MainInductionStep.Theorems.StageDataConstructors
public import MIPStarRE.LDT.MainInductionStep.Theorems.AvgSliceErrors.Core

@[expose] public section

/-!
# Section 6 — Averaged Slice Error Bounds: Core Estimates

The Jensen and averaging estimates for ordinary and answer-valued restricted slice errors: the
nonnegativity of the restricted failure profiles, and the bounds on the averages over the slice
height `x` of the slice self-improvement error `ζ_x`, of the slice induction parameter `ν_x` and of
the slice induction error `σ_x` by their next-dimensional counterparts. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Theorems/AvgSliceErrors/Core.lean` in the
port of `planning/c6b-plan.md` (milestone M12, section "Port conventions").

## Translation

A strategy is a `SymStrat params.next 𝔓 K` or an `AnswerSymStrat params.next 𝔓 K`
(`Co/Test/StrategyCore.lean`), whose state is the symmetric model `strategy.state : SymModel 𝔓 K`,
and errors are real numbers (the vendored `Error := ℝ`). The only quantum content of the file is
the nonnegativity of the restricted failure surrogates, `restricted.state.bipartiteConsError_nonneg`
and `restricted.state.bipartiteSSCError_nonneg` (Co `Test/Defs.lean`) in place of the vendored
`bipartiteConsError_nonneg restricted.state` and `bipartiteSSCError_nonneg restricted.state`, and
the nonnegativity of the parameters of a good strategy (Co `Test/StrategyFailures.lean`). The rest
is real arithmetic on the profiles. The error constants (`mainInductionError`, `mainInductionNu`,
`selfImprovementInInductionError`, `sliceConditioningLoss`) and the comparisons of
`InductionParameterBounds/Averaging` are the vendored classical declarations, reached through
explicit `open` lists. No vendored statement here has a swap, density or normalization
hypothesis, so none is dropped, and no declaration takes a new hypothesis. The vendored file-wide
`respectTransparency false` is not needed: the file sets no option.

## Proofs that differ from the vendored ones

The vendored file proves the self-improvement estimate twice (ordinary and answer-valued
successor) and the `ν` estimate twice, each time through a chain of about twenty `have`s and an
`nlinarith`. Here each estimate is proved once, for arbitrary nonnegative profiles
`a s g : Fq params → ℝ`, by the private theorems `avgOver_selfImprovementInInductionError_le`,
`avgOver_mainInductionNu_le` and `avgOver_mainInductionError_le` (Jensen for `t ↦ t^{1/n}`, then
the comparisons `m · (L t)^c ≤ (m + 1) t^c` and `m² · (L t)^c ≤ (m + 1)² t^c`, then `linarith`),
and the six vendored lemmas apply them to the profile at hand. The three `restricted_*_nonneg`
lemmas are terms.

## Not ported

- `avgOver_uniform_fq_nonneg`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/inductive_step.tex`
- `blueprint/src/chapter/ch10_induction.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.MainInductionStep

open MIPStarRE.LDT (Parameters FieldModel Point Fq uniformDistribution avgOver avgOver_nonneg
  avgOver_mono avgOver_add avgOver_const_mul avgOver_uniform_const AxisParallelTestSample
  RestrictedDiagonalSample)
open MIPStarRE.LDT.MainInductionStep (mainInductionError mainInductionNu
  selfImprovementInInductionError sliceConditioningLoss
  m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow
  m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow)
open MIPRE.LIDT.Co (SymStrat AnswerSymStrat)

universe uP uK

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof. -/
lemma avgOver_uniform_fq_rpow_le_rpow_avg
    (params : Parameters) [FieldModel params.q]
    (f : Fq params → ℝ)
    (n : ℕ)
    (hn : 1 ≤ n)
    (hf : ∀ a, 0 ≤ f a) :
    avgOver (uniformDistribution (Fq params))
        (fun a => Real.rpow (f a) (1 / (n : ℝ))) ≤
      Real.rpow (avgOver (uniformDistribution (Fq params)) f) (1 / (n : ℝ)) := by
  simpa using
    avgOver_uniform_rpow_one_div_le_rpow_avg
      (α := Fq params) (f := f) (n := n) hn hf

variable {𝔓 : Type uP} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## Nonnegativity of the restricted profiles -/

/-- The axis-parallel entries of a restricted failure profile are nonnegative. -/
theorem restricted_axis_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    (profile : RestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.axisParallel x := fun x =>
  le_trans
    ((xRestrictedStrategy params strategy x).state.bipartiteConsError_nonneg
      (uniformDistribution (AxisParallelTestSample params))
      (RestrictedSymStrat.axisParallelPointAnswerFamily (xRestrictedStrategy params strategy x))
      (RestrictedSymStrat.axisParallelLineAnswerFamily (xRestrictedStrategy params strategy x)))
    (profile.restrictedGood x).axisParallelTest

/-- The self-consistency entries of a restricted failure profile are nonnegative. -/
theorem restricted_self_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    (profile : RestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.selfConsistency x := fun x =>
  le_trans
    ((xRestrictedStrategy params strategy x).state.bipartiteSSCError_nonneg
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement))
    (profile.restrictedGood x).selfConsistencyTest

/-- The diagonal entries of a restricted failure profile are nonnegative. -/
theorem restricted_diag_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next 𝔓 K}
    (profile : RestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.diagonal x := fun x =>
  le_trans
    (mul_nonneg (by positivity) <| Finset.sum_nonneg fun j _ =>
      (xRestrictedStrategy params strategy x).state.bipartiteConsError_nonneg
        (uniformDistribution (RestrictedDiagonalSample params j))
        (RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
          (xRestrictedStrategy params strategy x) j)
        (RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
          (xRestrictedStrategy params strategy x) j))
    (profile.restrictedGood x).diagonalLineTest

/-- The axis-parallel entries of an answer-valued successor restricted profile are
nonnegative. -/
theorem answerSuccessor_restricted_axis_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next 𝔓 K}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.axisParallel x := fun x =>
  answer_eps_nonneg_of_isGood params
    (xRestrictedAnswerSymStratOfAnswer params strategy x)
    (profile.restrictedGood x)

/-- The self-consistency entries of an answer-valued successor restricted profile are
nonnegative. -/
theorem answerSuccessor_restricted_self_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next 𝔓 K}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.selfConsistency x := fun x =>
  answer_delta_nonneg_of_isGood params
    (xRestrictedAnswerSymStratOfAnswer params strategy x)
    (profile.restrictedGood x)

/-- The diagonal entries of an answer-valued successor restricted profile are nonnegative. -/
theorem answerSuccessor_restricted_diag_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : AnswerSymStrat params.next 𝔓 K}
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.diagonal x := fun x =>
  answer_gamma_nonneg_of_isGood params
    (xRestrictedAnswerSymStratOfAnswer params strategy x)
    (profile.restrictedGood x)

/-! ## The scalar estimates, for arbitrary nonnegative profiles -/

/-- Jensen for `t ↦ t^{1/n}` on a profile, followed by the averaged bound `E a ≤ b`:
`E_x (a x)^{1/n} ≤ b^{1/n}`. -/
private theorem avgOver_rpow_le_of_avg_le
    (params : Parameters) [FieldModel params.q]
    (a : Fq params → ℝ) (ha : ∀ x, 0 ≤ a x) {b : ℝ} (n : ℕ) (hn : 1 ≤ n)
    (hab : avgOver (uniformDistribution (Fq params)) a ≤ b) :
    avgOver (uniformDistribution (Fq params)) (fun x => Real.rpow (a x) (1 / (n : ℝ))) ≤
      Real.rpow b (1 / (n : ℝ)) :=
  (avgOver_uniform_fq_rpow_le_rpow_avg params a n hn ha).trans
    (Real.rpow_le_rpow (avgOver_nonneg _ a ha) hab (by positivity))

/-- The averaged self-improvement estimate for arbitrary nonnegative profiles `a`, `s` whose
averages are at most `sliceConditioningLoss params * eps` and `delta`. -/
private theorem avgOver_selfImprovementInInductionError_le
    (params : Parameters) [FieldModel params.q]
    (a s g : Fq params → ℝ) {eps delta gamma : ℝ}
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (ha : ∀ x, 0 ≤ a x) (hs : ∀ x, 0 ≤ s x)
    (haxis : avgOver (uniformDistribution (Fq params)) a ≤ sliceConditioningLoss params * eps)
    (hself : avgOver (uniformDistribution (Fq params)) s ≤ delta) :
    avgOver (uniformDistribution (Fq params))
        (fun x => selfImprovementInInductionError params (a x) (s x) (g x)) ≤
      selfImprovementInInductionError params.next eps delta gamma := by
  have hm : (0 : ℝ) ≤ params.m := Nat.cast_nonneg _
  have hm_le : (params.m : ℝ) ≤ params.next.m := by exact_mod_cast Nat.le_succ params.m
  have ha' := avgOver_rpow_le_of_avg_le params a ha 32 (by norm_num) haxis
  have hs' := avgOver_rpow_le_of_avg_le params s hs 32 (by norm_num) hself
  simp only [Nat.cast_ofNat] at ha' hs'
  have hA := (mul_le_mul_of_nonneg_left ha' hm).trans
    (m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow params heps (by norm_num)
      (by norm_num : (1 / (32 : ℝ)) ≤ 1))
  have hS := (mul_le_mul_of_nonneg_left hs' hm).trans
    (mul_le_mul_of_nonneg_right hm_le (Real.rpow_nonneg hdelta _))
  have hR : (params.m : ℝ) * Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / 32) ≤
      (params.next.m : ℝ) * Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / 32) :=
    mul_le_mul_of_nonneg_right hm_le (Real.rpow_nonneg (by positivity) _)
  simp only [selfImprovementInInductionError, avgOver_const_mul, avgOver_add,
    avgOver_uniform_const]
  change _ ≤ 3000 * (params.next.m : ℝ) *
    (Real.rpow eps (1 / 32) + Real.rpow delta (1 / 32) +
      Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / 32))
  linarith

/-- The averaged `ν` estimate for arbitrary nonnegative profiles `a`, `s`, `g` whose averages
are at most `sliceConditioningLoss params * eps`, `delta` and
`sliceConditioningLoss params * gamma`. -/
private theorem avgOver_mainInductionNu_le
    (params : Parameters) [FieldModel params.q] (k : ℕ)
    (a s g : Fq params → ℝ) {eps delta gamma : ℝ}
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) (hgamma : 0 ≤ gamma)
    (ha : ∀ x, 0 ≤ a x) (hs : ∀ x, 0 ≤ s x) (hg : ∀ x, 0 ≤ g x)
    (haxis : avgOver (uniformDistribution (Fq params)) a ≤ sliceConditioningLoss params * eps)
    (hself : avgOver (uniformDistribution (Fq params)) s ≤ delta)
    (hdiag : avgOver (uniformDistribution (Fq params)) g ≤
      sliceConditioningLoss params * gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => mainInductionNu params k (a x) (s x) (g x)) ≤
      mainInductionNu params.next k eps delta gamma := by
  have hm : (0 : ℝ) ≤ (params.m : ℝ) ^ (2 : ℕ) := by positivity
  have hm_le : (params.m : ℝ) ^ (2 : ℕ) ≤ (params.next.m : ℝ) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_succ params.m) 2
  have ha' := avgOver_rpow_le_of_avg_le params a ha 1024 (by norm_num) haxis
  have hs' := avgOver_rpow_le_of_avg_le params s hs 1024 (by norm_num) hself
  have hg' := avgOver_rpow_le_of_avg_le params g hg 1024 (by norm_num) hdiag
  simp only [Nat.cast_ofNat] at ha' hs' hg'
  have hA := (mul_le_mul_of_nonneg_left ha' hm).trans
    (m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow params heps (by norm_num)
      (by norm_num : (1 / (1024 : ℝ)) ≤ 1))
  have hS := (mul_le_mul_of_nonneg_left hs' hm).trans
    (mul_le_mul_of_nonneg_right hm_le (Real.rpow_nonneg hdelta _))
  have hG := (mul_le_mul_of_nonneg_left hg' hm).trans
    (m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow params hgamma (by norm_num)
      (by norm_num : (1 / (1024 : ℝ)) ≤ 1))
  have hR : (params.m : ℝ) ^ (2 : ℕ) * Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / 1024) ≤
      (params.next.m : ℝ) ^ (2 : ℕ) * Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / 1024) :=
    mul_le_mul_of_nonneg_right hm_le (Real.rpow_nonneg (by positivity) _)
  have hk : (0 : ℝ) ≤ 1000 * (k : ℝ) ^ (2 : ℕ) := by positivity
  have hinner := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hA hS) hG) hR) hk
  simp only [mainInductionNu, avgOver_const_mul, avgOver_add, avgOver_uniform_const]
  change _ ≤ 1000 * (k : ℝ) ^ (2 : ℕ) * (params.next.m : ℝ) ^ (2 : ℕ) *
    (Real.rpow eps (1 / 1024) + Real.rpow delta (1 / 1024) + Real.rpow gamma (1 / 1024) +
      Real.rpow ((params.d : ℝ) / (params.q : ℝ)) (1 / 1024))
  linarith

/-- The averaged main-induction error, given the averaged `ν` estimate. -/
private theorem avgOver_mainInductionError_le
    (params : Parameters) [FieldModel params.q] (k : ℕ)
    (a s g : Fq params → ℝ) {eps delta gamma : ℝ}
    (hnu : avgOver (uniformDistribution (Fq params))
        (fun x => mainInductionNu params k (a x) (s x) (g x)) ≤
      mainInductionNu params.next k eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => mainInductionError params k (a x) (s x) (g x)) ≤
      ((params.m : ℝ) ^ (2 : ℕ)) *
        (mainInductionNu params.next k eps delta gamma +
          Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ)))))) := by
  simp only [mainInductionError, avgOver_const_mul, avgOver_add, avgOver_uniform_const]
  exact mul_le_mul_of_nonneg_left (add_le_add_left hnu _) (by positivity)

/-! ## The averaged slice errors -/

/-- Averaging the slice self-improvement errors gives the paper's displayed
bound on `\mathbb{E}_x[\zeta_x]`, i.e. the first inequality from
`inductive_step.tex:555-567`. -/
theorem average_sliceSelfImprovementError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceSelfImprovementError params hrestrict x) ≤
      selfImprovementInInductionError params.next eps delta gamma :=
  avgOver_selfImprovementInInductionError_le params _ _ hrestrict.profile.diagonal
    (eps_nonneg_of_isGood params.next strategy hgood)
    (delta_nonneg_of_isGood params.next strategy hgood)
    (restricted_axis_nonneg params hrestrict.profile)
    (restricted_self_nonneg params hrestrict.profile)
    hrestrict.axisAverageBound hrestrict.selfAverageBound

/-- Jensen/conditioning estimate controlling the averaged slice induction
parameter `\mathbb{E}_x[\nu_x]` by the next-stage `\nu`, corresponding to the
second displayed inequality in `inductive_step.tex:555-567`. -/
theorem average_sliceMainInductionNu_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          mainInductionNu params k
            (hrestrict.profile.axisParallel x)
            (hrestrict.profile.selfConsistency x)
            (hrestrict.profile.diagonal x)) ≤
      mainInductionNu params.next k eps delta gamma :=
  avgOver_mainInductionNu_le params k _ _ _
    (eps_nonneg_of_isGood params.next strategy hgood)
    (delta_nonneg_of_isGood params.next strategy hgood)
    (gamma_nonneg_of_isGood params.next strategy hgood)
    (restricted_axis_nonneg params hrestrict.profile)
    (restricted_self_nonneg params hrestrict.profile)
    (restricted_diag_nonneg params hrestrict.profile)
    hrestrict.axisAverageBound hrestrict.selfAverageBound hrestrict.diagonalAverageBound

/-- Averaging the recursive slice errors `\sigma_x` and telescoping the slice
main-induction bound yields the paper's `\mathbb{E}_x[\sigma_x]` estimate used
in the final pasting-data record error calculation. -/
theorem average_sliceError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma)
    (hinduction : PerSliceInductionData params strategy eps delta gamma hrestrict k) :
    avgOver (uniformDistribution (Fq params)) hinduction.sliceError ≤
      ((params.m : ℝ) ^ (2 : ℕ)) *
        (mainInductionNu params.next k eps delta gamma +
          Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ)))))) :=
  (avgOver_mono _ hinduction.sliceError _ hinduction.error_le).trans
    (avgOver_mainInductionError_le params k _ _ _
      (average_sliceMainInductionNu_le params strategy eps delta gamma k hgood hrestrict))

/-- Answer-valued successor analogue of the averaged self-improvement error
estimate.

For the restricted profiles of an ambient `AnswerSymStrat` successor, the
average of the slice errors `\zeta_x` is bounded by the next-dimensional
quantity `\zeta`.  This is the scalar part of the answer-valued self-improvement
averaging in `inductive_step.tex:486-551`. -/
theorem average_answerSuccessorSliceSelfImprovementError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy)
    (haxis :
      averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
        sliceConditioningLoss params * eps)
    (hself :
      averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          selfImprovementInInductionError params
            (profile.axisParallel x)
            (profile.selfConsistency x)
            (profile.diagonal x)) ≤
      selfImprovementInInductionError params.next eps delta gamma :=
  avgOver_selfImprovementInInductionError_le params _ _ _
    (answer_eps_nonneg_of_isGood params.next strategy hgood)
    (answer_delta_nonneg_of_isGood params.next strategy hgood)
    (answerSuccessor_restricted_axis_nonneg params profile)
    (answerSuccessor_restricted_self_nonneg params profile)
    haxis hself

/-- Answer-valued successor analogue of the averaged recursive induction
parameter estimate.

For an ambient `AnswerSymStrat` in dimension `m + 1`, the restricted
answer-valued slice profile satisfies the same Jensen and conditioning estimate
as in the ordinary successor route.  This is the scalar calculation needed after
the recursive answer-valued predecessor calls. -/
theorem average_answerSuccessorSliceMainInductionNu_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy)
    (haxis :
      averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
        sliceConditioningLoss params * eps)
    (hself :
      averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta)
    (hdiag :
      averageAnswerSuccessorRestrictedDiagonalError params profile ≤
        sliceConditioningLoss params * gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          mainInductionNu params k
            (profile.axisParallel x)
            (profile.selfConsistency x)
            (profile.diagonal x)) ≤
      mainInductionNu params.next k eps delta gamma :=
  avgOver_mainInductionNu_le params k _ _ _
    (answer_eps_nonneg_of_isGood params.next strategy hgood)
    (answer_delta_nonneg_of_isGood params.next strategy hgood)
    (answer_gamma_nonneg_of_isGood params.next strategy hgood)
    (answerSuccessor_restricted_axis_nonneg params profile)
    (answerSuccessor_restricted_self_nonneg params profile)
    (answerSuccessor_restricted_diag_nonneg params profile)
    haxis hself hdiag

/-- Average of the recursive main-induction errors for answer-valued successor
slices.

This is the scalar estimate used after applying the predecessor answer-valued
induction hypothesis to each restricted successor slice. -/
theorem average_answerSuccessorSliceMainInductionError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params.next 𝔓 K)
    (eps delta gamma : ℝ)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (profile : AnswerSuccessorRestrictedFailureProfile params strategy)
    (haxis :
      averageAnswerSuccessorRestrictedAxisParallelError params profile ≤
        sliceConditioningLoss params * eps)
    (hself :
      averageAnswerSuccessorRestrictedSelfConsistencyError params profile ≤ delta)
    (hdiag :
      averageAnswerSuccessorRestrictedDiagonalError params profile ≤
        sliceConditioningLoss params * gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          mainInductionError params k
            (profile.axisParallel x)
            (profile.selfConsistency x)
            (profile.diagonal x)) ≤
      ((params.m : ℝ) ^ (2 : ℕ)) *
        (mainInductionNu params.next k eps delta gamma +
          Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ)))))) :=
  avgOver_mainInductionError_le params k _ _ _
    (average_answerSuccessorSliceMainInductionNu_le
      params strategy eps delta gamma k hgood profile haxis hself hdiag)

end MIPRE.LIDT.Co.MainInductionStep

end
