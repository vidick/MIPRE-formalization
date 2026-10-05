/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
Final.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.MatrixChernoff
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.ScalarBounds
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.DegreeZero
public import MIPRE.Background.LIDT.Co.Pasting.Defs.Tuples
public import MIPRE.Background.LIDT.Co.Pasting.Sandwich.PastedFamilies
public import MIPRE.Background.LIDT.Co.Pasting.CommutingWithG.Complete
public import MIPRE.Background.LIDT.Co.Pasting.CommutingWithG.Incomplete
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.HAConsistency
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.OverAllOutcomes.Final
public import MIPStarRE.LDT.Pasting.Bernoulli.Final

@[expose] public section

/-!
# Section 12 pasting: final pasting theorems

The completeness corollary `cor:ld-pasting-N-completeness`, the sub-measurement lemma
`lem:ld-pasting-sub-measurement` and the pasting theorem `thm:ld-pasting` with its complementary
branches: the counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/Final.lean` in
the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

A strategy is a `SymStrat params.next 𝔓 K` and a slice family an `IdxPolyFamily params 𝔓`;
errors are in `ℝ`. Every statement keeps the vendored argument list and order, and none has a
swap, density or normalization hypothesis (the vendored ones had none either). Inside the proofs,
three uses of the vendored strategy fields are replaced (section "Swap symmetry is a theorem"):

- in `fromHToGBernoulliTailMass_lower_bound`, the matrix Chernoff lemma is applied to the vector
  state `strategy.state.toVecState` without the vendored `strategy.isNormalized`, and the swap
  `strategy.permInvState.swap_ev` that moves the Bernoulli tail from the left register to the
  right one is `S.ev_L_eq_ev_R`, after `bernoulliTailOperator_leftTensor`;
- in `ldPasting_of_one_le_error`, `bipartiteConsError_uniform_le_one strategy.state
  strategy.isNormalized` is the keystone's `strategy.state.bipartiteConsError_uniform_le_one`;
- the nonnegativity of `κ` in `fromHToGBernoulliTailMass_lower_bound` is the ported
  `kappa_nonneg_of_complete` rather than an inline repetition of it.

The four arithmetic lemmas at the head of the vendored file mention no state, operator or
measurement, so they are not ported: this file imports the vendored file and names them through
an explicit `open MIPStarRE.LDT.Pasting (…)` list.

## Not ported

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `docs/paper-gaps/issue-1622-ld-pasting-degree-zero.tex`
-/

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Point AxisParallelTestSample uniformDistribution)
open MIPStarRE.LDT.MainInductionStep (ldPastingInInductionNu ldPastingInInductionError)
open MIPStarRE.LDT.Pasting (overAllOutcomesError fromHToGError ldPastingCompletenessLowerBound
  fallbackInterpolatedPolynomial
  one_le_ldPastingError_of_one_le_nu one_le_ldPastingError_of_k_eq_zero)
open MIPRE.LIDT.Co (SymStrat Measurement SubMeas IdxProjMeas IdxPolyFamily
  polynomialEvaluationFamily axisParallelPointAnswerFamily axisParallelLineAnswerFamily)

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof.

Arithmetic helper for `cor:ld-pasting-N-completeness`: absorb the
`overAllOutcomes` and `fromHToG` scalar losses into
`ldPastingInInductionNu`.

The proof uses that the corrected `fromHToGError` tail sum is a sub-sum of the
full `overAllOutcomesError` sum and the slack `46 + 46 ≤ 100`. -/
lemma overAllOutcomesError_add_fromHToGError_le_ldPastingNu
    (params : Parameters)
    [FieldModel params.q]
    (eps delta gamma zeta : ℝ) (k : ℕ)
    (hk_pos : 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    overAllOutcomesError params eps delta gamma zeta k +
        fromHToGError params gamma zeta k ≤
      MIPStarRE.LDT.MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
  let kE : ℝ := (k : ℝ)
  let mE : ℝ := (params.m : ℝ)
  let ratio : ℝ := (params.d : ℝ) / (params.q : ℝ)
  let epsTerm : ℝ := Real.rpow eps (1 / (32 : ℝ))
  let deltaTerm : ℝ := Real.rpow delta (1 / (32 : ℝ))
  let gammaTerm : ℝ := Real.rpow gamma (1 / (32 : ℝ))
  let zetaTerm : ℝ := Real.rpow zeta (1 / (32 : ℝ))
  let dqTerm : ℝ := Real.rpow ratio (1 / (32 : ℝ))
  let fullSum : ℝ := epsTerm + deltaTerm + gammaTerm + zetaTerm + dqTerm
  let tailSum : ℝ := gammaTerm + zetaTerm + dqTerm
  have hkE_one : (1 : ℝ) ≤ kE := by
    dsimp [kE]
    exact_mod_cast hk_pos
  have hkE_nonneg : 0 ≤ kE := by positivity
  have hmE_nonneg : 0 ≤ mE := by positivity
  have hratio_nonneg : 0 ≤ ratio := by
    dsimp [ratio]
    positivity
  have hepsTerm_nonneg : 0 ≤ epsTerm := by
    dsimp [epsTerm]
    exact Real.rpow_nonneg heps_nonneg _
  have hdeltaTerm_nonneg : 0 ≤ deltaTerm := by
    dsimp [deltaTerm]
    exact Real.rpow_nonneg hdelta_nonneg _
  have hgammaTerm_nonneg : 0 ≤ gammaTerm := by
    dsimp [gammaTerm]
    exact Real.rpow_nonneg hgamma_nonneg _
  have hzetaTerm_nonneg : 0 ≤ zetaTerm := by
    dsimp [zetaTerm]
    exact Real.rpow_nonneg hzeta_nonneg _
  have hdqTerm_nonneg : 0 ≤ dqTerm := by
    dsimp [dqTerm]
    exact Real.rpow_nonneg hratio_nonneg _
  have htail_le_full : tailSum ≤ fullSum := by
    dsimp [tailSum, fullSum]
    linarith
  have hfull_nonneg : 0 ≤ fullSum := by
    dsimp [fullSum]
    linarith
  calc
    overAllOutcomesError params eps delta gamma zeta k +
        fromHToGError params gamma zeta k
      = 46 * (kE ^ (2 : ℕ)) * mE * fullSum +
          46 * (kE ^ (2 : ℕ)) * mE * tailSum := by
          simp [overAllOutcomesError, fromHToGError, kE, mE, fullSum, tailSum,
            epsTerm, deltaTerm, gammaTerm, zetaTerm, dqTerm, ratio]
    _ ≤ 46 * (kE ^ (2 : ℕ)) * mE * fullSum +
          46 * (kE ^ (2 : ℕ)) * mE * fullSum := by
          gcongr
    _ ≤ 100 * (kE ^ (2 : ℕ)) * mE * fullSum := by
          have hterm_nonneg : 0 ≤ (kE ^ (2 : ℕ)) * mE * fullSum := by
            positivity
          nlinarith
    _ = MIPStarRE.LDT.MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
          simp [MIPStarRE.LDT.MainInductionStep.ldPastingInInductionNu, kE, mE, fullSum,
            epsTerm, deltaTerm, gammaTerm, zetaTerm, dqTerm, ratio]

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof.

Paper arithmetic: for `θ = 1/(200m)`,
`1/(1-θ) ≤ 1 + 1/(100m)`. -/
lemma ldPasting_theta_inv_le (params : Parameters) :
    (1 / (1 - 1 / (200 * (params.m : ℝ))) : ℝ) ≤
      1 + 1 / (100 * (params.m : ℝ)) := by
  have hm_pos : (0 : ℝ) < (params.m : ℝ) := by exact_mod_cast params.hm
  have hm_ge_one : (1 : ℝ) ≤ (params.m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt params.hm)
  have hden200_pos : 0 < 200 * (params.m : ℝ) := by positivity
  have hden100_pos : 0 < 100 * (params.m : ℝ) := by positivity
  have hdenMinus_pos : 0 < 200 * (params.m : ℝ) - 1 := by nlinarith
  have hdenMinus_ge : 100 * (params.m : ℝ) ≤ 200 * (params.m : ℝ) - 1 := by
    nlinarith
  calc
    (1 / (1 - 1 / (200 * (params.m : ℝ))) : ℝ)
        = (200 * (params.m : ℝ)) / (200 * (params.m : ℝ) - 1) := by
            field_simp [hden200_pos.ne', hdenMinus_pos.ne']
    _ = 1 + 1 / (200 * (params.m : ℝ) - 1) := by
            field_simp [hdenMinus_pos.ne']
            nlinarith
    _ ≤ 1 + 1 / (100 * (params.m : ℝ)) := by
            gcongr

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof.

Paper arithmetic: the matrix-Chernoff exponential at `θ = 1/(200m)` is the
stated `exp(-k/(80000m²))` term. -/
lemma ldPasting_chernoff_exponent_eq (params : Parameters) (k : ℕ) :
    -(((1 / (200 * (params.m : ℝ))) ^ (2 : ℕ)) * (k : ℝ)) / 2 =
      -((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ)))) := by
  have hm_pos : (0 : ℝ) < (params.m : ℝ) := by exact_mod_cast params.hm
  have hden_pos : (0 : ℝ) < 200 * (params.m : ℝ) := by positivity
  have hden2_pos : (0 : ℝ) < 80000 * ((params.m : ℝ) ^ (2 : ℕ)) := by positivity
  field_simp [hden_pos.ne', hden2_pos.ne']
  ring

/-- Upstream keeps this helper `private` since its Lean-module port (`LionSR/MIPStarRE` at `5fc363b`); the port carries its own copy, with upstream's proof.

The public size assumption `k ≥ 400md` implies the matrix-Chernoff size
condition `k ≥ 2d/θ` at `θ = 1/(200m)`. -/
lemma ldPasting_chernoff_size (params : Parameters) (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    (2 * (params.d : ℝ)) / (1 / (200 * (params.m : ℝ))) ≤ (k : ℝ) := by
  have hm_pos : (0 : ℝ) < (params.m : ℝ) := by exact_mod_cast params.hm
  have hden_pos : (0 : ℝ) < 200 * (params.m : ℝ) := by positivity
  have hkE : (400 * params.m * params.d : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  field_simp [hden_pos.ne']
  nlinarith

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Specialize `lem:chernoff-bernoulli-matrix` to the averaged complete operator
`G = 𝔼_x ∑_g G^x_g` and the paper's `θ = 1/(200m)`.

This is the Bernoulli-tail lower-bound step in `cor:ld-pasting-N-completeness`: the matrix
Chernoff lemma is applied to `S.L G` on the vector state, `bernoulliTailOperator_leftTensor`
identifies its conclusion, and the swap `S.ev_L_eq_ev_R` transfers it to the right-register
`fromHToGBernoulliTailMass`. -/
theorem fromHToGBernoulliTailMass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (kappa : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    1 - kappa * (1 + 1 / (100 * (params.m : ℝ))) -
        Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ))))) ≤
      fromHToGBernoulliTailMass params strategy.state family k := by
  set S := strategy.state
  set G : 𝔓 := family.averagedSubMeas.total
  have hm_one : (1 : ℝ) ≤ params.m := by exact_mod_cast params.hm
  have htheta_pos : (0 : ℝ) < 1 / (200 * (params.m : ℝ)) := by positivity
  have htheta_lt_one : 1 / (200 * (params.m : ℝ)) < 1 :=
    (div_lt_one (by positivity)).2 (by linarith)
  have hchern := (chernoffBernoulliMatrix S.toVecState (1 / (200 * (params.m : ℝ))) k params.d
    (S.L G) kappa htheta_pos htheta_lt_one (ldPasting_chernoff_size params k hk)
    (S.leftTensor_nonneg family.averagedSubMeas.total_nonneg)
    (S.leftTensor_le_one family.averagedSubMeas.total_le_one)
    ⟨hcomplete.averageCompleteness.lowerBound⟩).matrixTailBound.lowerBound
  have hmass_eq : S.ev (bernoulliTailOperator k params.d (S.L G)) =
      fromHToGBernoulliTailMass params S family k := by
    rw [bernoulliTailOperator_leftTensor S G k params.d]
    exact S.ev_L_eq_ev_R _
  have hcoef : kappa / (1 - 1 / (200 * (params.m : ℝ))) ≤
      kappa * (1 + 1 / (100 * (params.m : ℝ))) := by
    rw [← mul_one_div]
    exact mul_le_mul_of_nonneg_left (ldPasting_theta_inv_le params)
      (kappa_nonneg_of_complete params strategy family hcomplete)
  rw [ldPasting_chernoff_exponent_eq params k] at hchern
  change S.ev (bernoulliTailOperator k params.d (S.L G)) ≥ _ at hchern
  linarith

/-- Internal form of `cor:ld-pasting-N-completeness` from the two preceding
mass-comparison inputs.

This theorem isolates the scalar assembly after `lem:over-all-outcomes`,
`lem:from-H-to-G`, and the Bernoulli-tail lower bound have already been
established. -/
theorem ldPastingNCompleteness_of_overAllOutcomes_fromHToG_tail
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (family : IdxPolyFamily params 𝔓)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hOAO : OverAllOutcomesStatement params strategy family eps delta gamma zeta k)
    (hFrom : FromHToGStatement params strategy strategy.state family gamma zeta k)
    (htail :
      1 - kappa * (1 + 1 / (100 * (params.m : ℝ))) -
          Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ))))) ≤
        fromHToGBernoulliTailMass params strategy.state family k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (ldPastingInInductionNu params k eps delta gamma zeta) k := by
  have happrox := overAllOutcomesError_add_fromHToGError_le_ldPastingNu params
    eps delta gamma zeta k hk_pos heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  have hOAO_abs := (abs_le.mp hOAO.totalOutcomeExpansion).1
  have hFrom_abs := (abs_le.mp hFrom.bernoulliPolynomialRewrite).1
  -- The expansion mass of `lem:over-all-outcomes` is the all-outcomes mass of
  -- `lem:from-H-to-G` at the strategy state, by definition.
  change _ ≤ _ - fromHToGAllOutcomesMass params strategy strategy.state family k at hOAO_abs
  refine ⟨⟨?_⟩⟩
  change overAllOutcomesPastedMass params strategy family k ≥
    ldPastingCompletenessLowerBound params kappa _ k
  simp only [ldPastingCompletenessLowerBound]
  linarith

/-- `cor:ld-pasting-N-completeness` once the Bernoulli-tail lower bound is
supplied explicitly.

This records the downstream scalar algebra after `lem:over-all-outcomes` and
`lem:from-H-to-G`. The hypothesis `htail` is exactly the `θ = 1 / (200m)`
specialization of `lem:chernoff-bernoulli-matrix` for the averaged complete
operator `G = \mathbb E_x \sum_g G^x_g`, expressed as the concrete
`fromHToGBernoulliTailMass` lower bound with error
`κ · (1 + 1/(100m)) + exp(-k / (80000 m²))`. -/
theorem ldPastingNCompleteness_of_tailLowerBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (_hk : 400 * params.m * params.d ≤ k)
    (htail :
      1 - kappa * (1 + 1 / (100 * (params.m : ℝ))) -
          Real.exp (-((k : ℝ) / (80000 * ((params.m : ℝ) ^ (2 : ℕ))))) ≤
        fromHToGBernoulliTailMass params strategy.state family k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (ldPastingInInductionNu params k eps delta gamma zeta) k :=
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hzeta_nonneg := IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons
  ldPastingNCompleteness_of_overAllOutcomes_fromHToG_tail params strategy
    eps delta gamma kappa zeta (eps_nonneg_of_isGood params.next strategy hgood)
    (delta_nonneg_of_isGood params.next strategy hgood) hgamma_nonneg hzeta_nonneg family k hk_pos
    (overAllOutcomes params strategy eps delta gamma zeta
      hgood hgamma_le hzeta_le hdq_le hd family hcons hself hbound k)
    (fromHToG params strategy family eps delta gamma zeta
      hgamma_nonneg hzeta_nonneg hgamma_le hzeta_le hdq_le hgood hcons hself hbound k)
    htail

/-- `cor:ld-pasting-N-completeness`. -/
theorem ldPastingNCompleteness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (ldPastingInInductionNu params k eps delta gamma zeta) k :=
  ldPastingNCompleteness_of_tailLowerBound params strategy
    eps delta gamma kappa zeta hgood hgamma_le hzeta_le hdq_le hd
    family hcons hself hbound k hk_pos hk
    (fromHToGBernoulliTailMass_lower_bound params strategy kappa family hcomplete k hk)

/-- Internal form of `cor:ld-pasting-N-completeness` from the Section 11
commutativity conclusion. -/
theorem ldPastingNCompleteness_ofComMain_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hcom : Commutativity.ComMainConclusion params strategy family gamma zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (ldPastingInInductionNu params k eps delta gamma zeta) k :=
  ldPastingNCompleteness_of_overAllOutcomes_fromHToG_tail params strategy
    eps delta gamma kappa zeta
    ((strategy.state.bipartiteConsError_nonneg
      (uniformDistribution (AxisParallelTestSample params.next))
      (axisParallelPointAnswerFamily strategy) (axisParallelLineAnswerFamily strategy)).trans
      haxis)
    ((strategy.state.bipartiteSSCError_nonneg (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)).trans hself_good)
    hgamma_nonneg hzeta_nonneg family k hk_pos
    (overAllOutcomes_ofComMain_of_axis_self params strategy
      eps delta gamma zeta haxis hself_good hgamma_nonneg hgamma_le
      hzeta_nonneg hzeta_le hdq_le hd family hcons hself hcom k)
    (fromHToG_ofComMain params strategy family gamma zeta
      hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le hself hcom k)
    (fromHToGBernoulliTailMass_lower_bound params strategy kappa family hcomplete k hk)

/-- `lem:ld-pasting-sub-measurement`. -/
theorem ldPastingSubMeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : SubMeas (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      H = constructedPastedSubMeas params family k ∧
        LdPastingSubMeasConclusion params strategy family H eps delta gamma kappa zeta k :=
  ⟨constructedPastedSubMeas params family k, rfl,
    { pointConsistency := hAConsistency_submeas params strategy eps delta gamma zeta
        hgood hgamma_le hzeta_le hdq_le hd family hcons hself hbound k hk_pos
      completeness := (ldPastingNCompleteness params strategy eps delta gamma kappa zeta
        hgood hgamma_le hzeta_le hdq_le hd
        family hcomplete hcons hself hbound k hk_pos hk).completenessBound }⟩

/-- Restricted nontrivial-regime Lean form of `thm:ld-pasting`.

The source theorem is `references/ldt-paper/ld-pasting.tex`, lines 12--50.
Lines 52--55 explain that the proof may assume the nontrivial regime
`eps, delta, gamma, zeta, d / q ≤ 1`, since the complementary cases are
trivial.  This declaration states the restricted assumptions
`gamma ≤ 1`, `zeta ≤ 1`, `params.d ≤ params.q`, `0 < params.d`, and `1 ≤ k`.
The unrestricted statement aligned with the paper is `ldPasting`; the
degree-zero complementary branch is handled separately by
`ldPastingDegreeZeroBranch`. -/
theorem ldPastingNontrivial
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      H = constructedPastedMeasurement params family k ∧
        LdPastingConclusion params strategy family H eps delta gamma kappa zeta k :=
  ⟨constructedPastedMeasurement params family k, rfl,
    { pointConsistency := hAConsistency_completed params strategy eps delta gamma kappa zeta
        family k
        (hAConsistency_submeas params strategy eps delta gamma zeta
          hgood hgamma_le hzeta_le hdq_le hd family hcons hself hbound k hk_pos)
        (ldPastingNCompleteness params strategy eps delta gamma kappa zeta
          hgood hgamma_le hzeta_le hdq_le hd
          family hcomplete hcons hself hbound k hk_pos hk).completenessBound }⟩

/-- Trivial consistency conclusion when the target pasting error is at least `1`.

The consistency defect of two submeasurements against the state of a symmetric
model is always at most `1`; hence a scalar lower bound
`1 ≤ ldPastingInInductionError ...` is enough to produce the final conclusion
with a distinguished trivial measurement. -/
theorem ldPasting_of_one_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (k : ℕ)
    (herror : 1 ≤ ldPastingInInductionError params k eps delta gamma kappa zeta) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k :=
  ⟨Measurement.trivialDistinguishedOutcome (fallbackInterpolatedPolynomial params),
    { pointConsistency := ⟨(strategy.state.bipartiteConsError_uniform_le_one
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (Measurement.trivialDistinguishedOutcome
            (fallbackInterpolatedPolynomial params)).toSubMeas)).trans herror⟩ }⟩

/-- Trivial consistency conclusion from the complementary scalar branches.

If `k` is positive, it suffices to show that the `ν` term in the pasting error
is at least `1`; if `k = 0`, the exponential term already gives the trivial
bound. -/
theorem ldPasting_of_one_le_nu_or_zero_k
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (k : ℕ)
    (hnu : 1 ≤ k → 1 ≤ ldPastingInInductionNu params k eps delta gamma zeta) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  have hkappa_nonneg := kappa_nonneg_of_complete params strategy family hcomplete
  refine ldPasting_of_one_le_error params strategy eps delta gamma kappa zeta family k ?_
  rcases Nat.eq_zero_or_pos k with hk_zero | hk_pos
  · exact one_le_ldPastingError_of_k_eq_zero params k eps delta gamma kappa zeta
      hkappa_nonneg hk_zero
  · exact one_le_ldPastingError_of_one_le_nu params k eps delta gamma kappa zeta
      hkappa_nonneg (hnu hk_pos)

/-- Complementary branch for `thm:ld-pasting` when `gamma > 1`.

Paper origin: `references/ldt-paper/ld-pasting.tex:52-55`, where this is one
of the large-error cases in which the final consistency bound is trivial.
This is one of the proved complementary cases for `thm:ld-pasting`. -/
theorem ldPastingLargeGammaBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hgamma : 1 < gamma) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k :=
  ldPasting_of_one_le_nu_or_zero_k params strategy eps delta gamma kappa zeta
    family hcomplete k fun hk_pos =>
      one_le_ldPastingNu_of_large_gamma params strategy eps delta gamma zeta
        hgood family hcons k hk_pos hgamma

/-- Complementary branch for `thm:ld-pasting` when `zeta > 1`.

Paper origin: `references/ldt-paper/ld-pasting.tex:52-55`, where this is one
of the large-error cases in which the final consistency bound is trivial.
This is one of the proved complementary cases for `thm:ld-pasting`. -/
theorem ldPastingLargeZetaBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (_hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hzeta : 1 < zeta) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k :=
  ldPasting_of_one_le_nu_or_zero_k params strategy eps delta gamma kappa zeta
    family hcomplete k fun hk_pos =>
      one_le_ldPastingNu_of_large_zeta params strategy eps delta gamma zeta
        hgood k hk_pos hzeta

/-- Complementary branch for `thm:ld-pasting` when `d > q`.

Paper origin: `references/ldt-paper/ld-pasting.tex:52-55`, where this is the
large-error case `(d/q) ≥ 1`.  This is one of the proved complementary cases
for `thm:ld-pasting`. -/
theorem ldPastingLargeDegreeRatioBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hdq : params.q < params.d) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k :=
  ldPasting_of_one_le_nu_or_zero_k params strategy eps delta gamma kappa zeta
    family hcomplete k fun hk_pos =>
      one_le_ldPastingNu_of_large_degreeRatio params strategy eps delta gamma zeta
        hgood family hcons k hk_pos hdq

/-- Complementary branch for `thm:ld-pasting` when `k = 0`.

This branch is a boundary case for the reduction to the nontrivial theorem,
whose proof assumes `1 ≤ k`.  The scalar calculation showing that the
exponential term gives the trivial bound is the vendored
`one_le_ldPastingError_of_k_eq_zero`. -/
theorem ldPastingZeroKBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (_hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (_hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hk_zero : k = 0) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k :=
  ldPasting_of_one_le_error params strategy eps delta gamma kappa zeta family k
    (one_le_ldPastingError_of_k_eq_zero params k eps delta gamma kappa zeta
      (kappa_nonneg_of_complete params strategy family hcomplete) hk_zero)

/-- Degree-zero complementary branch for the unrestricted source theorem.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-55`.  The paper's
large-error reduction names the cases
`eps, delta, gamma, zeta, d/q ≥ 1`; it does not explicitly add `0 < d` as a
hypothesis of `thm:ld-pasting`.  Thus the Lean theorem should not add `0 < d`
as an assumption of that cited theorem.

Upstream issue #1622 recorded the need for a direct proof of this degree-zero branch; see
`docs/paper-gaps/issue-1622-ld-pasting-degree-zero.tex` upstream.  The
nontrivial argument cannot simply be reused: its `hBConsistency` aggregation
passes from distinct sampled heights to independent sampled heights and absorbs
the resulting `k^2/q` loss through the displayed `(d/q)^(1/32)` term.  When
`d = 0`, that term is zero, so the branch requires a separate argument rather
than an additional hypothesis on `ldPasting`. -/
theorem ldPastingDegreeZeroBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hd_zero : params.d = 0)
    (_hk_pos : 1 ≤ k) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k :=
  let ⟨H, _hHdef, hH⟩ := degreeZeroPastedPointConsistency params strategy
    eps delta gamma kappa zeta hgood family hcomplete hcons hd_zero k
  ⟨H, { pointConsistency := hH }⟩

/-- Projection from the restricted nontrivial construction.

The restricted construction theorem `ldPastingNontrivial` proves the nontrivial
analytic regime for the canonical pasted measurement.  This auxiliary statement
records the projection from the restricted construction theorem to the conclusion
needed by the unrestricted theorem, without changing the statement of
`thm:ld-pasting`. -/
theorem ldPastingNontrivialPublicBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k :=
  let ⟨H, _hHdef, hH⟩ := ldPastingNontrivial params strategy eps delta gamma kappa zeta
    hgood hgamma_le hzeta_le hdq_le hd family hcomplete hcons hself hbound k hk_pos hk
  ⟨H, hH⟩

/-- Paper-aligned form of `thm:ld-pasting`.

Paper origin: `references/ldt-paper/ld-pasting.tex`, lines 12--50.  The
following lines 52--55 explain that the proof may restrict to the regime
`eps, delta, gamma, zeta, d / q ≤ 1`, because the complementary cases are
trivial.  The restricted theorem `ldPastingNontrivial` proves the nontrivial
regime, and the large-`gamma`, large-`zeta`, large-`d / q`, and `k = 0`
complementary branches are proved above, including the degree-zero case, so
this declaration keeps the unrestricted paper statement visible without adding
the non-paper assumptions from the restricted theorem. -/
theorem ldPasting
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next 𝔓 K)
    (eps delta gamma kappa zeta : ℝ)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params 𝔓)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (MIPStarRE.LDT.Polynomial params.next) 𝔓,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  rcases le_or_gt gamma 1 with hgamma_le | hgamma
  · rcases le_or_gt zeta 1 with hzeta_le | hzeta
    · rcases le_or_gt params.d params.q with hdq_le | hdq
      · rcases Nat.eq_zero_or_pos k with hk_zero | hk_pos
        · exact ldPastingZeroKBranch params strategy eps delta gamma kappa zeta
            hgood family hcomplete hcons hself hbound k hk hk_zero
        · rcases Nat.eq_zero_or_pos params.d with hd_zero | hd
          · exact ldPastingDegreeZeroBranch params strategy eps delta gamma kappa zeta
              hgood family hcomplete hcons hself hbound k hk hd_zero hk_pos
          · exact ldPastingNontrivialPublicBranch params strategy eps delta gamma kappa zeta
              hgood hgamma_le hzeta_le hdq_le hd family hcomplete hcons hself hbound
              k hk_pos hk
      · exact ldPastingLargeDegreeRatioBranch params strategy eps delta gamma kappa zeta
          hgood family hcomplete hcons hself hbound k hk hdq
    · exact ldPastingLargeZetaBranch params strategy eps delta gamma kappa zeta
        hgood family hcomplete hcons hself hbound k hk hzeta
  · exact ldPastingLargeGammaBranch params strategy eps delta gamma kappa zeta
      hgood family hcomplete hcons hself hbound k hk hgamma

end MIPRE.LIDT.Co.Pasting

end
