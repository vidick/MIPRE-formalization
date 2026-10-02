/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
SelfImprovement/Theorems/Results/HelperSSC/PostDeleteA.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.SelfImprovement.Theorems.Results.HelperSSC.Core

@[expose] public section

/-!
# Helper strong self-consistency bounds: post-delete transports

Post-`delete-an-A` transport lemmas culminating in the moved-quantity bound used before the
residual-chain assembly: the counterpart of the vendored
`SelfImprovement/Theorems/Results/HelperSSC/PostDeleteA.lean` (under
`MIPRE/Background/LIDT/MIPStarRE/LDT/`) in the port of `planning/c6b-plan.md` (milestone M10,
section "Port conventions").

## Contents

- `helper_pair_sandwich_operator_sum_le`: `∑_{h,h'} (X_h H_{h'} X_h) ⊗ T_h ≤ ∑_h X_h² ⊗ T_h` for
  self-adjoint `X_h`, and `helper_pair_tensor_mass_le_one`: `∑_{h,h'} ev(H_{h'} ⊗ T_h) ≤ 1`.
- The two factors of the `eq:swap-u-for-v-attack-of-the-clones` Cauchy--Schwarz bound:
  `helperDeleteA_clone_variance_factor_le_globalVarianceDeviation_sum` and
  `helperDeleteA_clone_mass_factor_le_one`, and the bound itself,
  `helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt`.
- `helper_moveOverV_C_contraction` and the `eq:move-over-v` bound
  `helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta`.

A strategy is a `SymStrat params 𝔓 K`; the polynomial submeasurement `T`, the sandwiched
submeasurement `H^u` and the point projectors live in `𝔓`, and every scalar is
`strategy.state.ev` of a joint operator `strategy.state.opTensor X Y`; `leftTensor` and
`rightTensor` are `strategy.state.L` and `strategy.state.R`, and `Xᴴ` is `star X`. The vendored
`helper_pair_sandwich_operator_sum_le` names no state, its `opTensor` being the Kronecker product
on the carrier; here it takes the model `(S : SymModel 𝔓 K)` as an explicit first argument, as Co
`AddInUStep34AndTransfer/Selected`'s `addInU_selected_sandwich_tensor_if_sum_le` does, and its
hypothesis `(X h)ᴴ = X h` is `star (X h) = X h`.

**Global variance.** The variance factor is bounded by M6's summed deviation
`∑_g globalVarianceDeviationAtPolynomial params strategy strategy.state T g` (Co
`GlobalVariance/Defs/Families`), the independent-points variance of the family
`u ↦ S.L (A^u_{g(u)}) * S.R √T_g` on `strategy.state` itself rather than the vendored weighted
state; it is identified through Co `weightedPointConditionedOperator_sq`, exactly where the
vendored proof rewrites with its vendored counterpart, so the statement keeps its vendored text.

**Placement bounds.** The two operator bounds `∑_{h,h'} H_{h'} ⊗ T_h = H.total ⊗ T.total ≤ 1` of
`helper_pair_tensor_mass_le_one` and `helper_moveOverV_C_contraction`, which the vendored file
proves twice through `opTensor_le_leftTensor` and `leftTensor_le_one (ι₂ := ι)`, are the private
`pair_opTensor_sum_le_one`, closed by the keystone's `S.opTensor_le_one`.

**Proofs that differ from the vendored ones.**
- The nine Hermitian computations (`Matrix.conjTranspose_sub`, `Matrix.conjTranspose_mul`,
  `Matrix.conjTranspose_sum`, `Matrix.star_eq_conjTranspose`, `leftTensor_conjTranspose`,
  `rightTensor_conjTranspose` with `SubMeas.outcome_hermitian`) are `IsSelfAdjoint.of_nonneg`
  of the keystone's positivity, `IsSelfAdjoint.sub` and `star_mul`; the positivity of
  `(A^u - A^v) H (A^u - A^v)` through `star_left_conjugate_nonneg` is
  `IsSelfAdjoint.conjugate_nonneg`.
- `helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt` applies the sandwich Cauchy--Schwarz
  `S.ev_opTensor_sandwich_abs_le_sqrt` with `X = 1`, `Y = A^u - A^v` on the difference
  `ev((H (A^u - A^v)) ⊗ T)`, where the vendored proof takes `X = A^u - A^v`, `Y = 1` after
  conjugating it to `ev(((A^u - A^v) H) ⊗ T)`; the conjugation step disappears, the two factors
  come in the other order, and the closing absorption is the imported
  `addInU_le_sqrt_of_factor_bounds_left` in place of `…_right`.
- In `helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta` the collapse of
  `∑_a ∑_{(h,h')}` onto the fibre `a = h(v)` is the private `sum_fiber_collapse_pair` (the
  vendored `hAvg`), and the self-consistency input is passed to the Co
  `Preliminaries.closenessOfInnerProduct_right` as Co `AddInUStep12/Raw` does.

**Dropped hypotheses.** The vendored `helper_pair_tensor_mass_le_one` closes with
`ev_one_of_isNormalized strategy.state strategy.isNormalized` (vendored line 113), and the vendored
`helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta` passes
`strategy.isNormalized` to `closenessOfInnerProduct_right` (vendored line 607); here
`strategy.state.ev_one_of_isNormalized` and the ported Cauchy--Schwarz bound take no hypothesis.
No statement of the vendored file carries a swap, density or normalization hypothesis, so no
statement changed beyond the translation. The file sets no option, the vendored file-wide
`respectTransparency false` not being needed.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.SelfImprovement

open MIPStarRE.LDT (Parameters FieldModel Point Fq avgOver uniformDistribution avgOver_congr
  avgOver_mono avgOver_sub avgOver_sum avgOver_uniform_fst avgOver_uniform_le_const
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.ExpansionHypercubeGraph (avgOver_independentPointPair_eq_uniform_prod)
open MIPStarRE.LDT.GlobalVariance (localVarianceOfPointsError)
open MIPStarRE.LDT.SelfImprovement (selfImprovementVarianceError
  addInU_le_sqrt_of_factor_bounds_left)
open MIPRE.LIDT.Co.GlobalVariance (pointConditionedOutcomeOperatorAtPolynomial
  localVarianceDeviationAtPolynomial globalVarianceDeviationAtPolynomial
  weightedPointConditionedOperator_sq globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### Post-`delete-an-A` transports -/

/-- The point operators `A^u_{h(u)}` are self-adjoint, being positive. -/
private theorem pointConditionedOutcomeOperatorAtPolynomial_isSelfAdjoint'
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params 𝔓 K)
    (h : MIPStarRE.LDT.Polynomial params) (w : Point params) :
    IsSelfAdjoint (pointConditionedOutcomeOperatorAtPolynomial params strategy h w) :=
  .of_nonneg ((strategy.pointMeasurement w).toSubMeas.outcome_pos (h w))

/-- The pair sum `∑_{(h, h')} H_{h'} ⊗ T_h` of two submeasurements is `H.total ⊗ T.total`, an
effect. -/
private theorem pair_opTensor_sum_le_one (S : SymModel 𝔓 K) {α β : Type*} [Fintype α]
    [Fintype β] (H : SubMeas β 𝔓) (T : SubMeas α 𝔓) :
    (∑ hh : α × β, S.opTensor (H.outcome hh.2) (T.outcome hh.1)) ≤ 1 := by
  rw [Fintype.sum_prod_type]
  dsimp only
  calc
    _ = ∑ h : α, S.opTensor H.total (T.outcome h) :=
        Finset.sum_congr rfl fun h _ => by rw [← S.opTensor_sum_left_univ, H.sum_eq_total]
    _ = S.opTensor H.total T.total := by rw [← S.opTensor_sum_right_univ, T.sum_eq_total]
    _ ≤ 1 := S.opTensor_le_one H.total_nonneg H.total_le_one T.total_le_one

/-- Collapsing a double sum `∑ₐ ∑_b ev(X a b)` onto the fibre `a = f(b)`, when `X a b` vanishes
off it (the vendored `hAvg`). -/
private theorem sum_fiber_collapse_pair {α β : Type*} [Fintype α] [Fintype β]
    (V : VecState K) (f : β → α) (X : α → β → K →L[ℂ] K) (hX : ∀ a b, f b ≠ a → X a b = 0) :
    ∑ a : α, ∑ b : β, V.ev (X a b) = ∑ b : β, V.ev (X (f b) b) :=
  Finset.sum_comm.trans <| Finset.sum_congr rfl fun b _ =>
    Finset.sum_eq_single (f b) (fun a _ ha => by rw [hX a b (Ne.symm ha), V.ev_zero])
      fun hm => (hm (Finset.mem_univ _)).elim

/-- The pair sandwich `∑_{(h, h')} (X_h H_{h'} X_h) ⊗ T_h` is at most `∑_h X_h² ⊗ T_h` for
self-adjoint `X_h`: summing over `h'` gives `H.total ≤ 1`. -/
theorem helper_pair_sandwich_operator_sum_le
    (S : SymModel 𝔓 K)
    (params : Parameters) [FieldModel params.q]
    (H T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (X : MIPStarRE.LDT.Polynomial params → 𝔓)
    (hX_herm : ∀ h : MIPStarRE.LDT.Polynomial params, star (X h) = X h) :
    (∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
        S.opTensor (X hh.1 * H.outcome hh.2 * X hh.1) (T.outcome hh.1)) ≤
      ∑ h : MIPStarRE.LDT.Polynomial params, S.opTensor (X h * X h) (T.outcome h) := by
  have hX : ∀ h, IsSelfAdjoint (X h) := hX_herm
  calc
    _ = ∑ h : MIPStarRE.LDT.Polynomial params,
          S.opTensor (X h * H.total * X h) (T.outcome h) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun h _ => ?_
        dsimp only
        rw [← S.opTensor_sum_left_univ, ← Finset.sum_mul, ← Finset.mul_sum, H.sum_eq_total]
    _ ≤ _ := Finset.sum_le_sum fun h _ => by
        simpa only [mul_one] using S.opTensor_mono_left
          ((hX h).conjugate_le_conjugate H.total_le_one) (T.outcome_pos h)

/-- The pair mass `∑_{(h, h')} ev(H_{h'} ⊗ T_h)` of two submeasurements is at most `1`. -/
theorem helper_pair_tensor_mass_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (H T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    (∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
        strategy.state.ev (strategy.state.opTensor (H.outcome hh.2) (T.outcome hh.1))) ≤ 1 := by
  rw [← strategy.state.ev_sum]
  exact (strategy.state.ev_mono _ _ (pair_opTensor_sum_le_one strategy.state H T)).trans_eq
    strategy.state.ev_one_of_isNormalized

/-- The variance factor of `eq:swap-u-for-v-attack-of-the-clones` is at most the summed
global-variance deviation: the sandwich `(A^u - A^v) H^u_{h'} (A^u - A^v)` is dominated by
`(A^u - A^v)²` after summing over `h'`, and averaging over independent points gives the
deviation. -/
theorem helperDeleteA_clone_variance_factor_le_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
        let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
        strategy.state.ev
          (strategy.state.opTensor ((Au - Av) * Hh' * (Au - Av)) (T.outcome hh.1))) ≤
      ∑ g : MIPStarRE.LDT.Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g := by
  have hA := pointConditionedOutcomeOperatorAtPolynomial_isSelfAdjoint' params strategy
  calc
    _ ≤ avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ g : MIPStarRE.LDT.Polynomial params,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy g uv.1
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy g uv.2
            strategy.state.ev
              (strategy.state.opTensor (star (Au - Av) * (Au - Av)) (T.outcome g))) :=
        avgOver_mono _ _ _ fun uv => by
          let X : MIPStarRE.LDT.Polynomial params → 𝔓 := fun h =>
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 -
              pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          have hX : ∀ h, IsSelfAdjoint (X h) := fun h => (hA h uv.1).sub (hA h uv.2)
          calc
            _ = strategy.state.ev
                  (∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
                    strategy.state.opTensor
                      (X hh.1 * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome
                        hh.2 * X hh.1) (T.outcome hh.1)) :=
                (strategy.state.ev_sum _).symm
            _ ≤ strategy.state.ev (∑ h : MIPStarRE.LDT.Polynomial params,
                  strategy.state.opTensor (X h * X h) (T.outcome h)) :=
                strategy.state.ev_mono _ _ (helper_pair_sandwich_operator_sum_le strategy.state
                  params _ T X fun h => (hX h).star_eq)
            _ = _ := by
                rw [strategy.state.ev_sum]
                exact Finset.sum_congr rfl fun h _ => by
                  dsimp only
                  rw [(hX h).star_eq]
    _ = _ := by
        rw [avgOver_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [globalVarianceDeviationAtPolynomial, avgOver_independentPointPair_eq_uniform_prod]
        exact avgOver_congr _ _ _ fun uv =>
          congrArg strategy.state.ev (weightedPointConditionedOperator_sq params strategy T g
            uv.1 uv.2).symm

/-- The mass factor of `eq:swap-u-for-v-attack-of-the-clones` is at most `1`. -/
theorem helperDeleteA_clone_mass_factor_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
        strategy.state.ev
          (strategy.state.opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
            (T.outcome hh.1))) ≤ 1 :=
  avgOver_uniform_le_const _ 1 fun uv =>
    helper_pair_tensor_mass_le_one params strategy
      (sandwichedPolynomialSubMeasAt params strategy T uv.1) T

-- This post-delete transport combines the clone variance factor estimate with
-- the local-to-global variance transfer.
/-- Paper `eq:swap-u-for-v-attack-of-the-clones`: after `delete-an-A`, the
remaining point projector may be evaluated at an independent point at cost
`√ζ_variance`. -/
theorem helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (eps delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hlocal :
      (∑ g : MIPStarRE.LDT.Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |helperDeleteAQuantity params strategy T -
      helperDeleteAClonedQuantity params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) := by
  have hA := pointConditionedOutcomeOperatorAtPolynomial_isSelfAdjoint' params strategy
  let A := pointConditionedOutcomeOperatorAtPolynomial params strategy
  let H := fun u : Point params => sandwichedPolynomialSubMeasAt params strategy T u
  let t : Point params × Point params →
      MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params → ℝ := fun uv hh =>
    strategy.state.ev
      (strategy.state.opTensor ((H uv.1).outcome hh.2 * (A hh.1 uv.1 - A hh.1 uv.2))
        (T.outcome hh.1))
  let x : Point params × Point params →
      MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params → ℝ := fun uv hh =>
    strategy.state.ev
      (strategy.state.opTensor
        ((A hh.1 uv.1 - A hh.1 uv.2) * (H uv.1).outcome hh.2 * (A hh.1 uv.1 - A hh.1 uv.2))
        (T.outcome hh.1))
  let y : Point params × Point params →
      MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params → ℝ := fun uv hh =>
    strategy.state.ev (strategy.state.opTensor ((H uv.1).outcome hh.2) (T.outcome hh.1))
  have hdiff_eq :
      helperDeleteAQuantity params strategy T - helperDeleteAClonedQuantity params strategy T =
        avgOver (uniformDistribution (Point params × Point params))
          (fun uv => ∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
            t uv hh) := by
    rw [helperDeleteAQuantity, ← avgOver_uniform_fst (β := Point params),
      helperDeleteAClonedQuantity, ← avgOver_sub]
    refine avgOver_congr _ _ _ fun uv => ?_
    rw [Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [← strategy.state.ev_sub, strategy.state.opTensor_sub_left, ← mul_sub]
  have ht : ∀ uv hh, |t uv hh| ≤ Real.sqrt (y uv hh) * Real.sqrt (x uv hh) := fun uv hh => by
    have h := strategy.state.ev_opTensor_sandwich_abs_le_sqrt 1 (A hh.1 uv.1 - A hh.1 uv.2)
      ((H uv.1).outcome hh.2) (T.outcome hh.1) ((H uv.1).outcome_pos hh.2) (T.outcome_pos hh.1)
    have hX : IsSelfAdjoint (A hh.1 uv.1 - A hh.1 uv.2) := (hA hh.1 uv.1).sub (hA hh.1 uv.2)
    simp only [star_one, one_mul, mul_one, hX.star_eq] at h
    exact h
  have hx : ∀ uv hh, 0 ≤ x uv hh := fun uv hh =>
    strategy.state.ev_nonneg_of_psd _ (strategy.state.opTensor_nonneg
      (((hA hh.1 uv.1).sub (hA hh.1 uv.2)).conjugate_nonneg ((H uv.1).outcome_pos hh.2))
      (T.outcome_pos hh.1))
  have hy : ∀ uv hh, 0 ≤ y uv hh := fun uv hh =>
    strategy.state.ev_nonneg_of_psd _ (strategy.state.opTensor_nonneg
      ((H uv.1).outcome_pos hh.2) (T.outcome_pos hh.1))
  rw [hdiff_eq]
  exact addInU_le_sqrt_of_factor_bounds_left
    (MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz _ t y x ht hy hx)
    (helperDeleteA_clone_mass_factor_le_one params strategy T)
    ((helperDeleteA_clone_variance_factor_le_globalVarianceDeviation_sum params strategy T).trans
      (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
        params strategy eps delta T hlocal))

/-- The Cauchy--Schwarz side condition of `eq:move-over-v`: with
`C_a = ∑_{(h, h') : h(v) = a} H^u_{h'} ⊗ T_h`, `∑ₐ C_a^* C_a ≤ 1`. -/
theorem helper_moveOverV_C_contraction
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        star (∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
          (if hh.1 uv.2 = a then
            strategy.state.opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
              (T.outcome hh.1)
          else 0)) *
        (∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
          (if hh.1 uv.2 = a then
            strategy.state.opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
              (T.outcome hh.1)
          else 0)) ≤
      (1 : K →L[ℂ] K) := by
  let H := sandwichedPolynomialSubMeasAt params strategy T uv.1
  let C : Fq params → K →L[ℂ] K := fun a =>
    ∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
      if hh.1 uv.2 = a then strategy.state.opTensor (H.outcome hh.2) (T.outcome hh.1) else 0
  have hC0 : ∀ a, 0 ≤ C a := fun a => Finset.sum_nonneg fun hh _ => by
    split_ifs
    · exact strategy.state.opTensor_nonneg (H.outcome_pos hh.2) (T.outcome_pos hh.1)
    · exact le_rfl
  have hsum : ∑ a, C a ≤ 1 := by
    refine le_of_eq_of_le ?_ (pair_opTensor_sum_le_one strategy.state H T)
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun hh _ => ?_)
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  have hC1 : ∀ a, C a ≤ 1 := fun a =>
    (Finset.single_le_sum (fun b _ => hC0 b) (Finset.mem_univ a)).trans hsum
  calc
    _ = ∑ a : Fq params, C a * C a :=
        Finset.sum_congr rfl fun a _ =>
          congrArg (· * C a) (IsSelfAdjoint.of_nonneg (hC0 a)).star_eq
    _ ≤ ∑ a : Fq params, C a := Finset.sum_le_sum fun a _ => sq_le_self (hC0 a) (hC1 a)
    _ ≤ 1 := hsum

/-- Paper `eq:move-over-v`: the cloned `delete-an-A` quantity can be moved to
the right tensor factor at cost `√(2δ)` from point self-consistency. -/
theorem helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params 𝔓 K)
    (delta : ℝ)
    (T : SubMeas (MIPStarRE.LDT.Polynomial params) 𝔓)
    (hssc : strategy.state.BipartiteSSCRel (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |helperDeleteAClonedQuantity params strategy T -
      helperMoveOverVQuantity params strategy T| ≤
        Real.sqrt (2 * delta) := by
  let H := fun u : Point params => sandwichedPolynomialSubMeasAt params strategy T u
  let Aop : Point params × Point params → Fq params → K →L[ℂ] K :=
    fun uv a => strategy.state.L ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → K →L[ℂ] K :=
    fun uv a => strategy.state.R ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params →
      MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params → K →L[ℂ] K :=
    fun uv a hh =>
      if hh.1 uv.2 = a then
        strategy.state.opTensor ((H uv.1).outcome hh.2) (T.outcome hh.1)
      else 0
  have hAB :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        strategy.state.qSDDCore
          (fun a : Fq params => star (Aop uv a)) (fun a : Fq params => star (Bop uv a))) ≤
        2 * delta := by
    refine le_of_eq_of_le (avgOver_congr _ _ _ fun uv => ?_)
      (addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc).squaredDistanceBound
    have hpos := fun a => (strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a
    simp only [Aop, Bop,
      (IsSelfAdjoint.of_nonneg (strategy.state.leftTensor_nonneg (hpos _))).star_eq,
      (IsSelfAdjoint.of_nonneg (strategy.state.rightTensor_nonneg (hpos _))).star_eq]
    rfl
  have hcs := Preliminaries.closenessOfInnerProduct_right strategy.state
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB (helper_moveOverV_C_contraction params strategy T)
  have hCop : ∀ uv a hh, hh.1 uv.2 ≠ a → Cop uv a hh = 0 := fun _ _ _ ha => ite_eq_right ha
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
          strategy.state.ev (Aop uv a * Cop uv a hh)) -
        (∑ a : Fq params,
          ∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
            strategy.state.ev (Bop uv a * Cop uv a hh)) =
      (∑ h : MIPStarRE.LDT.Polynomial params,
        ∑ h' : MIPStarRE.LDT.Polynomial params,
          strategy.state.ev
            (strategy.state.opTensor
              (((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h') *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)
              (T.outcome h))) -
        (∑ h : MIPStarRE.LDT.Polynomial params,
          ∑ h' : MIPStarRE.LDT.Polynomial params,
            strategy.state.ev
              (strategy.state.opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h')
                (T.outcome h *
                  pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2))) := by
    intro uv
    rw [sum_fiber_collapse_pair strategy.state (fun hh => hh.1 uv.2)
        (fun a hh => Aop uv a * Cop uv a hh) fun a hh ha => by rw [hCop uv a hh ha, mul_zero],
      sum_fiber_collapse_pair strategy.state (fun hh => hh.1 uv.2)
        (fun a hh => Bop uv a * Cop uv a hh) fun a hh ha => by rw [hCop uv a hh ha, mul_zero],
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    have hH := fun h' => IsSelfAdjoint.of_nonneg ((H uv.1).outcome_pos h')
    have hT := fun h => IsSelfAdjoint.of_nonneg (T.outcome_pos h)
    have hAv := fun h : MIPStarRE.LDT.Polynomial params => IsSelfAdjoint.of_nonneg
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome_pos (h uv.2))
    congr 1
    · refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
      dsimp only [Aop, Cop]
      rw [ite_eq_left rfl, strategy.state.leftTensor_mul_opTensor, ← strategy.state.ev_conjTranspose,
        strategy.state.conjTranspose_opTensor, star_mul, (hH h').star_eq, (hAv h).star_eq,
        (hT h).star_eq]
      rfl
    · refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
      dsimp only [Bop, Cop]
      rw [ite_eq_left rfl, strategy.state.rightTensor_mul_opTensor, ← strategy.state.ev_conjTranspose,
        strategy.state.conjTranspose_opTensor, star_mul, (hH h').star_eq, (hAv h).star_eq,
        (hT h).star_eq]
      rfl
  have hmatch :
      helperDeleteAClonedQuantity params strategy T - helperMoveOverVQuantity params strategy T =
        avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
            ∑ a : Fq params,
              ∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
                strategy.state.ev (Aop uv a * Cop uv a hh)) -
          avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
            ∑ a : Fq params,
              ∑ hh : MIPStarRE.LDT.Polynomial params × MIPStarRE.LDT.Polynomial params,
                strategy.state.ev (Bop uv a * Cop uv a hh)) := by
    rw [← avgOver_sub, helperDeleteAClonedQuantity, helperMoveOverVQuantity, ← avgOver_sub]
    exact avgOver_congr _ _ _ fun uv => (hmatch_pointwise uv).symm
  rw [hmatch]
  exact hcs

end MIPRE.LIDT.Co.SelfImprovement

end
