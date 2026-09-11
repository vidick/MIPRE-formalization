/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/MainTheorem/OneShot.lean
-/
/-
# The legal one-shot strategy and its payoff (Section 7.2)

Statement skeleton for audit nodes 1.4, 1.4.1–1.4.4.
Anchors: 07_main_theorem.tex sec 7.2, eqs main-OT-error, payoff-under-Q,
payoff-under-JA, one-shot-final-payoff.

The absence of `IsPredicate` hypotheses in this file is intentional and
load-bearing: sec 7.2's argument is `[0,1]`-agnostic (its F ∈ [0,1]), and
node 1.6.2 re-consumes this machinery at `[0,1]` weights. Do not "restore"
a predicate hypothesis here.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Game.Strategy
import MIPRE.Background.Repetition.CommutingRepetition.Game.Value
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Main
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.Main
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Scalar
import MIPRE.Background.Repetition.CommutingRepetition.Game.Mixture

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

namespace PreroundedStrategy

variable (P : PreroundedStrategy X Y A B)

/-- The `π`-averaged unhalved ℓ¹ sampling error of a resource against the
ideal pair law — the quantity the sampling theorem controls by
`C_OT (Δ^{1/6} + ξ)`. [07_main_theorem.tex, eq main-OT-error] -/
noncomputable def samplingError
    (R : SamplingResource (P.Hist × X) (P.Hist × Y) A B) : ℝ :=
  ∑ h : P.Hist, ∑ x : X, ∑ y : Y, P.Q h x y *
    ∑ a : A, ∑ b : B,
      |R.answerLaw (h, x) (h, y) a b -
        P.idealCorrelation (h, x) (h, y) a b|

/-- The sampling error is the `π`-average of the ℓ¹ answer-law error —
the exact quantity `otqcs_sampling` controls. -/
theorem samplingError_eq_labelLaw
    (R : SamplingResource (P.Hist × X) (P.Hist × Y) A B) :
    P.samplingError R = ∑ s : P.Hist × X, ∑ t : P.Hist × Y,
      P.labelLaw s t * ∑ a : A, ∑ b : B,
        |R.answerLaw s t a b - P.idealCorrelation s t a b| := by
  unfold samplingError
  exact (P.sum_labelLaw_mul (fun s t => ∑ a : A, ∑ b : B,
    |R.answerLaw s t a b - P.idealCorrelation s t a b|)).symm

/-- The actual expected payoff on a tuple, when the two locally generated
histories agree: `F(h, x, y) = ∑_{a,b} V(a,b|x,y) q̂_{(h,x),(h,y)}(a,b)`,
defined for every tuple including tuples outside the support of `Q`.
[07_main_theorem.tex, display defining F] -/
noncomputable def tuplePayoff (G : Game X Y A B)
    (R : SamplingResource (P.Hist × X) (P.Hist × Y) A B)
    (t : P.Hist × X × Y) : ℝ :=
  ∑ a : A, ∑ b : B, G.payoff t.2.1 t.2.2 a b *
    R.answerLaw (t.1, t.2.1) (t.1, t.2.2) a b

theorem tuplePayoff_nonneg (G : Game X Y A B)
    (R : SamplingResource (P.Hist × X) (P.Hist × Y) A B)
    (t : P.Hist × X × Y) : 0 ≤ P.tuplePayoff G R t :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    mul_nonneg (G.payoff_nonneg _ _ _ _)
      (tracialPairLaw_nonneg R.N _ R.E R.F R.E_pos R.F_pos _ _ _ _)

theorem tuplePayoff_le_one (G : Game X Y A B)
    (R : SamplingResource (P.Hist × X) (P.Hist × Y) A B)
    (t : P.Hist × X × Y) : P.tuplePayoff G R t ≤ 1 := by
  calc P.tuplePayoff G R t
      ≤ ∑ a : A, ∑ b : B, R.answerLaw (t.1, t.2.1) (t.1, t.2.2) a b := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        have h0 := tracialPairLaw_nonneg R.N (fun _ _ => R.Ω) R.E R.F
          R.E_pos R.F_pos (t.1, t.2.1) (t.1, t.2.2) a b
        calc G.payoff t.2.1 t.2.2 a b *
            R.answerLaw (t.1, t.2.1) (t.1, t.2.2) a b
            ≤ 1 * R.answerLaw (t.1, t.2.1) (t.1, t.2.2) a b :=
              mul_le_mul_of_nonneg_right (G.payoff_le_one _ _ _ _) h0
          _ = R.answerLaw (t.1, t.2.1) (t.1, t.2.2) a b := one_mul _
    _ = 1 := tracialPairLaw_sum R.N (fun _ _ => R.Ω) R.E R.F
        (fun _ _ => R.Ω_norm) R.E_sum R.F_sum (t.1, t.2.1) (t.1, t.2.2)

end PreroundedStrategy

/-- Change of measure by total variation (node 1.4.3, generic form;
07_main_theorem.tex, eq payoff-under-JA): for laws `p, q` and a `[0,1]`-
valued observable, expectations differ by at most the (halved) total
variation. -/
theorem abs_expectation_sub_le_totalVariation
    {ι : Type*} [Fintype ι] {p q F : ι → ℝ}
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : (∑ i, p i) = 1)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_sum : (∑ i, q i) = 1)
    (hF0 : ∀ i, 0 ≤ F i) (hF1 : ∀ i, F i ≤ 1) :
    |(∑ i, p i * F i) - ∑ i, q i * F i|
      ≤ Pinsker.finiteTotalVariation p q := by
  have hcenter : (∑ i, p i * F i) - ∑ i, q i * F i
      = ∑ i, (p i - q i) * (F i - 1 / 2) := by
    have hhalf : (∑ i, (p i - q i) * (1 / 2 : ℝ)) = 0 := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, hp_sum, hq_sum]
      ring
    calc (∑ i, p i * F i) - ∑ i, q i * F i
        = (∑ i, (p i - q i) * F i) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i, (p i - q i) * (F i - 1 / 2)) +
            ∑ i, (p i - q i) * (1 / 2 : ℝ) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, (p i - q i) * (F i - 1 / 2) := by rw [hhalf, add_zero]
  rw [hcenter]
  calc |∑ i, (p i - q i) * (F i - 1 / 2)|
      ≤ ∑ i, |(p i - q i) * (F i - 1 / 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |p i - q i| * (1 / 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_le]
        exact ⟨by linarith [hF0 i], by linarith [hF1 i]⟩
    _ = (∑ i, |p i - q i|) / 2 := by
        rw [← Finset.sum_mul]
        ring
    _ = Pinsker.finiteTotalVariation p q := rfl

/-- Payoff under the ideal law (node 1.4.2; 07_main_theorem.tex, eq
payoff-under-Q): an unhalved ℓ¹ answer-law error changes the `[0,1]`-valued
expected payoff by at most half that error, so
`E_Q F ≥ idealSuccess − samplingError/2`. -/
theorem PreroundedStrategy.payoff_under_ideal
    (P : PreroundedStrategy X Y A B) (G : Game X Y A B)
    (R : SamplingResource (P.Hist × X) (P.Hist × Y) A B) :
    P.idealSuccess G - P.samplingError R / 2
      ≤ ∑ t : P.Hist × X × Y, P.Qflat t * P.tuplePayoff G R t := by
  classical
  have hflat : (∑ t : P.Hist × X × Y, P.Qflat t * P.tuplePayoff G R t)
      = ∑ h : P.Hist, ∑ x : X, ∑ y : Y,
          P.Q h x y * P.tuplePayoff G R (h, x, y) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Fintype.sum_prod_type]
    rfl
  have hpt : ∀ (h : P.Hist) (x : X) (y : Y),
      (∑ a : A, ∑ b : B, G.payoff x y a b *
          P.idealCorrelation (h, x) (h, y) a b) -
        (∑ a : A, ∑ b : B,
          |R.answerLaw (h, x) (h, y) a b -
            P.idealCorrelation (h, x) (h, y) a b|) / 2
      ≤ P.tuplePayoff G R (h, x, y) := by
    intro h x y
    have hsumI : (∑ a : A, ∑ b : B,
        P.idealCorrelation (h, x) (h, y) a b) = 1 :=
      tracialPairLaw_sum P.N P.u P.A_ P.B_ P.u_norm P.A_sum P.B_sum
        (h, x) (h, y)
    have hsumR : (∑ a : A, ∑ b : B,
        R.answerLaw (h, x) (h, y) a b) = 1 :=
      tracialPairLaw_sum R.N (fun _ _ => R.Ω) R.E R.F
        (fun _ _ => R.Ω_norm) R.E_sum R.F_sum (h, x) (h, y)
    have hzero : (∑ a : A, ∑ b : B,
        (P.idealCorrelation (h, x) (h, y) a b -
         R.answerLaw (h, x) (h, y) a b)) = 0 := by
      rw [sum2_sub, hsumI, hsumR, sub_self]
    have hexpand : (∑ a : A, ∑ b : B, G.payoff x y a b *
          P.idealCorrelation (h, x) (h, y) a b) -
        (∑ a : A, ∑ b : B, G.payoff x y a b *
          R.answerLaw (h, x) (h, y) a b)
        = ∑ a : A, ∑ b : B, (G.payoff x y a b - 1 / 2) *
            (P.idealCorrelation (h, x) (h, y) a b -
             R.answerLaw (h, x) (h, y) a b) := by
      calc (∑ a : A, ∑ b : B, G.payoff x y a b *
            P.idealCorrelation (h, x) (h, y) a b) -
          (∑ a : A, ∑ b : B, G.payoff x y a b *
            R.answerLaw (h, x) (h, y) a b)
          = ∑ a : A, ∑ b : B,
              (G.payoff x y a b * P.idealCorrelation (h, x) (h, y) a b -
               G.payoff x y a b * R.answerLaw (h, x) (h, y) a b) :=
            (sum2_sub _ _).symm
        _ = ∑ a : A, ∑ b : B,
              ((G.payoff x y a b - 1 / 2) *
                (P.idealCorrelation (h, x) (h, y) a b -
                 R.answerLaw (h, x) (h, y) a b) +
               (1 / 2) *
                (P.idealCorrelation (h, x) (h, y) a b -
                 R.answerLaw (h, x) (h, y) a b)) :=
            Finset.sum_congr rfl fun a _ =>
              Finset.sum_congr rfl fun b _ => by ring
        _ = (∑ a : A, ∑ b : B, (G.payoff x y a b - 1 / 2) *
              (P.idealCorrelation (h, x) (h, y) a b -
               R.answerLaw (h, x) (h, y) a b)) +
            (1 / 2) * ∑ a : A, ∑ b : B,
              (P.idealCorrelation (h, x) (h, y) a b -
               R.answerLaw (h, x) (h, y) a b) := by
            rw [sum2_add, sum2_mul_left]
        _ = ∑ a : A, ∑ b : B, (G.payoff x y a b - 1 / 2) *
              (P.idealCorrelation (h, x) (h, y) a b -
               R.answerLaw (h, x) (h, y) a b) := by
            rw [hzero, mul_zero, add_zero]
    have habs : |∑ a : A, ∑ b : B, (G.payoff x y a b - 1 / 2) *
        (P.idealCorrelation (h, x) (h, y) a b -
         R.answerLaw (h, x) (h, y) a b)|
        ≤ (∑ a : A, ∑ b : B,
            |R.answerLaw (h, x) (h, y) a b -
             P.idealCorrelation (h, x) (h, y) a b|) / 2 := by
      calc |∑ a : A, ∑ b : B, (G.payoff x y a b - 1 / 2) *
            (P.idealCorrelation (h, x) (h, y) a b -
             R.answerLaw (h, x) (h, y) a b)|
          ≤ ∑ a : A, ∑ b : B, |(G.payoff x y a b - 1 / 2) *
              (P.idealCorrelation (h, x) (h, y) a b -
               R.answerLaw (h, x) (h, y) a b)| :=
            (Finset.abs_sum_le_sum_abs _ _).trans <|
              Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a : A, ∑ b : B, (1 / 2) *
              |R.answerLaw (h, x) (h, y) a b -
               P.idealCorrelation (h, x) (h, y) a b| := by
            refine Finset.sum_le_sum fun a _ =>
              Finset.sum_le_sum fun b _ => ?_
            rw [abs_mul,
              abs_sub_comm (P.idealCorrelation (h, x) (h, y) a b)
                (R.answerLaw (h, x) (h, y) a b)]
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            rw [abs_le]
            constructor
            · linarith [G.payoff_nonneg x y a b]
            · linarith [G.payoff_le_one x y a b]
        _ = (∑ a : A, ∑ b : B,
              |R.answerLaw (h, x) (h, y) a b -
               P.idealCorrelation (h, x) (h, y) a b|) / 2 := by
            rw [sum2_mul_left]
            ring
    have hlow := (abs_le.mp habs).1
    have hgoal : (∑ a : A, ∑ b : B, G.payoff x y a b *
          P.idealCorrelation (h, x) (h, y) a b) -
        (∑ a : A, ∑ b : B,
          |R.answerLaw (h, x) (h, y) a b -
            P.idealCorrelation (h, x) (h, y) a b|) / 2
        ≤ ∑ a : A, ∑ b : B, G.payoff x y a b *
            R.answerLaw (h, x) (h, y) a b := by
      linarith [hexpand, hlow, (abs_le.mp habs).2]
    exact hgoal
  have hLHS : P.idealSuccess G - P.samplingError R / 2
      = ∑ h : P.Hist, ∑ x : X, ∑ y : Y,
          (P.Q h x y * (∑ a : A, ∑ b : B, G.payoff x y a b *
            P.idealCorrelation (h, x) (h, y) a b) -
           P.Q h x y * (∑ a : A, ∑ b : B,
            |R.answerLaw (h, x) (h, y) a b -
             P.idealCorrelation (h, x) (h, y) a b|) / 2) := by
    unfold PreroundedStrategy.idealSuccess PreroundedStrategy.samplingError
    rw [sum3_div, ← sum3_sub]
  rw [hLHS, hflat]
  refine Finset.sum_le_sum fun h _ => Finset.sum_le_sum fun x _ =>
    Finset.sum_le_sum fun y _ => ?_
  have h1 := hpt h x y
  have h2 := P.Q_nonneg h x y
  have h3 := mul_le_mul_of_nonneg_left h1 h2
  calc P.Q h x y * (∑ a : A, ∑ b : B, G.payoff x y a b *
        P.idealCorrelation (h, x) (h, y) a b) -
      P.Q h x y * (∑ a : A, ∑ b : B,
        |R.answerLaw (h, x) (h, y) a b -
         P.idealCorrelation (h, x) (h, y) a b|) / 2
      = P.Q h x y * ((∑ a : A, ∑ b : B, G.payoff x y a b *
          P.idealCorrelation (h, x) (h, y) a b) -
        (∑ a : A, ∑ b : B,
          |R.answerLaw (h, x) (h, y) a b -
           P.idealCorrelation (h, x) (h, y) a b|) / 2) := by ring
    _ ≤ P.Q h x y * P.tuplePayoff G R (h, x, y) := h3

/-- **The legal one-shot strategy and its payoff** (nodes 1.4, 1.4.1,
1.4.4; 07_main_theorem.tex sec 7.2, eq one-shot-final-payoff): tensoring
the sampling resource with the classical flag — seed `ω ∼ ν`, locally
computed histories `r_A(ω, x)`, `r_B(ω, y)`, labels `s = (r_A, x)`,
`t = (r_B, y)` — yields a legal commuting strategy for `G` (state fixed
before the questions, labels locally computable, Alice left, Bob right,
all cross-commutators vanishing) with winning probability at least
`idealSuccess − samplingError/2 − d_TV(Q, J_A) − Pr[r_A ≠ r_B]`.
On the event `r_A = r_B` the conditional payoff is exactly the tuple
payoff; on the complement it is nonnegative. The argument uses only the
exact `J_A` marginal, one change of measure, and the mismatch
probability. -/
theorem one_shot_strategy
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
    (G : Game X Y A B) (P : PreroundedStrategy X Y A B)
    (R : SamplingResource (P.Hist × X) (P.Hist × Y) A B) :
    ∃ Sc : CommutingStrategy.{0} X Y A B,
      P.idealSuccess G - P.samplingError R / 2 -
          Pinsker.finiteTotalVariation P.Qflat (P.JAflat G) -
          P.mismatchProb G
        ≤ G.win Sc.correlation := by
  classical
  -- The strategy: sample the shared seed, compute the local histories,
  -- and play the sampling resource's effects at the resulting labels.
  refine ⟨CommutingStrategy.seedMixture P.ν P.ν_nonneg P.ν_sum R.Ω R.Ω_norm
    (fun ω x a => R.N.L (R.E (P.rA ω x, x) a))
    (fun ω y b => R.N.Rop (R.F (P.rB ω y, y) b))
    (fun ω x a => R.N.L_isPositive (R.E_pos _ a))
    (fun ω y b => R.N.Rop_isPositive (R.F_pos _ b))
    (fun ω x => by rw [← map_sum, R.E_sum, map_one])
    (fun ω y => by
      simp only [StdTracialAlgebra.Rop]
      rw [← map_sum, ← Finset.op_sum, R.F_sum, MulOpposite.op_one, map_one])
    (fun ω x y a b => R.N.LR_commute _ _), ?_⟩
  -- Its correlation is the ν-mixture of the resource's answer laws at the
  -- locally computed labels.
  have hcorr : ∀ (x : X) (y : Y) (a : A) (b : B),
      (CommutingStrategy.seedMixture P.ν P.ν_nonneg P.ν_sum R.Ω R.Ω_norm
        (fun ω x a => R.N.L (R.E (P.rA ω x, x) a))
        (fun ω y b => R.N.Rop (R.F (P.rB ω y, y) b))
        (fun ω x a => R.N.L_isPositive (R.E_pos _ a))
        (fun ω y b => R.N.Rop_isPositive (R.F_pos _ b))
        (fun ω x => by rw [← map_sum, R.E_sum, map_one])
        (fun ω y => by
          simp only [StdTracialAlgebra.Rop]
          rw [← map_sum, ← Finset.op_sum, R.F_sum, MulOpposite.op_one,
            map_one])
        (fun ω x y a b => R.N.LR_commute _ _)).correlation x y a b
      = ∑ ω : P.Seed, P.ν ω *
          R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b := by
    intro x y a b
    exact CommutingStrategy.seedMixture_correlation _ _ _ _ _ _ _ _ _ _ _ _
      x y a b
  -- Expand the winning probability into the seeded experiment.
  have hwin : G.win (CommutingStrategy.seedMixture P.ν P.ν_nonneg P.ν_sum
      R.Ω R.Ω_norm
      (fun ω x a => R.N.L (R.E (P.rA ω x, x) a))
      (fun ω y b => R.N.Rop (R.F (P.rB ω y, y) b))
      (fun ω x a => R.N.L_isPositive (R.E_pos _ a))
      (fun ω y b => R.N.Rop_isPositive (R.F_pos _ b))
      (fun ω x => by rw [← map_sum, R.E_sum, map_one])
      (fun ω y => by
        simp only [StdTracialAlgebra.Rop]
        rw [← map_sum, ← Finset.op_sum, R.F_sum, MulOpposite.op_one,
          map_one])
      (fun ω x y a b => R.N.LR_commute _ _)).correlation
      = ∑ ω : P.Seed, ∑ x : X, ∑ y : Y,
          P.ν ω * G.questionWeight x y *
            (∑ a : A, ∑ b : B, G.payoff x y a b *
              R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b) := by
    unfold Game.win
    simp only [hcorr]
    calc (∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
          G.questionWeight x y * G.payoff x y a b *
            (∑ ω : P.Seed, P.ν ω *
              R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b))
        = ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B, ∑ ω : P.Seed,
            P.ν ω * G.questionWeight x y * (G.payoff x y a b *
              R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl
            fun y _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ = ∑ ω : P.Seed, ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
            P.ν ω * G.questionWeight x y * (G.payoff x y a b *
              R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b) := by
          calc (∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B, ∑ ω : P.Seed,
                P.ν ω * G.questionWeight x y * (G.payoff x y a b *
                  R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b))
              = ∑ x : X, ∑ y : Y, ∑ a : A, ∑ ω : P.Seed, ∑ b : B,
                  P.ν ω * G.questionWeight x y * (G.payoff x y a b *
                    R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b) :=
                Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl
                  fun y _ => Finset.sum_congr rfl fun a _ =>
                  Finset.sum_comm
            _ = ∑ x : X, ∑ y : Y, ∑ ω : P.Seed, ∑ a : A, ∑ b : B,
                  P.ν ω * G.questionWeight x y * (G.payoff x y a b *
                    R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b) :=
                Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl
                  fun y _ => Finset.sum_comm
            _ = ∑ x : X, ∑ ω : P.Seed, ∑ y : Y, ∑ a : A, ∑ b : B,
                  P.ν ω * G.questionWeight x y * (G.payoff x y a b *
                    R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b) :=
                Finset.sum_congr rfl fun x _ => Finset.sum_comm
            _ = ∑ ω : P.Seed, ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
                  P.ν ω * G.questionWeight x y * (G.payoff x y a b *
                    R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b) :=
                Finset.sum_comm
      _ = ∑ ω : P.Seed, ∑ x : X, ∑ y : Y,
            P.ν ω * G.questionWeight x y *
              (∑ a : A, ∑ b : B, G.payoff x y a b *
                R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b) := by
          refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl
            fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
  rw [hwin]
  -- Per-tuple: the matched-label payoff, minus the mismatch indicator,
  -- lower-bounds the seeded payoff (nonnegative off the match event).
  have hkey : ∀ (ω : P.Seed) (x : X) (y : Y),
      P.tuplePayoff G R (P.rA ω x, x, y) -
          (if P.rA ω x = P.rB ω y then 0 else 1)
        ≤ ∑ a : A, ∑ b : B, G.payoff x y a b *
            R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b := by
    intro ω x y
    by_cases hm : P.rA ω x = P.rB ω y
    · rw [if_pos hm, sub_zero]
      have htp : P.tuplePayoff G R (P.rA ω x, x, y)
          = ∑ a : A, ∑ b : B, G.payoff x y a b *
              R.answerLaw (P.rA ω x, x) (P.rA ω x, y) a b := rfl
      rw [htp, show P.rB ω y = P.rA ω x from hm.symm]
    · rw [if_neg hm]
      have h1 := P.tuplePayoff_le_one G R (P.rA ω x, x, y)
      have h2 : 0 ≤ ∑ a : A, ∑ b : B, G.payoff x y a b *
          R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b :=
        Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
          mul_nonneg (G.payoff_nonneg _ _ _ _)
            (tracialPairLaw_nonneg R.N _ R.E R.F R.E_pos R.F_pos _ _ _ _)
      linarith
  -- Average the key inequality over the seeded experiment.
  have hsum1 : (∑ ω : P.Seed, ∑ x : X, ∑ y : Y,
        P.ν ω * G.questionWeight x y *
          P.tuplePayoff G R (P.rA ω x, x, y)) - P.mismatchProb G
      ≤ ∑ ω : P.Seed, ∑ x : X, ∑ y : Y,
          P.ν ω * G.questionWeight x y *
            (∑ a : A, ∑ b : B, G.payoff x y a b *
              R.answerLaw (P.rA ω x, x) (P.rB ω y, y) a b) := by
    unfold PreroundedStrategy.mismatchProb
    rw [← sum3_sub]
    refine Finset.sum_le_sum fun ω _ => Finset.sum_le_sum fun x _ =>
      Finset.sum_le_sum fun y _ => ?_
    have hνμ : 0 ≤ P.ν ω * G.questionWeight x y :=
      mul_nonneg (P.ν_nonneg ω) (G.weight_nonneg x y)
    have hstep := mul_le_mul_of_nonneg_left (hkey ω x y) hνμ
    calc P.ν ω * G.questionWeight x y *
          P.tuplePayoff G R (P.rA ω x, x, y) -
        P.ν ω * G.questionWeight x y *
          (if P.rA ω x = P.rB ω y then 0 else 1)
        = P.ν ω * G.questionWeight x y *
            (P.tuplePayoff G R (P.rA ω x, x, y) -
              (if P.rA ω x = P.rB ω y then 0 else 1)) := by ring
      _ ≤ _ := hstep
  -- The matched-label average is the J_A expectation of the tuple payoff.
  have hJA : (∑ ω : P.Seed, ∑ x : X, ∑ y : Y,
      P.ν ω * G.questionWeight x y *
        P.tuplePayoff G R (P.rA ω x, x, y))
      = ∑ t : P.Hist × X × Y, P.JAflat G t * P.tuplePayoff G R t :=
    (P.sum_JAflat_mul G (P.tuplePayoff G R)).symm
  -- Change of measure J_A → Q, then the ideal-law payoff bound.
  have hCM := abs_expectation_sub_le_totalVariation
    (p := P.Qflat) (q := P.JAflat G) (F := P.tuplePayoff G R)
    P.Qflat_nonneg P.Qflat_sum (P.JAflat_nonneg G) (P.JAflat_sum G)
    (P.tuplePayoff_nonneg G R) (P.tuplePayoff_le_one G R)
  have h5 := (abs_le.mp hCM).2
  have hQF := P.payoff_under_ideal G R
  rw [hJA] at hsum1
  linarith [hsum1, h5, hQF]

end CommutingRepetition
