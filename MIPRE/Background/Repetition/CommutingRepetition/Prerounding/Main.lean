/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/Main.lean
-/
/-
# Tracial pre-rounding (Section 5, root)

Statement skeleton for audit node 1.2. Anchors: 05_prerounding.tex, prop
tracial-prerounding (eqs prerounding-hypothesis, prerounding-ideal-success,
prerounding-delta, prerounding-kl, prerounding-tv, prerounding-mismatch),
and the label structure of 07_main_theorem.tex sec 7.2
(`s = (i, r_A, x)`, `t = (i, r_B, y)`).

Encoding notes (recorded in DIFFERENCES.md):
- the proposition's abstract label sets `S, T` with question maps
  `x : S → X`, `y : T → Y` are instantiated as `S = Hist × X`,
  `T = Hist × Y` with coordinate projections — the shape the manuscript's
  proof constructs (labels `(i, r, x)`, the tuple `(i, r)` bundled as
  `Hist`) and the one-shot assembly of sec 7.2 consumes;
- the locally generated tuple laws `J_A, J_B` are DEFINED as the exact
  pushforwards of the seeded samplers (the manuscript's "the histories
  output by the two local samplers have the exact marginals J_A, J_B"),
  so exactness of marginals is definitional;
- the KL conclusions carry explicit absolute-continuity conjuncts, which
  the manuscript's finite `D(Q‖J) ≤ 3η < ∞` implies;
- `d_TV` is the halved total variation (`Pinsker.finiteTotalVariation`),
  matching the manuscript's Pinsker form `κ = √(3η/2)`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Game.Basic
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Strategy
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.Main
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Entropy
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.History
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Success
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.PackageAlignment
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Sampler

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The output package of tracial pre-rounding (05_prerounding.tex, prop
tracial-prerounding): a finite standard-form algebra `N`; a finite shared
history alphabet `Hist` (the manuscript's tuples `(i, r)`); the ideal
posterior tuple law `Q` on `Hist × X × Y`; unit vectors `u_{st}` (indexed
by the full label rectangle `(Hist × X) × (Hist × Y)`), `x_s`, `y_t`; full
POVMs `(A_s^a)`, `(B_t^b)` in `N`, Alice's used on the left and Bob's on
the right; and one finite shared classical seed with its two local history
samplers. -/
structure PreroundedStrategy (X Y A B : Type)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] : Type 1 where
  N : StdTracialAlgebra.{0}
  Hist : Type
  [histFintype : Fintype Hist]
  [histDecEq : DecidableEq Hist]
  Q : Hist → X → Y → ℝ
  Q_nonneg : ∀ h x y, 0 ≤ Q h x y
  Q_sum : (∑ h : Hist, ∑ x : X, ∑ y : Y, Q h x y) = 1
  u : Hist × X → Hist × Y → N.H
  xvec : Hist × X → N.H
  yvec : Hist × Y → N.H
  u_norm : ∀ s t, ‖u s t‖ = 1
  xvec_norm : ∀ s, ‖xvec s‖ = 1
  yvec_norm : ∀ t, ‖yvec t‖ = 1
  A_ : Hist × X → A → N.A
  B_ : Hist × Y → B → N.A
  A_pos : ∀ s a, IsPosElem (A_ s a)
  B_pos : ∀ t b, IsPosElem (B_ t b)
  A_sum : ∀ s, (∑ a : A, A_ s a) = 1
  B_sum : ∀ t, (∑ b : B, B_ t b) = 1
  Seed : Type
  [seedFintype : Fintype Seed]
  ν : Seed → ℝ
  ν_nonneg : ∀ ω, 0 ≤ ν ω
  ν_sum : (∑ ω : Seed, ν ω) = 1
  rA : Seed → X → Hist
  rB : Seed → Y → Hist

namespace PreroundedStrategy

attribute [instance] histFintype histDecEq seedFintype

variable (P : PreroundedStrategy X Y A B)

/-- The ideal pair answer law `q_{st}(a,b) = ⟪u_{st}, L(A_s^a) R(B_t^b)
u_{st}⟫`, defined on the full label rectangle. -/
noncomputable def idealCorrelation :
    P.Hist × X → P.Hist × Y → A → B → ℝ :=
  tracialPairLaw P.N P.u P.A_ P.B_

/-- The label law `π` on `S × T`: the pushforward of the ideal posterior
tuple law under `(h, x, y) ↦ ((h, x), (h, y))` — supported on matching
histories. [05_prerounding.tex, label-law-pi] -/
def labelLaw (s : P.Hist × X) (t : P.Hist × Y) : ℝ :=
  if s.1 = t.1 then P.Q s.1 s.2 t.2 else 0

/-- The `π`-averaged ideal success
`E_π ∑_{a,b} V(a,b | x(s), y(t)) ⟪u_{st}, L(A_s^a) R(B_t^b) u_{st}⟫`.
[05_prerounding.tex, eq prerounding-ideal-success] -/
noncomputable def idealSuccess (G : Game X Y A B) : ℝ :=
  ∑ h : P.Hist, ∑ x : X, ∑ y : Y, P.Q h x y *
    ∑ a : A, ∑ b : B, G.payoff x y a b *
      P.idealCorrelation (h, x) (h, y) a b

/-- The alignment defect
`Δ = E_π(‖u_{st} − x_s‖² + ‖u_{st} − y_t‖²)`.
[05_prerounding.tex, eq prerounding-delta] -/
noncomputable def alignment : ℝ :=
  ∑ h : P.Hist, ∑ x : X, ∑ y : Y, P.Q h x y *
    (‖P.u (h, x) (h, y) - P.xvec (h, x)‖ ^ 2 +
      ‖P.u (h, x) (h, y) - P.yvec (h, y)‖ ^ 2)

/-- The locally generated Alice tuple law `J_A`: the exact law of
`(r_A(ω, x), x, y)` when `ω ∼ ν` and `(x, y) ∼ μ`.
[05_prerounding.tex, eq prerounding-tv context; 07_main_theorem.tex, "The
exact Alice tuple marginal in the actual classical experiment is J_A"] -/
def JA (G : Game X Y A B) (h : P.Hist) (x : X) (y : Y) : ℝ :=
  (∑ ω : P.Seed, P.ν ω * if P.rA ω x = h then 1 else 0) *
    G.questionWeight x y

/-- The locally generated Bob tuple law `J_B`: the exact law of
`(r_B(ω, y), x, y)`. -/
def JB (G : Game X Y A B) (h : P.Hist) (x : X) (y : Y) : ℝ :=
  (∑ ω : P.Seed, P.ν ω * if P.rB ω y = h then 1 else 0) *
    G.questionWeight x y

/-- The history mismatch probability
`Pr[r_A ≠ r_B]` under `ω ∼ ν`, `(x, y) ∼ μ`.
[05_prerounding.tex, eq prerounding-mismatch] -/
def mismatchProb (G : Game X Y A B) : ℝ :=
  ∑ ω : P.Seed, ∑ x : X, ∑ y : Y,
    P.ν ω * G.questionWeight x y *
      if P.rA ω x = P.rB ω y then 0 else 1

/-- The tuple law `Q` flattened to the tuple type, for divergence and
total-variation statements. -/
def Qflat (t : P.Hist × X × Y) : ℝ := P.Q t.1 t.2.1 t.2.2

/-- `J_A` flattened to the tuple type. -/
def JAflat (G : Game X Y A B) (t : P.Hist × X × Y) : ℝ :=
  P.JA G t.1 t.2.1 t.2.2

/-- `J_B` flattened to the tuple type. -/
def JBflat (G : Game X Y A B) (t : P.Hist × X × Y) : ℝ :=
  P.JB G t.1 t.2.1 t.2.2

/-- Master conversion: a `π`-average over the label rectangle collapses to
a `Q`-average over tuples, since `labelLaw` is supported on matching
histories. -/
theorem sum_labelLaw_mul (f : P.Hist × X → P.Hist × Y → ℝ) :
    (∑ s : P.Hist × X, ∑ t : P.Hist × Y, P.labelLaw s t * f s t)
      = ∑ h : P.Hist, ∑ x : X, ∑ y : Y, P.Q h x y * f (h, x) (h, y) := by
  classical
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [labelLaw, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem labelLaw_nonneg (s : P.Hist × X) (t : P.Hist × Y) :
    0 ≤ P.labelLaw s t := by
  unfold labelLaw
  split
  · exact P.Q_nonneg _ _ _
  · exact le_refl 0

/-- The label law is a probability law on the rectangle. -/
theorem labelLaw_sum :
    (∑ s : P.Hist × X, ∑ t : P.Hist × Y, P.labelLaw s t) = 1 := by
  have h := P.sum_labelLaw_mul fun _ _ => 1
  simpa using h.trans (by simpa using P.Q_sum)

theorem alignment_nonneg : 0 ≤ P.alignment :=
  Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => mul_nonneg (P.Q_nonneg h x y)
      (add_nonneg (pow_nonneg (norm_nonneg _) 2)
        (pow_nonneg (norm_nonneg _) 2))

/-- The abstract `π`-alignment of the package's data is its alignment. -/
theorem piAlignment_labelLaw :
    piAlignment P.labelLaw P.u P.xvec P.yvec = P.alignment := by
  simp only [piAlignment, alignment]
  exact P.sum_labelLaw_mul fun s t =>
    ‖P.u s t - P.xvec s‖ ^ 2 + ‖P.u s t - P.yvec t‖ ^ 2

theorem Qflat_nonneg (t : P.Hist × X × Y) : 0 ≤ P.Qflat t :=
  P.Q_nonneg _ _ _

theorem Qflat_sum : (∑ t : P.Hist × X × Y, P.Qflat t) = 1 := by
  rw [show (∑ t : P.Hist × X × Y, P.Qflat t)
      = ∑ h : P.Hist, ∑ x : X, ∑ y : Y, P.Q h x y from by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun h _ => by
      rw [Fintype.sum_prod_type]
      rfl]
  exact P.Q_sum

/-- Pushforward identity for the locally generated Alice law: a
`J_A`-average over tuples is the seeded-experiment average
(`ω ∼ ν`, `(x,y) ∼ μ`, tuple `(r_A(ω,x), x, y)`). -/
theorem sum_JAflat_mul (G : Game X Y A B) (f : P.Hist × X × Y → ℝ) :
    (∑ t : P.Hist × X × Y, P.JAflat G t * f t)
      = ∑ ω : P.Seed, ∑ x : X, ∑ y : Y,
          P.ν ω * G.questionWeight x y * f (P.rA ω x, x, y) := by
  classical
  have hflat : (∑ t : P.Hist × X × Y, P.JAflat G t * f t)
      = ∑ h : P.Hist, ∑ x : X, ∑ y : Y,
          P.JA G h x y * f (h, x, y) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun h _ => by
      rw [Fintype.sum_prod_type]
      rfl
  have hexp : ∀ (h : P.Hist) (x : X) (y : Y),
      P.JA G h x y * f (h, x, y)
        = ∑ ω : P.Seed, (if P.rA ω x = h then
            P.ν ω * (G.questionWeight x y * f (h, x, y)) else 0) := by
    intro h x y
    simp only [PreroundedStrategy.JA]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split
    · ring
    · ring
  have hswap : (∑ h : P.Hist, ∑ x : X, ∑ y : Y, ∑ ω : P.Seed,
        (if P.rA ω x = h then
          P.ν ω * (G.questionWeight x y * f (h, x, y)) else 0))
      = ∑ ω : P.Seed, ∑ x : X, ∑ y : Y, ∑ h : P.Hist,
        (if P.rA ω x = h then
          P.ν ω * (G.questionWeight x y * f (h, x, y)) else 0) := by
    calc (∑ h : P.Hist, ∑ x : X, ∑ y : Y, ∑ ω : P.Seed,
          (if P.rA ω x = h then
            P.ν ω * (G.questionWeight x y * f (h, x, y)) else 0))
        = ∑ h : P.Hist, ∑ x : X, ∑ ω : P.Seed, ∑ y : Y,
            (if P.rA ω x = h then
              P.ν ω * (G.questionWeight x y * f (h, x, y)) else 0) :=
          Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun x _ =>
            Finset.sum_comm
      _ = ∑ h : P.Hist, ∑ ω : P.Seed, ∑ x : X, ∑ y : Y,
            (if P.rA ω x = h then
              P.ν ω * (G.questionWeight x y * f (h, x, y)) else 0) :=
          Finset.sum_congr rfl fun h _ => Finset.sum_comm
      _ = ∑ ω : P.Seed, ∑ h : P.Hist, ∑ x : X, ∑ y : Y,
            (if P.rA ω x = h then
              P.ν ω * (G.questionWeight x y * f (h, x, y)) else 0) :=
          Finset.sum_comm
      _ = ∑ ω : P.Seed, ∑ x : X, ∑ h : P.Hist, ∑ y : Y,
            (if P.rA ω x = h then
              P.ν ω * (G.questionWeight x y * f (h, x, y)) else 0) :=
          Finset.sum_congr rfl fun ω _ => Finset.sum_comm
      _ = ∑ ω : P.Seed, ∑ x : X, ∑ y : Y, ∑ h : P.Hist,
            (if P.rA ω x = h then
              P.ν ω * (G.questionWeight x y * f (h, x, y)) else 0) :=
          Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun x _ =>
            Finset.sum_comm
  have hcollapse : ∀ (ω : P.Seed) (x : X) (y : Y),
      (∑ h : P.Hist, (if P.rA ω x = h then
          P.ν ω * (G.questionWeight x y * f (h, x, y)) else 0))
        = P.ν ω * G.questionWeight x y * f (P.rA ω x, x, y) := by
    intro ω x y
    rw [Finset.sum_ite_eq]
    simp [mul_assoc]
  calc (∑ t : P.Hist × X × Y, P.JAflat G t * f t)
      = ∑ h : P.Hist, ∑ x : X, ∑ y : Y, P.JA G h x y * f (h, x, y) :=
        hflat
    _ = ∑ h : P.Hist, ∑ x : X, ∑ y : Y, ∑ ω : P.Seed,
          (if P.rA ω x = h then
            P.ν ω * (G.questionWeight x y * f (h, x, y)) else 0) :=
        Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => hexp h x y
    _ = ∑ ω : P.Seed, ∑ x : X, ∑ y : Y, ∑ h : P.Hist,
          (if P.rA ω x = h then
            P.ν ω * (G.questionWeight x y * f (h, x, y)) else 0) := hswap
    _ = ∑ ω : P.Seed, ∑ x : X, ∑ y : Y,
          P.ν ω * G.questionWeight x y * f (P.rA ω x, x, y) :=
        Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => hcollapse ω x y

theorem JAflat_nonneg (G : Game X Y A B) (t : P.Hist × X × Y) :
    0 ≤ P.JAflat G t := by
  refine mul_nonneg (Finset.sum_nonneg fun ω _ => ?_) (G.weight_nonneg _ _)
  split
  · simpa using P.ν_nonneg ω
  · simp

theorem JAflat_sum (G : Game X Y A B) :
    (∑ t : P.Hist × X × Y, P.JAflat G t) = 1 := by
  have h := P.sum_JAflat_mul G (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  calc (∑ ω : P.Seed, ∑ x : X, ∑ y : Y,
        P.ν ω * G.questionWeight x y)
      = ∑ ω : P.Seed, P.ν ω * ∑ x : X, ∑ y : Y,
          G.questionWeight x y := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ ω : P.Seed, P.ν ω := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [G.weight_normalized, mul_one]
    _ = 1 := P.ν_sum

end PreroundedStrategy

/-- **Weighted tracial pre-rounding** (nodes 1.2 + 1.6.2;
05_prerounding.tex, prop tracial-prerounding, run as modified by
07_main_theorem.tex sec 7.4 for rational payoff tables): the referee
declares acceptance per coordinate with a fresh finite private coin of
bias `V(aᵢ, bᵢ | xᵢ, yᵢ)` — possible exactly because the payoffs are
rational — and the coins are never revealed, so no effect, sampler, or
label depends on them. The Section 5 machinery runs with the core
indicator replaced by the weight `w_D ∈ [0,1]` (eq
private-coin-core-weight), the accepted-word budget by the weighted
entropy inequality `w·H₁(a) ≤ H₁(w·a)` plus log-sum (eq
weighted-accepted-word-entropy), and the history budget by data
processing from the private-coin space; the manuscript notes every
constant is unchanged, so the conclusion is form-identical to the
predicate case, of which this statement is the generalization (the
predicate case is the specialization to `{0,1}`-valued — hence rational —
payoffs). Conclusion shape as in `tracial_prerounding` below. -/
theorem weighted_tracial_prerounding
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
    (G : Game X Y A B)
    (hQ : ∀ x y a b, ∃ r : ℚ, G.payoff x y a b = (r : ℝ))
    (n : ℕ) (hn : 1 ≤ n)
    (Trep : TracialStrategy.{0}
      (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
    {ε γ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hγ : γ ≤ ε / 8)
    (hθ : Real.exp (-(γ * n)) < (G.«repeat» n).win Trep.correlation) :
    ∃ (P : PreroundedStrategy X Y A B) (η : ℝ), 0 ≤ η ∧
      η ≤ 8 * γ * ((ε + Real.log ((Fintype.card A : ℝ) *
        (Fintype.card B : ℝ))) / ε) ∧
      1 - ε / 4 ≤ P.idealSuccess G ∧
      P.alignment ≤ 16 * η ∧
      (∀ t, P.JAflat G t = 0 → P.Qflat t = 0) ∧
      (∀ t, P.JBflat G t = 0 → P.Qflat t = 0) ∧
      Pinsker.finiteRelativeEntropy P.Qflat (P.JAflat G) ≤ 3 * η ∧
      Pinsker.finiteRelativeEntropy P.Qflat (P.JBflat G) ≤ 3 * η ∧
      Pinsker.finiteTotalVariation P.Qflat (P.JAflat G)
        ≤ Real.sqrt (3 * η / 2) ∧
      Pinsker.finiteTotalVariation P.Qflat (P.JBflat G)
        ≤ Real.sqrt (3 * η / 2) ∧
      P.mismatchProb G ≤ 4 * Real.sqrt (3 * η / 2) := by
  -- Proof layer: Prerounding/{CoinLaw, Family, Package, IdealSuccess, Success,
  -- PackageAlignment, Sampler}.lean. Fixed decidable equalities on the question
  -- and answer alphabets (the Section 5 layer is generic in them).
  let _instX : DecidableEq X := Classical.decEq X
  let _instY : DecidableEq Y := Classical.decEq Y
  let _instA : DecidableEq A := Classical.decEq A
  let _instB : DecidableEq B := Classical.decEq B
  set μ := G.questionWeight with hμdef
  have hμ : ∀ x y, 0 ≤ μ x y := G.weight_nonneg
  have hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1 := G.weight_normalized
  set ℓ : ℝ := Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) with hℓdef
  have hℓ : 0 ≤ ℓ := by
    apply Real.log_nonneg
    have hA : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
    have hB : (1 : ℝ) ≤ Fintype.card B := by exact_mod_cast Fintype.card_pos
    nlinarith
  -- Step 1: rational payoffs have a common denominator (07 sec 7.4).
  obtain ⟨den, num, hden, hV, hnum⟩ := G.exists_common_denominator hQ
  -- Step 2: the greedy core of the private-coin law (node 1.2.1).
  set law := coinLaw G Trep den hden with hlaw
  set wins : Fin n → CoinSpace n den X Y A B → Bool := coinWins den num with hwins
  have hθwin : law.eventMass (FiniteEventLaw.winEvent wins Finset.univ)
      = (G.«repeat» n).win Trep.correlation :=
    coinLaw_eventMass_univ G Trep den hden num hnum hV
  set θ := law.eventMass (FiniteEventLaw.winEvent wins Finset.univ) with hθdef
  have hθ' : Real.exp (-(γ * n)) < θ := by rw [hθwin]; exact hθ
  have hθpos : 0 < θ := (Real.exp_pos _).trans hθ'
  have hθ1 : θ ≤ 1 := (law.eventMass_mono (Finset.subset_univ _)).trans law.eventMass_univ.le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hγn : Real.log (1 / θ) < γ * n := by
    rw [one_div, Real.log_inv, neg_lt]
    exact (Real.lt_log_iff_exp_lt hθpos).mpr hθ'
  have hδ0 : 0 < ε / 4 := by positivity
  have hδ1 : ε / 4 < 1 := by linarith
  have hlogn : Real.log (1 / θ) / (ε / 4) < (Fintype.card (Fin n) : ℝ) := by
    rw [Fintype.card_fin, div_lt_iff₀ hδ0]
    calc Real.log (1 / θ) < γ * n := hγn
      _ ≤ ε / 8 * n := by gcongr
      _ ≤ n * (ε / 4) := by nlinarith
  obtain ⟨D, hDsub, hDcard, hθD, hgreedy⟩ := greedy_core law wins hδ0 hδ1 hθpos hlogn
  rw [Fintype.card_fin] at hgreedy
  -- Step 3: the core parameters (node 1.2.2).
  set p := law.eventMass (FiniteEventLaw.winEvent wins D) with hpdef
  have hppos : 0 < p := hθpos.trans_le hθD
  have hp1 : p ≤ 1 := (law.eventMass_mono (Finset.subset_univ _)).trans law.eventMass_univ.le
  have hm : D.card < n := by
    have := Finset.card_lt_card hDsub
    simpa [Finset.card_univ, Fintype.card_fin] using this
  obtain ⟨-, -, -, -, hη1, hη2⟩ := core_parameters hε0 hε1 hγ hℓ hn hθ' hθD hp1 hDcard
  set η : ℝ := 2 * γ * (1 + 4 * ℓ / ε) with hηdef
  set m : ℝ := (n : ℝ) - D.card with hmdef
  have hm0 : 0 < m := by
    rw [hmdef, ← Nat.cast_sub hm.le]
    exact_mod_cast Nat.sub_pos_of_lt hm
  -- One fixed decidable equality on histories (all history indicators use it).
  let hdecH : DecidableEq (TracialStrategy.PostTuple n X Y A B D) := Classical.decEq _
  have hmcast : ((n - D.card : ℕ) : ℝ) = m := by rw [hmdef, Nat.cast_sub hm.le]
  have ht0 : 0 ≤ Real.log p⁻¹ := by
    rw [Real.log_inv]
    linarith [Real.log_nonpos hppos.le hp1]
  have hs0 : 0 ≤ (D.card : ℝ) * ℓ := mul_nonneg (Nat.cast_nonneg _) hℓ
  rw [one_div] at hη1
  have hηpos : 0 < η := lt_of_le_of_lt (div_nonneg (add_nonneg ht0 hs0) hm0.le) hη1
  -- The relative-entropy bound `T = (3t₀ + 2s₀)/m < 3η` and the rounding slack.
  set T : ℝ := (3 * Real.log p⁻¹ + 2 * ((D.card : ℝ) * ℓ)) / m with hTdef
  have hT : T < 3 * η := by
    calc T ≤ 3 * ((Real.log p⁻¹ + D.card * ℓ) / m) := by
          rw [hTdef, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right (by linarith) hm0.le
      _ < 3 * η := by linarith
  set slack : ℝ := 3 * η - T with hslack
  have hslack0 : 0 < slack := by rw [hslack]; linarith
  set ρ : ℝ := 1 - Real.exp (-slack) with hρdef
  have hexp1 : Real.exp (-slack) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith [Real.exp_pos (-slack)]
  have hlogρ : Real.log (1 / (1 - ρ)) = slack := by
    have h1 : 1 - ρ = Real.exp (-slack) := by rw [hρdef]; ring
    rw [h1, one_div, Real.log_inv, Real.log_exp, neg_neg]
  -- Step 4: the entropic arena over the fully refined family (nodes 1.2.5-6).
  obtain ⟨R, hcol, hrow⟩ := Trep.exists_refined_arena D μ hμ
  have htotF := Trep.sum_refinedA D μ
  have htotG := Trep.sum_refinedB D μ
  -- Step 5: the private-coin core weight (eq private-coin-core-weight).
  set w := coreW G D with hwdef
  have hw0 := coreW_nonneg G D
  have hw1 := coreW_le_one G D
  have hwD := coreW_agree G D
  have hp : p = Trep.coreMass D μ w := (Trep.coreMass_eq_eventMass G hden hnum hV D).symm
  -- Step 6: the live coordinates and the base histories.
  have hcardι : (Fintype.card {i : Fin n // i ∉ D} : ℝ) = m := by
    rw [hmdef, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, Nat.cast_sub hm.le]
  have hι : Nonempty {i : Fin n // i ∉ D} := by
    obtain ⟨i, -, hi⟩ := Finset.exists_of_ssubset hDsub
    exact ⟨⟨i, hi⟩⟩
  have hbase : ∀ i : {i : Fin n // i ∉ D}, ∃ d : RevealDatum n D, d.i = i.1 := by
    intro i
    have hsum := RevealDatum.revealLaw_sum_fiber (D := D) i.1 i.2
    have hne : (∑ d : RevealDatum n D, if d.i = i.1 then d.revealLaw else 0) ≠ 0 := by
      rw [hsum, hmcast]
      exact one_div_ne_zero hm0.ne'
    obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact ⟨d, by by_contra h; exact hd (if_neg h)⟩
  choose d₀ hd₀ using hbase
  set h₀ : {i : Fin n // i ∉ D} → TracialStrategy.PostTuple n X Y A B D := fun i =>
    (d₀ i, fun _ => Classical.arbitrary X, fun _ => Classical.arbitrary Y,
      (fun _ => Classical.arbitrary A, fun _ => Classical.arbitrary B)) with hh₀
  set lc : TracialStrategy.PostTuple n X Y A B D → {i : Fin n // i ∉ D} := fun h => ⟨h.1.i, h.1.i_notMem⟩
    with hlc
  have hlc₀ : ∀ i, lc (h₀ i) = i := fun i => Subtype.ext (hd₀ i)
  -- Step 7: the conditional history laws and their rounded numerators.
  set qA : {i : Fin n // i ∉ D} → X → TracialStrategy.PostTuple n X Y A B D → ℝ :=
    fun i x h => Trep.condQA R D μ w p i.1 x h with hqA
  set qB : {i : Fin n // i ∉ D} → Y → TracialStrategy.PostTuple n X Y A B D → ℝ :=
    fun i y h => Trep.condQB R D μ w p i.1 y h with hqB
  have hqA0 : ∀ i x h, 0 ≤ qA i x h := by
    intro i x h
    simp only [hqA, Trep.condQA_eq]
    split_ifs
    · exact div_nonneg (Trep.histX_nonneg R μ hμ w hw0 hppos h x)
        (Trep.liveX_nonneg R μ hμ w hw0 hppos i.1 x)
    · exact le_rfl
  have hqB0 : ∀ i y h, 0 ≤ qB i y h := by
    intro i y h
    simp only [hqB, Trep.condQB_eq]
    split_ifs
    · exact div_nonneg (Trep.histY_nonneg R μ hμ w hw0 hppos h y)
        (Trep.liveY_nonneg R μ hμ w hw0 hppos i.1 y)
    · exact le_rfl
  have hqA1 : ∀ i x, (∑ h, qA i x h) ≤ 1 := by
    intro i x
    simp only [hqA, Trep.condQA_eq]
    have : (∑ h : TracialStrategy.PostTuple n X Y A B D, if h.1.i = i.1 then
        Trep.histX R D μ w p h x / Trep.liveX R D μ w p i.1 x else 0)
        = (∑ h : TracialStrategy.PostTuple n X Y A B D, if h.1.i = i.1 then Trep.histX R D μ w p h x else 0) /
            Trep.liveX R D μ w p i.1 x := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun h _ => by rw [ite_div, zero_div]
    rw [this]
    exact div_self_le_one _
  have hqB1 : ∀ i y, (∑ h, qB i y h) ≤ 1 := by
    intro i y
    simp only [hqB, Trep.condQB_eq]
    have : (∑ h : TracialStrategy.PostTuple n X Y A B D, if h.1.i = i.1 then
        Trep.histY R D μ w p h y / Trep.liveY R D μ w p i.1 y else 0)
        = (∑ h : TracialStrategy.PostTuple n X Y A B D, if h.1.i = i.1 then Trep.histY R D μ w p h y else 0) /
            Trep.liveY R D μ w p i.1 y := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun h _ => by rw [ite_div, zero_div]
    rw [this]
    exact div_self_le_one _
  have hqAsupp : ∀ i x h, h.1.i ≠ i.1 → qA i x h = 0 := by
    intro i x h hne
    simp only [hqA, Trep.condQA_eq, if_neg hne]
  have hqBsupp : ∀ i y h, h.1.i ≠ i.1 → qB i y h = 0 := by
    intro i y h hne
    simp only [hqB, Trep.condQB_eq, if_neg hne]
  set dens : ℕ := ⌈(Fintype.card (TracialStrategy.PostTuple n X Y A B D) : ℝ) / ρ⌉₊ + 1 with hdens_def
  have hdens : 0 < dens := Nat.succ_pos _
  have hdensR : (0 : ℝ) < dens := by exact_mod_cast hdens
  have hcardH : (Fintype.card (TracialStrategy.PostTuple n X Y A B D) : ℝ) ≤ dens * ρ := by
    have h1 := Nat.le_ceil ((Fintype.card (TracialStrategy.PostTuple n X Y A B D) : ℝ) / ρ)
    rw [div_le_iff₀ hρ0] at h1
    rw [hdens_def]
    push_cast
    rw [add_mul, one_mul]
    linarith
  set numA : {i : Fin n // i ∉ D} → X → TracialStrategy.PostTuple n X Y A B D → ℕ :=
    fun i x => RoundedSampler.roundedNum dens ρ (qA i x) (h₀ i) with hnumA
  set numB : {i : Fin n // i ∉ D} → Y → TracialStrategy.PostTuple n X Y A B D → ℕ :=
    fun i y => RoundedSampler.roundedNum dens ρ (qB i y) (h₀ i) with hnumB
  have hsumA : ∀ i x, (∑ h, numA i x h) = dens := fun i x =>
    RoundedSampler.sum_roundedNum dens hρ1.le (qA i x) (hqA0 i x) (hqA1 i x) hcardH (h₀ i)
  have hsumB : ∀ i y, (∑ h, numB i y h) = dens := fun i y =>
    RoundedSampler.sum_roundedNum dens hρ1.le (qB i y) (hqB0 i y) (hqB1 i y) hcardH (h₀ i)
  have hsA : ∀ i x h, lc h ≠ i → numA i x h = 0 := by
    intro i x h hne
    apply RoundedSampler.roundedNum_eq_zero
    · exact hqAsupp i x h fun heq => hne (Subtype.ext heq)
    · intro heq
      exact hne (by rw [heq]; exact hlc₀ i)
  have hsB : ∀ i y h, lc h ≠ i → numB i y h = 0 := by
    intro i y h hne
    apply RoundedSampler.roundedNum_eq_zero
    · exact hqBsupp i y h fun heq => hne (Subtype.ext heq)
    · intro heq
      exact hne (by rw [heq]; exact hlc₀ i)
  -- Step 8: the package.
  let P : PreroundedStrategy X Y A B :=
    { N := R.N
      Hist := TracialStrategy.PostTuple n X Y A B D
      Q := fun h x y => Trep.flatQ R D μ w p (h, x, y)
      Q_nonneg := fun h x y => Trep.flatQ_nonneg μ hμ R w hw0 hppos (h, x, y)
      Q_sum := by
        have := Trep.sum_flatQ μ hμ R htotF htotG w hwD hp hppos hm
        simpa only [Fintype.sum_prod_type] using this
      u := Trep.uVec μ R
      xvec := Trep.xVec μ R
      yvec := Trep.yVec μ R
      u_norm := fun _ _ => R.N.unitOr_norm _
      xvec_norm := fun _ => R.N.unitOr_norm _
      yvec_norm := fun _ => R.N.unitOr_norm _
      A_ := Trep.Apov μ R
      B_ := Trep.Bpov μ R
      A_pos := Trep.Apov_pos μ R
      B_pos := Trep.Bpov_pos μ R
      A_sum := Trep.Apov_sum μ R
      B_sum := Trep.Bpov_sum μ R
      Seed := RoundedSampler.Seed (TracialStrategy.PostTuple n X Y A B D) {i : Fin n // i ∉ D} dens
      ν := RoundedSampler.ν dens
      ν_nonneg := RoundedSampler.ν_nonneg dens
      ν_sum := RoundedSampler.ν_sum dens
      rA := fun ω x => RoundedSampler.output dens hdens (fun i => numA i x) (fun i => hsumA i x) ω
      rB := fun ω y =>
        RoundedSampler.output dens hdens (fun i => numB i y) (fun i => hsumB i y) ω }
  -- Step 9: the sampler tuple laws in closed form.
  set JA' : TracialStrategy.PostTuple n X Y A B D × X × Y → ℝ := fun u =>
    (∑ ω : RoundedSampler.Seed (TracialStrategy.PostTuple n X Y A B D) {i : Fin n // i ∉ D} dens,
      RoundedSampler.ν dens ω *
        (if RoundedSampler.output dens hdens (fun i => numA i u.2.1) (fun i => hsumA i u.2.1) ω
          = u.1 then (1 : ℝ) else 0)) * μ u.2.1 u.2.2 with hJA'
  set JB' : TracialStrategy.PostTuple n X Y A B D × X × Y → ℝ := fun u =>
    (∑ ω : RoundedSampler.Seed (TracialStrategy.PostTuple n X Y A B D) {i : Fin n // i ∉ D} dens,
      RoundedSampler.ν dens ω *
        (if RoundedSampler.output dens hdens (fun i => numB i u.2.2) (fun i => hsumB i u.2.2) ω
          = u.1 then (1 : ℝ) else 0)) * μ u.2.1 u.2.2 with hJB'
  have hJA'eq : ∀ u, JA' u = m⁻¹ * μ u.2.1 u.2.2 * ((numA (lc u.1) u.2.1 u.1 : ℝ) / dens) := by
    intro u
    simp only [hJA']
    rw [RoundedSampler.sum_ν_output dens hdens (fun i => numA i u.2.1) (fun i => hsumA i u.2.1)
      u.1, RoundedSampler.sum_num_eq dens (fun i => numA i u.2.1) lc
      (fun i h hne => hsA i u.2.1 h hne) u.1, hcardι]
    ring
  have hJB'eq : ∀ u, JB' u = m⁻¹ * μ u.2.1 u.2.2 * ((numB (lc u.1) u.2.2 u.1 : ℝ) / dens) := by
    intro u
    simp only [hJB']
    rw [RoundedSampler.sum_ν_output dens hdens (fun i => numB i u.2.2) (fun i => hsumB i u.2.2)
      u.1, RoundedSampler.sum_num_eq dens (fun i => numB i u.2.2) lc
      (fun i h hne => hsB i u.2.2 h hne) u.1, hcardι]
    ring
  have hJA'0 : ∀ u, 0 ≤ JA' u := fun u => by
    rw [hJA'eq u]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hm0.le) (hμ _ _))
      (div_nonneg (Nat.cast_nonneg _) hdensR.le)
  have hJB'0 : ∀ u, 0 ≤ JB' u := fun u => by
    rw [hJB'eq u]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hm0.le) (hμ _ _))
      (div_nonneg (Nat.cast_nonneg _) hdensR.le)
  have hJA'1 : (∑ u : TracialStrategy.PostTuple n X Y A B D × X × Y, JA' u) = 1 :=
    RoundedSampler.sum_law_A dens hdens (fun x i => numA i x) (fun x i => hsumA i x) μ hμsum
  have hJB'1 : (∑ u : TracialStrategy.PostTuple n X Y A B D × X × Y, JB' u) = 1 :=
    RoundedSampler.sum_law_B dens hdens (fun y i => numB i y) (fun y i => hsumB i y) μ hμsum
  -- Step 10: domination `J' ≥ (1 − ρ) J` and absolute continuity.
  have hdomA : ∀ u, (1 - ρ) * Trep.flatJA R D μ w p u ≤ JA' u := by
    intro u
    rw [hJA'eq u]
    show (1 - ρ) * ((((n - D.card : ℕ) : ℝ))⁻¹ * μ u.2.1 u.2.2 * qA (lc u.1) u.2.1 u.1)
      ≤ m⁻¹ * μ u.2.1 u.2.2 * ((numA (lc u.1) u.2.1 u.1 : ℝ) / dens)
    rw [hmcast]
    have hle := RoundedSampler.le_roundedNum dens ρ (qA (lc u.1) u.2.1) (h₀ (lc u.1)) u.1
    have hq : (1 - ρ) * qA (lc u.1) u.2.1 u.1 ≤ (numA (lc u.1) u.2.1 u.1 : ℝ) / dens := by
      rw [le_div_iff₀ hdensR]
      linarith
    calc (1 - ρ) * (m⁻¹ * μ u.2.1 u.2.2 * qA (lc u.1) u.2.1 u.1)
        = m⁻¹ * μ u.2.1 u.2.2 * ((1 - ρ) * qA (lc u.1) u.2.1 u.1) := by ring
      _ ≤ m⁻¹ * μ u.2.1 u.2.2 * ((numA (lc u.1) u.2.1 u.1 : ℝ) / dens) :=
          mul_le_mul_of_nonneg_left hq (mul_nonneg (inv_nonneg.mpr hm0.le) (hμ _ _))
  have hdomB : ∀ u, (1 - ρ) * Trep.flatJB R D μ w p u ≤ JB' u := by
    intro u
    rw [hJB'eq u]
    show (1 - ρ) * ((((n - D.card : ℕ) : ℝ))⁻¹ * μ u.2.1 u.2.2 * qB (lc u.1) u.2.2 u.1)
      ≤ m⁻¹ * μ u.2.1 u.2.2 * ((numB (lc u.1) u.2.2 u.1 : ℝ) / dens)
    rw [hmcast]
    have hle := RoundedSampler.le_roundedNum dens ρ (qB (lc u.1) u.2.2) (h₀ (lc u.1)) u.1
    have hq : (1 - ρ) * qB (lc u.1) u.2.2 u.1 ≤ (numB (lc u.1) u.2.2 u.1 : ℝ) / dens := by
      rw [le_div_iff₀ hdensR]
      linarith
    calc (1 - ρ) * (m⁻¹ * μ u.2.1 u.2.2 * qB (lc u.1) u.2.2 u.1)
        = m⁻¹ * μ u.2.1 u.2.2 * ((1 - ρ) * qB (lc u.1) u.2.2 u.1) := by ring
      _ ≤ m⁻¹ * μ u.2.1 u.2.2 * ((numB (lc u.1) u.2.2 u.1 : ℝ) / dens) :=
          mul_le_mul_of_nonneg_left hq (mul_nonneg (inv_nonneg.mpr hm0.le) (hμ _ _))
  have hρ0' : 0 < 1 - ρ := by linarith
  have habsA : ∀ u, JA' u = 0 → Trep.flatQ R D μ w p u = 0 := by
    intro u hu
    apply Trep.flatQ_eq_zero_of_flatJA μ hμ R htotF htotG w hw0 hwD hppos hm u
    have h1 := hdomA u
    rw [hu] at h1
    have h2 := Trep.flatJA_nonneg R μ hμ w hw0 hppos u
    have h3 : (1 - ρ) * Trep.flatJA R D μ w p u ≤ (1 - ρ) * 0 := by rw [mul_zero]; exact h1
    exact le_antisymm (le_of_mul_le_mul_left h3 hρ0') h2
  have habsB : ∀ u, JB' u = 0 → Trep.flatQ R D μ w p u = 0 := by
    intro u hu
    apply Trep.flatQ_eq_zero_of_flatJB μ hμ R htotF htotG w hw0 hwD hppos hm u
    have h1 := hdomB u
    rw [hu] at h1
    have h2 := Trep.flatJB_nonneg R μ hμ w hw0 hppos u
    have h3 : (1 - ρ) * Trep.flatJB R D μ w p u ≤ (1 - ρ) * 0 := by rw [mul_zero]; exact h1
    exact le_antisymm (le_of_mul_le_mul_left h3 hρ0') h2
  -- Step 11: relative entropy, total variation, mismatch.
  have hQ0 := Trep.flatQ_nonneg μ hμ R w hw0 hppos
  have hQ1 := Trep.sum_flatQ μ hμ R htotF htotG w hwD hp hppos hm
  have hklA : Pinsker.finiteRelativeEntropy (Trep.flatQ R D μ w p) JA' ≤ 3 * η := by
    have h1 := RoundedSampler.finiteRelativeEntropy_le_of_dominates (Trep.flatQ R D μ w p)
      (Trep.flatJA R D μ w p) JA' hQ0 hQ1 (Trep.flatJA_nonneg R μ hμ w hw0 hppos)
      (Trep.flatQ_eq_zero_of_flatJA μ hμ R htotF htotG w hw0 hwD hppos hm) hJA'0 hJA'1.le hρ1
      hdomA
    have h2 := Trep.logSumA_le μ hμ hμsum R htotF htotG w hw0 hw1 hwD hp hppos hm
    rw [hlogρ] at h1
    calc _ ≤ _ := h1
      _ ≤ T + slack := add_le_add h2 le_rfl
      _ = 3 * η := by rw [hslack]; ring
  have hklB : Pinsker.finiteRelativeEntropy (Trep.flatQ R D μ w p) JB' ≤ 3 * η := by
    have h1 := RoundedSampler.finiteRelativeEntropy_le_of_dominates (Trep.flatQ R D μ w p)
      (Trep.flatJB R D μ w p) JB' hQ0 hQ1 (Trep.flatJB_nonneg R μ hμ w hw0 hppos)
      (Trep.flatQ_eq_zero_of_flatJB μ hμ R htotF htotG w hw0 hwD hppos hm) hJB'0 hJB'1.le hρ1
      hdomB
    have h2 := Trep.logSumB_le μ hμ hμsum R htotF htotG w hw0 hw1 hwD hp hppos hm
    rw [hlogρ] at h1
    calc _ ≤ _ := h1
      _ ≤ T + slack := add_le_add h2 le_rfl
      _ = 3 * η := by rw [hslack]; ring
  have htvA : Pinsker.finiteTotalVariation (Trep.flatQ R D μ w p) JA' ≤ Real.sqrt (3 * η / 2) :=
    (Pinsker.finite_pinsker_sqrt_of_absolute_continuity (Trep.flatQ R D μ w p) JA' hQ0 hJA'0
      habsA hQ1 hJA'1).trans (Real.sqrt_le_sqrt (by linarith))
  have htvB : Pinsker.finiteTotalVariation (Trep.flatQ R D μ w p) JB' ≤ Real.sqrt (3 * η / 2) :=
    (Pinsker.finite_pinsker_sqrt_of_absolute_continuity (Trep.flatQ R D μ w p) JB' hQ0 hJB'0
      habsB hQ1 hJB'1).trans (Real.sqrt_le_sqrt (by linarith))
  have hmis := RoundedSampler.sum_ν_disagree_le dens hdens numA numB hsumA hsumB lc hsA hsB μ hμ
  have hfa : (fun u : TracialStrategy.PostTuple n X Y A B D × X × Y =>
      (Fintype.card {i : Fin n // i ∉ D} : ℝ)⁻¹ * μ u.2.1 u.2.2 *
        ((numA (lc u.1) u.2.1 u.1 : ℝ) / dens)) = JA' := by
    funext u
    rw [hJA'eq u, hcardι]
  have hfb : (fun u : TracialStrategy.PostTuple n X Y A B D × X × Y =>
      (Fintype.card {i : Fin n // i ∉ D} : ℝ)⁻¹ * μ u.2.1 u.2.2 *
        ((numB (lc u.1) u.2.2 u.1 : ℝ) / dens)) = JB' := by
    funext u
    rw [hJB'eq u, hcardι]
  rw [hfa, hfb] at hmis
  have htri := RoundedSampler.finiteTotalVariation_triangle (Trep.flatQ R D μ w p) JA' JB'
  -- Step 12: the ideal success and the alignment defect.
  have hsucc := Trep.flatQ_idealPayoff_ge G hden hnum hV D hm.le hgreedy R
  rw [RoundedSampler.sum_triple] at hsucc
  have halign := Trep.sum_flatQ_alignTerm_le μ R hμ hμsum hcol hrow w hw0 hw1 hwD hp hppos hm
  rw [RoundedSampler.sum_triple] at halign
  have halign' : (∑ h : TracialStrategy.PostTuple n X Y A B D, ∑ x : X, ∑ y : Y,
      Trep.flatQ R D μ w p (h, x, y) * Trep.alignTerm μ R (h, x, y)) ≤ 16 * η := by
    refine halign.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hη1.le (by norm_num)
  -- Assemble: identify the package's laws with the explicit ones.
  have hQflat : P.Qflat = Trep.flatQ R D μ w p := rfl
  have hJAflat : P.JAflat G = JA' := rfl
  have hJBflat : P.JBflat G = JB' := rfl
  have hsuccP : 1 - ε / 4 ≤ P.idealSuccess G := hsucc
  have halignP : P.alignment ≤ 16 * η := halign'
  have hmisP : P.mismatchProb G ≤ 4 * Real.sqrt (3 * η / 2) :=
    hmis.trans (by linarith only [htri, htvA, htvB])
  refine ⟨P, η, hηpos.le, hη2, hsuccP, halignP, ?_, ?_, ?_, ?_, ?_, ?_, hmisP⟩
  · rw [hJAflat, hQflat]; exact habsA
  · rw [hJBflat, hQflat]; exact habsB
  · rw [hJAflat, hQflat]; exact hklA
  · rw [hJBflat, hQflat]; exact hklB
  · rw [hJAflat, hQflat]; exact htvA
  · rw [hJBflat, hQflat]; exact htvB

/-- **Tracial pre-rounding** (node 1.2; 05_prerounding.tex, prop
tracial-prerounding). Standing assumption of Section 5: the payoff is a
predicate. Given a tracially embeddable strategy for `G^{⊗n}` with success
`θ > e^{−γn}`, `0 < ε ≤ 1`, `γ ≤ ε/8`, and `ℓ = log(|A||B|)`, there is a
pre-rounded package and an `η ≤ 8γ(ε + ℓ)/ε` with: ideal success
`≥ 1 − ε/4`; alignment `Δ ≤ 16η`; `D(Q‖J_A), D(Q‖J_B) ≤ 3η` (with the
absolute continuity finiteness implies); `d_TV(Q, J_A), d_TV(Q, J_B) ≤ κ
= √(3η/2)`; and sampler mismatch `Pr[r_A ≠ r_B] ≤ 4κ`. The samplers'
marginals ARE `J_A, J_B` by definition of the package. Obtained from the
weighted form above: a predicate payoff is `0` or `1`, both rational. -/
theorem tracial_prerounding
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
    (G : Game X Y A B) (hV : G.IsPredicate) (n : ℕ) (hn : 1 ≤ n)
    (Trep : TracialStrategy.{0}
      (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
    {ε γ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hγ : γ ≤ ε / 8)
    (hθ : Real.exp (-(γ * n)) < (G.«repeat» n).win Trep.correlation) :
    ∃ (P : PreroundedStrategy X Y A B) (η : ℝ), 0 ≤ η ∧
      η ≤ 8 * γ * ((ε + Real.log ((Fintype.card A : ℝ) *
        (Fintype.card B : ℝ))) / ε) ∧
      1 - ε / 4 ≤ P.idealSuccess G ∧
      P.alignment ≤ 16 * η ∧
      (∀ t, P.JAflat G t = 0 → P.Qflat t = 0) ∧
      (∀ t, P.JBflat G t = 0 → P.Qflat t = 0) ∧
      Pinsker.finiteRelativeEntropy P.Qflat (P.JAflat G) ≤ 3 * η ∧
      Pinsker.finiteRelativeEntropy P.Qflat (P.JBflat G) ≤ 3 * η ∧
      Pinsker.finiteTotalVariation P.Qflat (P.JAflat G)
        ≤ Real.sqrt (3 * η / 2) ∧
      Pinsker.finiteTotalVariation P.Qflat (P.JBflat G)
        ≤ Real.sqrt (3 * η / 2) ∧
      P.mismatchProb G ≤ 4 * Real.sqrt (3 * η / 2) := by
  refine weighted_tracial_prerounding G (fun x y a b => ?_) n hn Trep
    hε0 hε1 hγ hθ
  rcases hV x y a b with h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩

end CommutingRepetition
