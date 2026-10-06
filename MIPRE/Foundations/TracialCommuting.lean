/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.GNS
public import MIPRE.Foundations.Correlations
public import MIPRE.Tactics

@[expose] public section

/-!
# Tracial strategies are commuting-operator strategies

Blueprint `lem:tracial-le-co`: for every synchronous game `G`, the tracial commuting value is at
most the bipartite commuting-operator value, `commValue G ≤ commutingOperatorValue G.toGame`.

Given a commuting strategy `(𝒜, τ, M)`, the GNS space of `τ` (`MIPRE/Foundations/GNS.lean`) is
the completion of `𝒜` for `⟨a, b⟩ = τ(a⋆ b)`, with the class of `1` as the unit vector. The first
player's operators are the lifts of left multiplication by `M^x_a`, the second player's those of
*right* multiplication by `M^y_b`. Left and right multiplications commute exactly, by
associativity, and the correlation is `τ(1⋆ M^x_a M^y_b) = τ(M^x_a M^y_b)`, so the strategy has
the value of `(𝒜, τ, M)`.

Right multiplication by a projection `g` is where the trace is used. It is a contraction,
`τ((s g)⋆ (s g)) = τ(s⋆ s g) ≤ τ(s⋆ s)` because `τ(s⋆ s (1 - g)) = τ((s (1 - g))⋆ (s (1 - g)))`.
It is symmetric for the form, `τ((s g)⋆ t) = τ(s⋆ t g)`, and positive, `τ(s⋆ s g) =
τ((s g)⋆ (s g))`. No norm on `𝒜` is used: the argument is algebraic in the projections and the
trace, and the bounds come from the positivity of `τ` alone.

A tracial state is Hermitian, `τ(a⋆) = conj τ(a)`, by polarization of its positivity at
`1 + a` and `1 + i a` (`TracialState.map_star`). So it is a GNS state (`TracialState.toState`).

## Main declarations

* `TracialState.map_star`, `TracialState.toState`;
* `TracialCo.bdd_mulRight`, `TracialCo.lift_mulRight_isPositive`;
* `CommutingStrategy.toCommutingOperatorStrategy`, `CommutingStrategy.value_toCommutingOperator`;
* `commValue_le_commutingOperatorValue`.
-/

open scoped InnerProductSpace ComplexConjugate

namespace MIPRE

variable {𝒜 : Type} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]

namespace TracialState

omit [StarModule ℂ 𝒜] in
/-- The value of a tracial state on `m⋆ m` is real. -/
theorem im_star_mul_self (τ : TracialState 𝒜) (m : 𝒜) : (τ (star m * m)).im = 0 :=
  ((Complex.le_def.mp (τ.star_mul_self_nonneg m)).2).symm

/-- **A tracial state is Hermitian**: `τ(a⋆) = conj τ(a)`, by polarization of positivity at
`1 + a` and `1 + i a`. -/
theorem map_star (τ : TracialState 𝒜) (a : 𝒜) : τ (star a) = conj (τ a) := by
  have h1 := τ.im_star_mul_self (1 + a)
  have h2 := τ.im_star_mul_self (1 + Complex.I • a)
  have h0 := τ.im_star_mul_self a
  have e1 : star (1 + a) * (1 + a) = 1 + a + star a + star a * a := by
    simp only [star_add, star_one]; noncomm_ring
  have e2 : star (1 + Complex.I • a) * (1 + Complex.I • a) =
      1 + Complex.I • a - Complex.I • star a + star a * a := by
    have hs : star (1 + Complex.I • a) = 1 - Complex.I • star a := by
      rw [star_add, star_one, star_smul, Complex.star_def, Complex.conj_I, neg_smul,
        sub_eq_add_neg]
    rw [hs, sub_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_smul_comm,
      Complex.I_mul_I, neg_one_smul]
    abel
  rw [e1, map_add, map_add, map_add, τ.map_one] at h1
  rw [e2, map_add, map_sub, map_add, τ.map_one, map_smul, map_smul] at h2
  simp only [Complex.add_im, Complex.one_im, Complex.sub_im, smul_eq_mul, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at h1 h2
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith

/-- A tracial state as a GNS state (`MIPRE.GNS.State`). -/
def toState (τ : TracialState 𝒜) : GNS.State 𝒜 where
  L := τ.toLinearMap
  map_one := τ.map_one
  map_star := τ.map_star
  nonneg a := (Complex.le_def.mp (τ.star_mul_self_nonneg a)).1

@[simp] theorem toState_L (τ : TracialState 𝒜) (a : 𝒜) : τ.toState.L a = τ a := rfl

end TracialState

namespace TracialCo

open GNS

variable (τ : TracialState 𝒜) {g : 𝒜}

omit [StarModule ℂ 𝒜] in
/-- The GNS form of `τ` against right multiplication: `τ((s g)⋆ t) = τ(s⋆ t g)` for
self-adjoint `g`. -/
theorem form_mulRight_left (hgs : star g = g) (s t : 𝒜) :
    τ (star (s * g) * t) = τ (star s * (t * g)) := by
  rw [star_mul, hgs, mul_assoc, τ.map_mul_comm, mul_assoc]

omit [StarModule ℂ 𝒜] in
/-- For a projection `g`, `τ(s⋆ s g) = τ((s g)⋆ (s g))`. -/
theorem form_mulRight_self (hgs : star g = g) (hgg : g * g = g) (s : 𝒜) :
    τ (star s * (s * g)) = τ (star (s * g) * (s * g)) := by
  rw [form_mulRight_left τ hgs, mul_assoc, hgg]

/-- **Right multiplication by a projection is a contraction for the GNS form of a tracial
state.** -/
theorem bdd_mulRight (hgs : star g = g) (hgg : g * g = g) :
    Bdd τ.toState.form (LinearMap.mulRight ℂ g) := by
  refine bdd_of_contraction _ _ fun s => ?_
  simp only [State.form_B, LinearMap.mulRight_apply, TracialState.toState_L]
  have h1g : star (1 - g) = 1 - g := by rw [star_sub, star_one, hgs]
  have h1gg : (1 - g) * (1 - g) = 1 - g := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hgg]; abel
  have hpos := (Complex.le_def.mp (τ.star_mul_self_nonneg (s * (1 - g)))).1
  rw [← form_mulRight_self τ h1g h1gg, mul_sub, mul_one, mul_sub, map_sub,
    Complex.sub_re] at hpos
  rw [← form_mulRight_self τ hgs hgg]
  simp only [Complex.zero_re] at hpos
  linarith

/-- The lift of right multiplication by a projection is a positive operator. -/
theorem lift_mulRight_isPositive (hgs : star g = g) (hgg : g * g = g) :
    (lift τ.toState.form (LinearMap.mulRight ℂ g) (bdd_mulRight τ hgs hgg)).IsPositive := by
  refine lift_isPositive _ _ _ (fun u v => ?_) (fun v => ?_)
  · simp only [State.form_B, LinearMap.mulRight_apply, TracialState.toState_L]
    exact form_mulRight_left τ hgs u v
  · simp only [State.form_B, LinearMap.mulRight_apply, TracialState.toState_L]
    rw [form_mulRight_self τ hgs hgg]
    exact (Complex.le_def.mp (τ.star_mul_self_nonneg _)).1

/-- Left multiplication by a projection is bounded for the GNS form of a tracial state. -/
theorem bdd_mulLeft (hgs : star g = g) (hgg : g * g = g) :
    Bdd τ.toState.form (LinearMap.mulLeft ℂ g) := by
  refine τ.toState.bdd_mulLeft g fun s => ?_
  have h1g : star (1 - g) = 1 - g := by rw [star_sub, star_one, hgs]
  have h1gg : (1 - g) * (1 - g) = 1 - g := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hgg]; abel
  have e : star s * (1 - star g * g) * s = star ((1 - g) * s) * ((1 - g) * s) := by
    rw [hgs, hgg, star_mul, h1g, ← mul_assoc, mul_assoc (star s) (1 - g) (1 - g), h1gg]
  rw [e]
  exact (Complex.le_def.mp (τ.star_mul_self_nonneg _)).1

/-- The lift of left multiplication by a projection is a positive operator. -/
theorem lift_mulLeft_isPositive (hgs : star g = g) (hgg : g * g = g) :
    (lift τ.toState.form (LinearMap.mulLeft ℂ g) (bdd_mulLeft τ hgs hgg)).IsPositive := by
  refine τ.toState.lift_mulLeft_isPositive g _ hgs fun s => ?_
  have e : star s * g * s = star (g * s) * (g * s) := by
    rw [star_mul, hgs, ← mul_assoc, mul_assoc (star s) g g, hgg]
  rw [e]
  exact (Complex.le_def.mp (τ.star_mul_self_nonneg _)).1

end TracialCo

/-! ## The commuting-operator strategy of a commuting strategy -/

namespace CommutingStrategy

open GNS TracialCo

variable {X A : Type} [Fintype X] [Fintype A] [DecidableEq A] {G : SynchronousGame X A}

/-- **The GNS strategy of a tracial strategy**: on the GNS space of `τ`, with the cyclic vector
`ι 1`, the first player multiplies on the left by `M^x_a`, the second on the right by `M^y_b`. -/
noncomputable def toCommutingOperatorStrategy (S : CommutingStrategy G) :
    CommutingOperatorStrategy X X A A where
  H := H S.τ.toState.form
  ψ := ι S.τ.toState.form 1
  ψ_norm := S.τ.toState.norm_ι_one
  E x a := lift _ _ (bdd_mulLeft S.τ (S.P.selfAdjoint x a) (S.P.projective x a))
  F y b := lift _ _ (bdd_mulRight S.τ (S.P.selfAdjoint y b) (S.P.projective y b))
  E_pos x a := lift_mulLeft_isPositive S.τ (S.P.selfAdjoint x a) (S.P.projective x a)
  F_pos y b := lift_mulRight_isPositive S.τ (S.P.selfAdjoint y b) (S.P.projective y b)
  E_sum x := sum_lift_eq_one _ _ _ fun v => by
    rw [sum_mulLeft_apply, S.P.normalized x, one_mul, sub_self, map_zero]
  F_sum y := sum_lift_eq_one _ _ _ fun v => by
    rw [LinearMap.sum_apply]
    simp only [LinearMap.mulRight_apply]
    rw [← Finset.mul_sum, S.P.normalized y, mul_one, sub_self, map_zero]
  commutes x y a b := commute_lift _ _ _ fun v => by
    simp only [LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    rw [mul_assoc, sub_self, map_zero]

/-- The correlation of the GNS strategy is `Re τ(M^x_a M^y_b)`. -/
theorem correlation_toCommutingOperatorStrategy (S : CommutingStrategy G) (x y : X) (a b : A) :
    S.toCommutingOperatorStrategy.correlation x y a b = (S.τ (S.P.M x a * S.P.M y b)).re := by
  change (⟪ι S.τ.toState.form 1, lift _ _ (bdd_mulLeft S.τ (S.P.selfAdjoint x a)
    (S.P.projective x a)) (lift _ _ (bdd_mulRight S.τ (S.P.selfAdjoint y b)
    (S.P.projective y b)) (ι S.τ.toState.form 1))⟫_ℂ).re = _
  rw [lift_ι, lift_ι, State.inner_ι]
  simp only [LinearMap.mulLeft_apply, LinearMap.mulRight_apply, star_one, one_mul,
    TracialState.toState_L]

/-- **The GNS strategy has the value of the tracial strategy.** -/
theorem value_toCommutingOperatorStrategy (S : CommutingStrategy G) :
    S.toCommutingOperatorStrategy.value G.toGame = S.value := by
  simp only [CommutingOperatorStrategy.value, CommutingStrategy.value, tracialValue,
    correlation_toCommutingOperatorStrategy]
  rfl

end CommutingStrategy

/-- **Tracial strategies are commuting-operator strategies** (blueprint `lem:tracial-le-co`):
the commuting value of a synchronous game is at most the commuting-operator value of its
bipartite game. -/
theorem commValue_le_commutingOperatorValue {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq A] (G : SynchronousGame X A) :
    commValue G ≤ commutingOperatorValue G.toGame :=
  Real.iSup_le (fun S => by
    rw [← S.value_toCommutingOperatorStrategy]
    exact S.toCommutingOperatorStrategy.value_le_commutingOperatorValue G.toGame)
    (commutingOperatorValue_nonneg _)

end MIPRE

end
