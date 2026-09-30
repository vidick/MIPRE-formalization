/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.POVMValue
public import MIPRE.Foundations.CommutingDilation

@[expose] public section

/-!
# Strategies in a bipartite model, read in `ω_co`

The analyses of the stages are written once, for POVM families in a bipartite model
(`MIPRE/Foundations/BipartiteModel.lean`). This file is how such an analysis becomes a statement
about the commuting-operator value `ω_co`, in both directions:

* **from the model to `ω_co`**: a POVM strategy in a bipartite model on a Hilbert space is a
  commuting-operator strategy with the same value (`BipartiteModel.toCommuting`), so its value is
  at most `ω_co` (`BipartiteModel.povmValue_le_commutingOperatorValue`);
* **from `ω_co` to the model**: `ω_co` is approached by strategies whose measurements are
  projective in the players' algebras of their own model (`exists_isPVMIn_lt_povmValue`), by the
  commutation-preserving dilation of Phase 1(a) (`exists_isProjective_lt_value`) and the
  orthogonality of projections summing to one in a C⋆-algebra (`IsPVMIn.of_isStarProjection`).

So a model-level theorem — projective families of value at least `1 - ε` give families in the same
model of value at least `1 - f(ε)` — bounds `ω_co` of the second game below by `1 - f(ε)` as soon
as `ω_co` of the first exceeds `1 - ε`.
-/

namespace MIPRE

open Finset

/-! ## Projective measurements from projections -/

section PVM

variable {R Λ : Type*} [Ring R] [StarRing R] [Fintype Λ] {P : Λ → R}

/-- **An injective unital `⋆`-ring homomorphism reflects projective measurements.** -/
theorem IsPVMIn.of_map {S F : Type*} [Ring S] [StarRing S] [FunLike F R S] [RingHomClass F R S]
    [StarHomClass F R S] {f : F} (hf : Function.Injective f) (h : IsPVMIn fun a => f (P a)) :
    IsPVMIn P where
  star_eq a := hf (by rw [map_star, h.star_eq])
  idem a := hf (by rw [map_mul, h.idem])
  sum_eq_one := hf (by rw [map_sum, h.sum_eq_one, map_one])
  orthogonal hab := hf (by rw [map_mul, h.orthogonal hab, map_zero])

/-- **Projections summing to one are mutually orthogonal**, in a star-ordered ring in which
`x⋆ x = 0` forces `x = 0` — a C⋆-algebra, for instance. Conjugating `∑_c P_c = 1` by `P_a` makes
the compressions `P_a P_c P_a = (P_c P_a)⋆ (P_c P_a)`, `c ≠ a`, nonnegative elements summing to
zero. -/
theorem IsPVMIn.of_isStarProjection [PartialOrder R] [StarOrderedRing R]
    (hR : ∀ x : R, star x * x = 0 → x = 0) (hP : ∀ a, IsStarProjection (P a))
    (hsum : ∑ a, P a = 1) : IsPVMIn P := by
  classical
  have hstar : ∀ a, star (P a) = P a := fun a => (hP a).isSelfAdjoint.star_eq
  have hidem : ∀ a, P a * P a = P a := fun a => (hP a).isIdempotentElem.eq
  refine ⟨hstar, hidem, hsum, fun {a b} hab => ?_⟩
  have hcomp : ∀ c, P a * P c * P a = star (P c * P a) * (P c * P a) := fun c => by
    rw [star_mul, hstar, hstar, show P a * P c * (P c * P a) = P a * (P c * P c) * P a by
      simp only [mul_assoc], hidem]
  have hpos : ∀ c, 0 ≤ P a * P c * P a := fun c => by
    rw [hcomp]
    exact star_mul_self_nonneg _
  have hrest : ∑ c ∈ univ.erase a, P a * P c * P a = 0 := by
    have hall : ∑ c, P a * P c * P a = P a := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_one, hidem]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      show P a * P a * P a = P a by rw [hidem, hidem]] at hall
    exact add_left_cancel (hall.trans (add_zero _).symm)
  have hb : P a * P b * P a = 0 :=
    le_antisymm ((Finset.single_le_sum (fun c _ => hpos c)
      (Finset.mem_erase.mpr ⟨hab.symm, mem_univ b⟩)).trans hrest.le) (hpos b)
  have hba : P b * P a = 0 := hR _ ((hcomp b).symm.trans hb)
  have h := congrArg star hba
  rwa [star_mul, hstar, hstar, star_zero] at h

end PVM

/-! ## A strategy in a model is a commuting-operator strategy -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] (M : BipartiteModel.{0} 𝒞 𝒜 ℬ)
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- **A POVM strategy in a bipartite model is a commuting-operator strategy**: the represented
operators of the two families, on the model's space and state. -/
noncomputable def toCommuting (hψ : ‖M.ψ‖ = 1) (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ) :
    CommutingOperatorStrategy X Y A B where
  H := M.H
  ψ := M.ψ
  ψ_norm := hψ
  E x a := M.π (M.πA ((MA x).op a))
  F y b := M.π (M.πB ((MB y).op b))
  E_pos x a := ContinuousLinearMap.nonneg_iff_isPositive.1 (M.π_πA_nonneg ((MA x).op_nonneg a))
  F_pos y b := ContinuousLinearMap.nonneg_iff_isPositive.1 (M.π_πB_nonneg ((MB y).op_nonneg b))
  E_sum x := by rw [← map_sum, ← map_sum, (MA x).sum_op, map_one, map_one]
  F_sum y := by rw [← map_sum, ← map_sum, (MB y).sum_op, map_one, map_one]
  commutes x y a b := (M.commute _ _).map M.π

theorem correlation_toCommuting (hψ : ‖M.ψ‖ = 1) (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ)
    (x : X) (y : Y) (a : A) (b : B) :
    (M.toCommuting hψ MA MB).correlation x y a b = M.bornProb ((MA x).op a) ((MB y).op b) := by
  show _ = Op.qform M.ψ (M.π (M.πA ((MA x).op a) * M.πB ((MB y).op b)))
  rw [map_mul]
  rfl

/-- **The value of the strategy is its value in the model.** -/
theorem value_toCommuting (hψ : ‖M.ψ‖ = 1) (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ)
    (G : Game X Y A B) : (M.toCommuting hψ MA MB).value G = M.povmValue G MA MB := by
  unfold CommutingOperatorStrategy.value povmValue condWin
  simp only [correlation_toCommuting, Finset.mul_sum, mul_assoc]

/-- **The value of a POVM strategy in a bipartite model is at most `ω_co`.** -/
theorem povmValue_le_commutingOperatorValue (hψ : ‖M.ψ‖ = 1) (MA : X → POVMIn A 𝒜)
    (MB : Y → POVMIn B ℬ) (G : Game X Y A B) :
    M.povmValue G MA MB ≤ commutingOperatorValue G := by
  rw [← M.value_toCommuting hψ MA MB G]
  exact (M.toCommuting hψ MA MB).value_le_commutingOperatorValue G

end BipartiteModel

/-! ## `ω_co` is approached by projective strategies in their own model -/

namespace CommutingOperatorStrategy

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The first player's measurements of a projective strategy are projective in the first player's
algebra of its model. -/
theorem isPVMIn_aliceMeas {S : CommutingOperatorStrategy X Y A B} (hS : S.IsProjective)
    (x : X) : IsPVMIn (S.aliceMeas x).op := by
  refine IsPVMIn.of_map (f := S.aliceAlg.subtype) Subtype.val_injective ?_
  exact IsPVMIn.of_isStarProjection (fun T h => (CStarRing.star_mul_self_eq_zero_iff T).mp h)
    (fun a => ⟨hS.1 x a, (S.E_pos x a).isSelfAdjoint⟩) (S.E_sum x)

/-- The second player's measurements of a projective strategy are projective in the second
player's algebra of its model. -/
theorem isPVMIn_bobMeas {S : CommutingOperatorStrategy X Y A B} (hS : S.IsProjective)
    (y : Y) : IsPVMIn (S.bobMeas y).op := by
  refine IsPVMIn.of_map (f := S.bobAlg.subtype) Subtype.val_injective ?_
  exact IsPVMIn.of_isStarProjection (fun T h => (CStarRing.star_mul_self_eq_zero_iff T).mp h)
    (fun b => ⟨hS.2 y b, (S.F_pos y b).isSelfAdjoint⟩) (S.F_sum y)

end CommutingOperatorStrategy

/-- **`ω_co` is approached by strategies projective in their own model**: below `ω_co`, some
commuting-operator strategy has model value above the threshold with both players' measurements
projective in their algebras. -/
theorem exists_isPVMIn_lt_povmValue {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A]
    [Fintype B] {G : Game X Y A B} {t : ℝ} (ht : 0 ≤ t) (h : t < commutingOperatorValue G) :
    ∃ S : CommutingOperatorStrategy X Y A B, (∀ x, IsPVMIn (S.aliceMeas x).op) ∧
      (∀ y, IsPVMIn (S.bobMeas y).op) ∧ t < S.toModel.povmValue G S.aliceMeas S.bobMeas := by
  obtain ⟨S, hS, hv⟩ := exists_isProjective_lt_value ht h
  exact ⟨S, CommutingOperatorStrategy.isPVMIn_aliceMeas hS,
    CommutingOperatorStrategy.isPVMIn_bobMeas hS, S.value_eq_povmValue G ▸ hv⟩

end MIPRE

end
