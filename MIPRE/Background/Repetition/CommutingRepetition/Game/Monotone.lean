/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Game/Monotone.lean
-/
/-
# Marginal monotonicity and payoff perturbation

Statement skeleton for audit nodes 1.6.1 and 1.6.3 (perturbation half).
Anchors: 07_main_theorem.tex, sec 7.4, eqs marginal-monotonicity and
payoff-rational-approximation.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Game.Basic
import MIPRE.Background.Repetition.CommutingRepetition.Game.Value
import MIPRE.Background.Repetition.CommutingRepetition.Game.Strategy
import MIPRE.Background.Repetition.CommutingRepetition.Game.Mixture
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Scalar

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

namespace Game

section Presample

variable {n : ℕ}

/-- The product question law over any finite index set is normalized. -/
private theorem prod_law_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Game X Y A B) :
    (∑ xs : ι → X, ∑ ys : ι → Y,
      ∏ j : ι, G.questionWeight (xs j) (ys j)) = 1 := by
  classical
  calc (∑ xs : ι → X, ∑ ys : ι → Y,
        ∏ j : ι, G.questionWeight (xs j) (ys j))
      = ∑ xs : ι → X, ∏ j : ι, ∑ y : Y, G.questionWeight (xs j) y := by
        refine Finset.sum_congr rfl fun xs _ => ?_
        exact (Fintype.prod_sum
          (fun j : ι => fun y : Y => G.questionWeight (xs j) y)).symm
    _ = ∏ _j : ι, ∑ x : X, ∑ y : Y, G.questionWeight x y := by
        exact (Fintype.prod_sum
          (fun _j : ι => fun x : X => ∑ y : Y, G.questionWeight x y)).symm
    _ = 1 := by simp [G.weight_normalized]

/-- Collapsing the one-shot answer pair against the coordinate-`i`
indicator of the marginalized effects. -/
private theorem answer_collapse [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (i : Fin n) (x : X) (y : Y)
    (c : (Fin n → A) → (Fin n → B) → ℝ) :
    (∑ a : A, ∑ b : B, G.payoff x y a b *
        ∑ as : Fin n → A, ∑ bs : Fin n → B,
          (if as i = a then (if bs i = b then c as bs else 0) else 0))
      = ∑ as : Fin n → A, ∑ bs : Fin n → B,
          G.payoff x y (as i) (bs i) * c as bs := by
  calc (∑ a : A, ∑ b : B, G.payoff x y a b *
        ∑ as : Fin n → A, ∑ bs : Fin n → B,
          (if as i = a then (if bs i = b then c as bs else 0) else 0))
      = ∑ a : A, ∑ b : B, ∑ as : Fin n → A, ∑ bs : Fin n → B,
          (if as i = a then (if bs i = b then
            G.payoff x y a b * c as bs else 0) else 0) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl
          fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun as _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun bs _ => ?_
        split
        · split
          · rfl
          · rw [mul_zero]
        · rw [mul_zero]
    _ = ∑ as : Fin n → A, ∑ bs : Fin n → B, ∑ a : A, ∑ b : B,
          (if as i = a then (if bs i = b then
            G.payoff x y a b * c as bs else 0) else 0) := sum4_swap _
    _ = ∑ as : Fin n → A, ∑ bs : Fin n → B,
          G.payoff x y (as i) (bs i) * c as bs := by
        refine Finset.sum_congr rfl fun as _ => Finset.sum_congr rfl
          fun bs _ => ?_
        rw [show (∑ a : A, ∑ b : B, if as i = a then (if bs i = b then
            G.payoff x y a b * c as bs else 0) else 0)
          = ∑ a : A, if as i = a then (∑ b : B, if bs i = b then
              G.payoff x y a b * c as bs else 0) else 0 from
          Finset.sum_congr rfl fun a _ => by
            split
            · rfl
            · exact Finset.sum_const_zero]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- Presampling change of variables: sampling the off-`i` coordinates from
the product law and the live pair from `μ` reproduces the full product
law. -/
private theorem presample_change_of_variables (i : Fin n)
    (G : Game X Y A B) (g : (Fin n → X) → (Fin n → Y) → ℝ) :
    (∑ rx : {j : Fin n // j ≠ i} → X, ∑ ry : {j : Fin n // j ≠ i} → Y,
      ∑ x : X, ∑ y : Y,
        (∏ j : {j : Fin n // j ≠ i}, G.questionWeight (rx j) (ry j)) *
          G.questionWeight x y *
          g ((Equiv.funSplitAt i X).symm (x, rx))
            ((Equiv.funSplitAt i Y).symm (y, ry)))
      = ∑ w : Fin n → X, ∑ v : Fin n → Y,
          (∏ j : Fin n, G.questionWeight (w j) (v j)) * g w v := by
  classical
  have hsplit : ∀ (x : X) (rx : {j : Fin n // j ≠ i} → X)
      (y : Y) (ry : {j : Fin n // j ≠ i} → Y),
      (∏ j : Fin n, G.questionWeight
        (((Equiv.funSplitAt i X).symm (x, rx)) j)
        (((Equiv.funSplitAt i Y).symm (y, ry)) j))
      = G.questionWeight x y *
        ∏ j : {j : Fin n // j ≠ i}, G.questionWeight (rx j) (ry j) := by
    intro x rx y ry
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · rw [Finset.prod_subtype (p := fun j : Fin n => j ≠ i)
        (Finset.univ.erase i)
        (fun j => by simp [Finset.mem_erase])
        (fun j => G.questionWeight
          (((Equiv.funSplitAt i X).symm (x, rx)) j)
          (((Equiv.funSplitAt i Y).symm (y, ry)) j))]
      refine Finset.prod_congr rfl fun j _ => ?_
      have hji : (j : Fin n) ≠ i := j.2
      simp [Equiv.funSplitAt, Equiv.piSplitAt, dif_neg hji]
  calc (∑ rx : {j : Fin n // j ≠ i} → X, ∑ ry : {j : Fin n // j ≠ i} → Y,
        ∑ x : X, ∑ y : Y,
          (∏ j : {j : Fin n // j ≠ i}, G.questionWeight (rx j) (ry j)) *
            G.questionWeight x y *
            g ((Equiv.funSplitAt i X).symm (x, rx))
              ((Equiv.funSplitAt i Y).symm (y, ry)))
      = ∑ x : X, ∑ rx : {j : Fin n // j ≠ i} → X,
          ∑ y : Y, ∑ ry : {j : Fin n // j ≠ i} → Y,
          (∏ j : {j : Fin n // j ≠ i}, G.questionWeight (rx j) (ry j)) *
            G.questionWeight x y *
            g ((Equiv.funSplitAt i X).symm (x, rx))
              ((Equiv.funSplitAt i Y).symm (y, ry)) := by
        calc (∑ rx : {j : Fin n // j ≠ i} → X,
              ∑ ry : {j : Fin n // j ≠ i} → Y, ∑ x : X, ∑ y : Y,
              (∏ j : {j : Fin n // j ≠ i},
                G.questionWeight (rx j) (ry j)) *
                G.questionWeight x y *
                g ((Equiv.funSplitAt i X).symm (x, rx))
                  ((Equiv.funSplitAt i Y).symm (y, ry)))
            = ∑ rx : {j : Fin n // j ≠ i} → X, ∑ x : X,
                ∑ ry : {j : Fin n // j ≠ i} → Y, ∑ y : Y,
                (∏ j : {j : Fin n // j ≠ i},
                  G.questionWeight (rx j) (ry j)) *
                  G.questionWeight x y *
                  g ((Equiv.funSplitAt i X).symm (x, rx))
                    ((Equiv.funSplitAt i Y).symm (y, ry)) :=
              Finset.sum_congr rfl fun rx _ => Finset.sum_comm
          _ = ∑ x : X, ∑ rx : {j : Fin n // j ≠ i} → X,
                ∑ ry : {j : Fin n // j ≠ i} → Y, ∑ y : Y,
                (∏ j : {j : Fin n // j ≠ i},
                  G.questionWeight (rx j) (ry j)) *
                  G.questionWeight x y *
                  g ((Equiv.funSplitAt i X).symm (x, rx))
                    ((Equiv.funSplitAt i Y).symm (y, ry)) := Finset.sum_comm
          _ = ∑ x : X, ∑ rx : {j : Fin n // j ≠ i} → X,
                ∑ y : Y, ∑ ry : {j : Fin n // j ≠ i} → Y,
                (∏ j : {j : Fin n // j ≠ i},
                  G.questionWeight (rx j) (ry j)) *
                  G.questionWeight x y *
                  g ((Equiv.funSplitAt i X).symm (x, rx))
                    ((Equiv.funSplitAt i Y).symm (y, ry)) :=
              Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl
                fun rx _ => Finset.sum_comm
    _ = ∑ w : Fin n → X, ∑ v : Fin n → Y,
          (∏ j : Fin n, G.questionWeight (w j) (v j)) * g w v := by
        rw [← Equiv.sum_comp (Equiv.funSplitAt i X).symm
          (fun w => ∑ v : Fin n → Y,
            (∏ j : Fin n, G.questionWeight (w j) (v j)) * g w v),
          Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl
          fun rx _ => ?_
        rw [← Equiv.sum_comp (Equiv.funSplitAt i Y).symm
          (fun v => (∏ j : Fin n, G.questionWeight
            (((Equiv.funSplitAt i X).symm (x, rx)) j) (v j)) *
            g ((Equiv.funSplitAt i X).symm (x, rx)) v),
          Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl
          fun ry _ => ?_
        rw [hsplit x rx y ry]
        ring

end Presample

/-- **Marginal monotonicity** (node 1.6.1; 07_main_theorem.tex, eq
marginal-monotonicity): `ω^co(G^{⊗n}) ≤ ω^co(G)` for every `n ≥ 1`.
Stated for arbitrary `[0,1]` payoffs — a disclosed safe-direction
strengthening of the manuscript's predicate-context display
(DIFFERENCES.md D11). Proof: presample the other `n − 1` question pairs
with shared randomness (the seed mixture of `Game/Mixture.lean`), play
the chosen coordinate `i`, and marginalize the answers; the product
payoff is bounded by the coordinate-`i` payoff since all factors lie in
`[0,1]`. -/
theorem repeat_omegaCO_le [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
    (G : Game X Y A B) (n : ℕ) (hn : 1 ≤ n) :
    (G.«repeat» n).omegaCO ≤ G.omegaCO := by
  classical
  refine csSup_le
    ⟨_, ⟨CommutingStrategy.trivial (X := Fin n → X) (Y := Fin n → Y), rfl⟩⟩ ?_
  rintro _ ⟨S, rfl⟩
  show (G.«repeat» n).win S.correlation ≤ G.omegaCO
  set i : Fin n := ⟨0, hn⟩ with hidef
  -- The presampled one-shot strategy, kept abstract through its
  -- correlation formula.
  obtain ⟨Sc, hSc⟩ : ∃ Sc : CommutingStrategy.{0} X Y A B,
      ∀ (x : X) (y : Y) (a : A) (b : B), Sc.correlation x y a b
        = ∑ ω : ({j : Fin n // j ≠ i} → X) × ({j : Fin n // j ≠ i} → Y),
            (∏ j : {j : Fin n // j ≠ i},
              G.questionWeight (ω.1 j) (ω.2 j)) *
              ∑ as : Fin n → A, ∑ bs : Fin n → B,
                (if as i = a then (if bs i = b then
                  S.correlation ((Equiv.funSplitAt i X).symm (x, ω.1))
                    ((Equiv.funSplitAt i Y).symm (y, ω.2)) as bs
                  else 0) else 0) := by
    refine ⟨CommutingStrategy.seedMixture
    (Seed := ({j : Fin n // j ≠ i} → X) × ({j : Fin n // j ≠ i} → Y))
    (fun ω => ∏ j : {j : Fin n // j ≠ i},
      G.questionWeight (ω.1 j) (ω.2 j))
    (fun ω => Finset.prod_nonneg fun j _ => G.weight_nonneg _ _)
    (by
      rw [show (∑ ω : ({j : Fin n // j ≠ i} → X) ×
          ({j : Fin n // j ≠ i} → Y),
          ∏ j : {j : Fin n // j ≠ i},
            G.questionWeight (ω.1 j) (ω.2 j))
          = ∑ rx : {j : Fin n // j ≠ i} → X,
              ∑ ry : {j : Fin n // j ≠ i} → Y,
              ∏ j : {j : Fin n // j ≠ i},
                G.questionWeight (rx j) (ry j) from
        Fintype.sum_prod_type
          (fun ω : ({j : Fin n // j ≠ i} → X) ×
            ({j : Fin n // j ≠ i} → Y) =>
            ∏ j : {j : Fin n // j ≠ i},
              G.questionWeight (ω.1 j) (ω.2 j))]
      exact prod_law_sum G)
    S.ψ S.ψ_norm
    (fun ω x a => ∑ as : Fin n → A,
      if as i = a then S.E ((Equiv.funSplitAt i X).symm (x, ω.1)) as
      else 0)
    (fun ω y b => ∑ bs : Fin n → B,
      if bs i = b then S.F ((Equiv.funSplitAt i Y).symm (y, ω.2)) bs
      else 0)
    (fun ω x a => isPositive_sum _ _ fun as _ =>
      isPositive_ite _ fun _ => S.E_pos _ as)
    (fun ω y b => isPositive_sum _ _ fun bs _ =>
      isPositive_ite _ fun _ => S.F_pos _ bs)
    (fun ω x => by
      rw [Finset.sum_comm]
      rw [show (∑ as : Fin n → A, ∑ a : A,
          if as i = a then S.E ((Equiv.funSplitAt i X).symm (x, ω.1)) as
          else 0)
          = ∑ as : Fin n → A,
              S.E ((Equiv.funSplitAt i X).symm (x, ω.1)) as from
        Finset.sum_congr rfl fun as _ => by
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]]
      exact S.E_sum _)
    (fun ω y => by
      rw [Finset.sum_comm]
      rw [show (∑ bs : Fin n → B, ∑ b : B,
          if bs i = b then S.F ((Equiv.funSplitAt i Y).symm (y, ω.2)) bs
          else 0)
          = ∑ bs : Fin n → B,
              S.F ((Equiv.funSplitAt i Y).symm (y, ω.2)) bs from
        Finset.sum_congr rfl fun bs _ => by
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]]
      exact S.F_sum _)
    (fun ω x y a b => Commute.sum_left _ _ _ fun as _ =>
      Commute.sum_right _ _ _ fun bs _ => by
        split_ifs
        · exact S.commutes _ _ as bs
        · exact Commute.zero_right _
        · exact Commute.zero_left _
        · exact Commute.zero_left _), ?_⟩
    intro x y a b
    rw [CommutingStrategy.seedMixture_correlation]
    refine Finset.sum_congr rfl fun ω _ => ?_
    congr 1
    calc (⟪S.ψ, (∑ as : Fin n → A,
          if as i = a then S.E ((Equiv.funSplitAt i X).symm (x, ω.1)) as
          else 0)
          ((∑ bs : Fin n → B,
            if bs i = b then S.F ((Equiv.funSplitAt i Y).symm (y, ω.2)) bs
            else 0) S.ψ)⟫_ℂ).re
        = (∑ as : Fin n → A, ∑ bs : Fin n → B,
            ⟪S.ψ, (if as i = a then
                S.E ((Equiv.funSplitAt i X).symm (x, ω.1)) as else 0)
              ((if bs i = b then
                S.F ((Equiv.funSplitAt i Y).symm (y, ω.2)) bs else 0)
                S.ψ)⟫_ℂ).re := by
          congr 1
          rw [ContinuousLinearMap.sum_apply, inner_sum]
          refine Finset.sum_congr rfl fun as _ => ?_
          rw [ContinuousLinearMap.sum_apply, map_sum, inner_sum]
      _ = ∑ as : Fin n → A, ∑ bs : Fin n → B,
            (⟪S.ψ, (if as i = a then
                S.E ((Equiv.funSplitAt i X).symm (x, ω.1)) as else 0)
              ((if bs i = b then
                S.F ((Equiv.funSplitAt i Y).symm (y, ω.2)) bs else 0)
                S.ψ)⟫_ℂ).re := by
          rw [Complex.re_sum]
          exact Finset.sum_congr rfl fun as _ => Complex.re_sum _ _
      _ = ∑ as : Fin n → A, ∑ bs : Fin n → B,
            (if as i = a then (if bs i = b then
              S.correlation ((Equiv.funSplitAt i X).symm (x, ω.1))
                ((Equiv.funSplitAt i Y).symm (y, ω.2)) as bs
              else 0) else 0) := by
          refine Finset.sum_congr rfl fun as _ =>
            Finset.sum_congr rfl fun bs _ => ?_
          split_ifs
          · rfl
          · simp
          · simp
          · simp
  -- Bound through the presampled strategy's value.
  refine le_trans ?_ (G.le_omegaCO Sc)
  have hwx : ∀ (x : X) (rx : {j : Fin n // j ≠ i} → X),
      ((Equiv.funSplitAt i X).symm (x, rx)) i = x := by
    intro x rx
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hwy : ∀ (y : Y) (ry : {j : Fin n // j ≠ i} → Y),
      ((Equiv.funSplitAt i Y).symm (y, ry)) i = y := by
    intro y ry
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  -- The mixture's win in change-of-variables form.
  have hScwin : G.win Sc.correlation
      = ∑ w : Fin n → X, ∑ v : Fin n → Y,
          (∏ j : Fin n, G.questionWeight (w j) (v j)) *
            ∑ as : Fin n → A, ∑ bs : Fin n → B,
              G.payoff (w i) (v i) (as i) (bs i) *
                S.correlation w v as bs := by
    unfold Game.win
    simp only [hSc]
    calc (∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
          G.questionWeight x y * G.payoff x y a b *
            ∑ ω : ({j : Fin n // j ≠ i} → X) ×
              ({j : Fin n // j ≠ i} → Y),
              (∏ j : {j : Fin n // j ≠ i},
                G.questionWeight (ω.1 j) (ω.2 j)) *
                ∑ as : Fin n → A, ∑ bs : Fin n → B,
                  (if as i = a then (if bs i = b then
                    S.correlation ((Equiv.funSplitAt i X).symm (x, ω.1))
                      ((Equiv.funSplitAt i Y).symm (y, ω.2)) as bs
                    else 0) else 0))
        = ∑ x : X, ∑ y : Y,
            ∑ ω : ({j : Fin n // j ≠ i} → X) ×
              ({j : Fin n // j ≠ i} → Y),
              (∏ j : {j : Fin n // j ≠ i},
                G.questionWeight (ω.1 j) (ω.2 j)) *
                G.questionWeight x y *
                ∑ a : A, ∑ b : B, G.payoff x y a b *
                  ∑ as : Fin n → A, ∑ bs : Fin n → B,
                    (if as i = a then (if bs i = b then
                      S.correlation ((Equiv.funSplitAt i X).symm (x, ω.1))
                        ((Equiv.funSplitAt i Y).symm (y, ω.2)) as bs
                      else 0) else 0) := by
          refine Finset.sum_congr rfl fun x _ =>
            Finset.sum_congr rfl fun y _ => ?_
          calc (∑ a : A, ∑ b : B, G.questionWeight x y *
                G.payoff x y a b *
                ∑ ω : ({j : Fin n // j ≠ i} → X) ×
                  ({j : Fin n // j ≠ i} → Y),
                  (∏ j : {j : Fin n // j ≠ i},
                    G.questionWeight (ω.1 j) (ω.2 j)) *
                    ∑ as : Fin n → A, ∑ bs : Fin n → B,
                      (if as i = a then (if bs i = b then
                        S.correlation
                          ((Equiv.funSplitAt i X).symm (x, ω.1))
                          ((Equiv.funSplitAt i Y).symm (y, ω.2)) as bs
                        else 0) else 0))
              = ∑ a : A, ∑ b : B, ∑ ω : ({j : Fin n // j ≠ i} → X) ×
                  ({j : Fin n // j ≠ i} → Y),
                  (∏ j : {j : Fin n // j ≠ i},
                    G.questionWeight (ω.1 j) (ω.2 j)) *
                    G.questionWeight x y *
                    (G.payoff x y a b *
                      ∑ as : Fin n → A, ∑ bs : Fin n → B,
                        (if as i = a then (if bs i = b then
                          S.correlation
                            ((Equiv.funSplitAt i X).symm (x, ω.1))
                            ((Equiv.funSplitAt i Y).symm (y, ω.2)) as bs
                          else 0) else 0)) := by
                refine Finset.sum_congr rfl fun a _ =>
                  Finset.sum_congr rfl fun b _ => ?_
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun ω _ => by ring
            _ = ∑ ω : ({j : Fin n // j ≠ i} → X) ×
                  ({j : Fin n // j ≠ i} → Y), ∑ a : A, ∑ b : B,
                  (∏ j : {j : Fin n // j ≠ i},
                    G.questionWeight (ω.1 j) (ω.2 j)) *
                    G.questionWeight x y *
                    (G.payoff x y a b *
                      ∑ as : Fin n → A, ∑ bs : Fin n → B,
                        (if as i = a then (if bs i = b then
                          S.correlation
                            ((Equiv.funSplitAt i X).symm (x, ω.1))
                            ((Equiv.funSplitAt i Y).symm (y, ω.2)) as bs
                          else 0) else 0)) := sum3_swap _
            _ = ∑ ω : ({j : Fin n // j ≠ i} → X) ×
                  ({j : Fin n // j ≠ i} → Y),
                  (∏ j : {j : Fin n // j ≠ i},
                    G.questionWeight (ω.1 j) (ω.2 j)) *
                    G.questionWeight x y *
                    ∑ a : A, ∑ b : B, G.payoff x y a b *
                      ∑ as : Fin n → A, ∑ bs : Fin n → B,
                        (if as i = a then (if bs i = b then
                          S.correlation
                            ((Equiv.funSplitAt i X).symm (x, ω.1))
                            ((Equiv.funSplitAt i Y).symm (y, ω.2)) as bs
                          else 0) else 0) := by
                refine Finset.sum_congr rfl fun ω _ => ?_
                rw [sum2_mul_left]
      _ = ∑ x : X, ∑ y : Y,
            ∑ ω : ({j : Fin n // j ≠ i} → X) ×
              ({j : Fin n // j ≠ i} → Y),
              (∏ j : {j : Fin n // j ≠ i},
                G.questionWeight (ω.1 j) (ω.2 j)) *
                G.questionWeight x y *
                ∑ as : Fin n → A, ∑ bs : Fin n → B,
                  G.payoff x y (as i) (bs i) *
                    S.correlation ((Equiv.funSplitAt i X).symm (x, ω.1))
                      ((Equiv.funSplitAt i Y).symm (y, ω.2)) as bs := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl
            fun y _ => Finset.sum_congr rfl fun ω _ => ?_
          rw [answer_collapse]
      _ = ∑ ω : ({j : Fin n // j ≠ i} → X) ×
            ({j : Fin n // j ≠ i} → Y), ∑ x : X, ∑ y : Y,
            (∏ j : {j : Fin n // j ≠ i},
              G.questionWeight (ω.1 j) (ω.2 j)) *
              G.questionWeight x y *
              ∑ as : Fin n → A, ∑ bs : Fin n → B,
                G.payoff x y (as i) (bs i) *
                  S.correlation ((Equiv.funSplitAt i X).symm (x, ω.1))
                    ((Equiv.funSplitAt i Y).symm (y, ω.2)) as bs :=
          sum3_swap _
      _ = ∑ rx : {j : Fin n // j ≠ i} → X,
            ∑ ry : {j : Fin n // j ≠ i} → Y, ∑ x : X, ∑ y : Y,
            (∏ j : {j : Fin n // j ≠ i},
              G.questionWeight (rx j) (ry j)) *
              G.questionWeight x y *
              (∑ as : Fin n → A, ∑ bs : Fin n → B,
                G.payoff (((Equiv.funSplitAt i X).symm (x, rx)) i)
                  (((Equiv.funSplitAt i Y).symm (y, ry)) i)
                  (as i) (bs i) *
                  S.correlation ((Equiv.funSplitAt i X).symm (x, rx))
                    ((Equiv.funSplitAt i Y).symm (y, ry)) as bs) := by
          rw [Fintype.sum_prod_type
            (f := fun ω : ({j : Fin n // j ≠ i} → X) ×
              ({j : Fin n // j ≠ i} → Y) => ∑ x : X, ∑ y : Y,
              (∏ j : {j : Fin n // j ≠ i},
                G.questionWeight (ω.1 j) (ω.2 j)) *
                G.questionWeight x y *
                ∑ as : Fin n → A, ∑ bs : Fin n → B,
                  G.payoff x y (as i) (bs i) *
                    S.correlation ((Equiv.funSplitAt i X).symm (x, ω.1))
                      ((Equiv.funSplitAt i Y).symm (y, ω.2)) as bs)]
          refine Finset.sum_congr rfl fun rx _ =>
            Finset.sum_congr rfl fun ry _ => Finset.sum_congr rfl
            fun x _ => Finset.sum_congr rfl fun y _ => ?_
          congr 1
      _ = ∑ w : Fin n → X, ∑ v : Fin n → Y,
            (∏ j : Fin n, G.questionWeight (w j) (v j)) *
              ∑ as : Fin n → A, ∑ bs : Fin n → B,
                G.payoff (w i) (v i) (as i) (bs i) *
                  S.correlation w v as bs :=
          presample_change_of_variables i G
            (fun w v => ∑ as : Fin n → A, ∑ bs : Fin n → B,
              G.payoff (w i) (v i) (as i) (bs i) *
                S.correlation w v as bs)
  rw [hScwin]
  -- The repeated win is dominated termwise: ∏ V ≤ V_i on [0,1] payoffs.
  have hLHS : (G.«repeat» n).win S.correlation
      = ∑ w : Fin n → X, ∑ v : Fin n → Y,
          ∑ as : Fin n → A, ∑ bs : Fin n → B,
            (∏ j : Fin n, G.questionWeight (w j) (v j)) *
              (∏ j : Fin n, G.payoff (w j) (v j) (as j) (bs j)) *
              S.correlation w v as bs := rfl
  rw [hLHS]
  refine Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun v _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun as _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun bs _ => ?_
  have hprod : (∏ j : Fin n, G.payoff (w j) (v j) (as j) (bs j))
      ≤ G.payoff (w i) (v i) (as i) (bs i) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    calc G.payoff (w i) (v i) (as i) (bs i) *
          ∏ j ∈ Finset.univ.erase i, G.payoff (w j) (v j) (as j) (bs j)
        ≤ G.payoff (w i) (v i) (as i) (bs i) * 1 :=
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_one
              (fun j _ => G.payoff_nonneg _ _ _ _)
              (fun j _ => G.payoff_le_one _ _ _ _))
            (G.payoff_nonneg _ _ _ _)
      _ = G.payoff (w i) (v i) (as i) (bs i) := mul_one _
  have hμ0 : 0 ≤ ∏ j : Fin n, G.questionWeight (w j) (v j) :=
    Finset.prod_nonneg fun j _ => G.weight_nonneg _ _
  have hc0 := S.correlation_nonneg w v as bs
  calc (∏ j : Fin n, G.questionWeight (w j) (v j)) *
        (∏ j : Fin n, G.payoff (w j) (v j) (as j) (bs j)) *
        S.correlation w v as bs
      ≤ (∏ j : Fin n, G.questionWeight (w j) (v j)) *
          G.payoff (w i) (v i) (as i) (bs i) *
          S.correlation w v as bs := by
        refine mul_le_mul_of_nonneg_right ?_ hc0
        exact mul_le_mul_of_nonneg_left hprod hμ0
    _ = (∏ j : Fin n, G.questionWeight (w j) (v j)) *
          (G.payoff (w i) (v i) (as i) (bs i) *
            S.correlation w v as bs) := by ring


/-- Payoff perturbation for the winning functional (node 1.6.3;
07_main_theorem.tex, eq payoff-rational-approximation, first inequality):
two games with the same question law and `δ`-close payoff tables give
winning probabilities within `δ`, for any subnormalized nonnegative
correlation. (`hδ` is needed for degenerate empty alphabets, where the
payoff hypothesis is vacuous and both wins are zero.) -/
theorem abs_win_sub_win_le {G₁ G₂ : Game X Y A B} {δ : ℝ} (hδ : 0 ≤ δ)
    (hμ : G₁.questionWeight = G₂.questionWeight)
    (hV : ∀ x y a b, |G₁.payoff x y a b - G₂.payoff x y a b| ≤ δ)
    {p : Correlation X Y A B}
    (hp : ∀ x y a b, 0 ≤ p x y a b)
    (hsum : ∀ x y, (∑ a : A, ∑ b : B, p x y a b) ≤ 1) :
    |G₁.win p - G₂.win p| ≤ δ := by
  have hterm : ∀ x y a b,
      |G₁.questionWeight x y * G₁.payoff x y a b * p x y a b -
        G₂.questionWeight x y * G₂.payoff x y a b * p x y a b|
      ≤ G₁.questionWeight x y * p x y a b * δ := by
    intro x y a b
    rw [← hμ]
    have h1 : G₁.questionWeight x y * G₁.payoff x y a b * p x y a b -
        G₁.questionWeight x y * G₂.payoff x y a b * p x y a b
        = G₁.questionWeight x y * p x y a b *
          (G₁.payoff x y a b - G₂.payoff x y a b) := by ring
    rw [h1, abs_mul,
      abs_of_nonneg (mul_nonneg (G₁.weight_nonneg x y) (hp x y a b))]
    exact mul_le_mul_of_nonneg_left (hV x y a b)
      (mul_nonneg (G₁.weight_nonneg x y) (hp x y a b))
  calc |G₁.win p - G₂.win p|
      = |∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
          (G₁.questionWeight x y * G₁.payoff x y a b * p x y a b -
           G₂.questionWeight x y * G₂.payoff x y a b * p x y a b)| := by
        simp only [Game.win, Finset.sum_sub_distrib]
    _ ≤ ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
          |G₁.questionWeight x y * G₁.payoff x y a b * p x y a b -
           G₂.questionWeight x y * G₂.payoff x y a b * p x y a b| :=
        abs_sum4_le _
    _ ≤ ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
          G₁.questionWeight x y * p x y a b * δ :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
            hterm x y a b
    _ = ∑ x : X, ∑ y : Y, G₁.questionWeight x y *
          (∑ a : A, ∑ b : B, p x y a b) * δ := by
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro y _
        simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ x : X, ∑ y : Y, G₁.questionWeight x y * 1 * δ := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hsum x y) (G₁.weight_nonneg x y)) hδ
    _ = δ := by
        calc (∑ x : X, ∑ y : Y, G₁.questionWeight x y * 1 * δ)
            = ∑ x : X, (∑ y : Y, G₁.questionWeight x y) * δ :=
              Finset.sum_congr rfl fun x _ => by
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun y _ => by ring
          _ = (∑ x : X, ∑ y : Y, G₁.questionWeight x y) * δ := by
              rw [Finset.sum_mul]
          _ = 1 * δ := by rw [G₁.weight_normalized]
          _ = δ := one_mul δ

/-- Payoff perturbation for the commuting value (node 1.6.3): `δ`-close
payoff tables give `δ`-close values. ["The same bounds hold after taking
commuting suprema", 07_main_theorem.tex] -/
theorem abs_omegaCO_sub_omegaCO_le [Nonempty A] [Nonempty B]
    {G₁ G₂ : Game X Y A B} {δ : ℝ} (hδ : 0 ≤ δ)
    (hμ : G₁.questionWeight = G₂.questionWeight)
    (hV : ∀ x y a b, |G₁.payoff x y a b - G₂.payoff x y a b| ≤ δ) :
    |G₁.omegaCO - G₂.omegaCO| ≤ δ := by
  have key : ∀ (Ga Gb : Game X Y A B),
      Ga.questionWeight = Gb.questionWeight →
      (∀ x y a b, |Ga.payoff x y a b - Gb.payoff x y a b| ≤ δ) →
      Ga.omegaCO ≤ Gb.omegaCO + δ := by
    intro Ga Gb hμ' hV'
    have hne : (Set.range fun S : CommutingStrategy.{0} X Y A B =>
        Ga.win S.correlation).Nonempty :=
      ⟨_, ⟨CommutingStrategy.trivial (X := X) (Y := Y), rfl⟩⟩
    refine csSup_le hne ?_
    rintro _ ⟨S, rfl⟩
    have hb := abs_win_sub_win_le (G₁ := Ga) (G₂ := Gb) hδ hμ' hV'
      (p := S.correlation)
      (fun x y a b => S.correlation_nonneg x y a b)
      (fun x y => (S.correlation_sum x y).le)
    have h2 := Gb.le_omegaCO S
    have h3 := (abs_le.mp hb).2
    linarith
  have h12 := key G₁ G₂ hμ hV
  have h21 := key G₂ G₁ hμ.symm
    (fun x y a b => by rw [abs_sub_comm]; exact hV x y a b)
  rw [abs_le]
  constructor <;> linarith

/-- Repeated-game payoff perturbation (node 1.6.3; 07_main_theorem.tex, eq
payoff-rational-approximation, second inequality, "telescoping the
product"): `δ`-close payoff tables give `n·δ`-close repeated values. -/
theorem abs_repeat_omegaCO_sub_le [Nonempty A] [Nonempty B]
    {G₁ G₂ : Game X Y A B} {δ : ℝ} (hδ : 0 ≤ δ)
    (hμ : G₁.questionWeight = G₂.questionWeight)
    (hV : ∀ x y a b, |G₁.payoff x y a b - G₂.payoff x y a b| ≤ δ)
    (n : ℕ) :
    |(G₁.«repeat» n).omegaCO - (G₂.«repeat» n).omegaCO| ≤ (n : ℝ) * δ := by
  have hμn : (G₁.«repeat» n).questionWeight
      = (G₂.«repeat» n).questionWeight := by
    funext xs ys
    simp only [Game.repeat, hμ]
  have hVn : ∀ xs ys as bs,
      |(G₁.«repeat» n).payoff xs ys as bs -
        (G₂.«repeat» n).payoff xs ys as bs| ≤ (n : ℝ) * δ := by
    intro xs ys as bs
    show |(∏ i : Fin n, G₁.payoff (xs i) (ys i) (as i) (bs i)) -
      ∏ i : Fin n, G₂.payoff (xs i) (ys i) (as i) (bs i)| ≤ (n : ℝ) * δ
    calc |(∏ i : Fin n, G₁.payoff (xs i) (ys i) (as i) (bs i)) -
        ∏ i : Fin n, G₂.payoff (xs i) (ys i) (as i) (bs i)|
        ≤ ∑ i : Fin n, |G₁.payoff (xs i) (ys i) (as i) (bs i) -
            G₂.payoff (xs i) (ys i) (as i) (bs i)| :=
          abs_prod_sub_prod_le Finset.univ _ _
            (fun i _ => G₁.payoff_nonneg _ _ _ _)
            (fun i _ => G₁.payoff_le_one _ _ _ _)
            (fun i _ => G₂.payoff_nonneg _ _ _ _)
            (fun i _ => G₂.payoff_le_one _ _ _ _)
      _ ≤ ∑ _i : Fin n, δ :=
          Finset.sum_le_sum fun i _ => hV _ _ _ _
      _ = (n : ℝ) * δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  exact abs_omegaCO_sub_omegaCO_le (mul_nonneg (Nat.cast_nonneg n) hδ)
    hμn hVn

end Game

end CommutingRepetition
