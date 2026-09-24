/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.POVMMix

/-!
# The disagreement of two parties' measurements

The probability `dis ψ M N = 1 - ∑_a ⟨ψ| M_a ⊗ N_a |ψ⟩` that Alice's POVM `M` and Bob's `N`,
measured on `ψ`, return different outcomes, and four facts about it that the soundness of answer
reduction uses throughout:

* it only decreases under a common coarse-graining (`dis_map_le`);
* disagreements chain across the two parties, linearly (`sum_dis_triangle`, from
  `agreeSum_triangle`): Alice's `A` against Bob's `D` through Bob's `B` and Alice's `C`;
* the probability of an event under Alice's measurement is at most its probability under Bob's,
  plus their disagreement (`sum_ite_bornProb_one_le`): no square root is lost, and the two
  measurements need not be projective;
* a subtest whose acceptance forces the agreement of two readings of the answers bounds their
  disagreement by its conditional failure, and a subtest whose acceptance excludes an event bounds
  that event's probability by it (`sum_ite_bornProb_le_condFail`).
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker

variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]

/-- **The disagreement** of Alice's POVM `M` and Bob's POVM `N` on the state `ψ`: the probability
that their outcomes differ. -/
def dis (ψ : dA × dB → ℂ) (M : POVM Λ dA) (N : POVM Λ dB) : ℝ :=
  1 - ∑ a, bornProb ψ ((M.mats a).val) ((N.mats a).val)

theorem bornProb_one_right (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) (N : POVM Λ dB) :
    bornProb ψ EA (1 : Matrix dB dB ℂ) = ∑ b, bornProb ψ EA ((N.mats b).val) := by
  rw [← POVM.sum_val N, bornProb_sum_right]

theorem bornProb_one_left (ψ : dA × dB → ℂ) (M : POVM Λ dA) (EB : Matrix dB dB ℂ) :
    bornProb ψ (1 : Matrix dA dA ℂ) EB = ∑ a, bornProb ψ ((M.mats a).val) EB := by
  rw [← POVM.sum_val M, bornProb_sum_left]

theorem sum_bornProb_diag_le {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : POVM Λ dA)
    (N : POVM Λ dB) : ∑ a, bornProb ψ ((M.mats a).val) ((N.mats a).val) ≤ 1 := by
  rw [← sum_bornProb hψ M N]
  exact Finset.sum_le_sum fun a _ => Finset.single_le_sum
    (f := fun b => bornProb ψ ((M.mats a).val) ((N.mats b).val))
    (fun b _ => bornProb_nonneg ψ (M.posSemidef a) (N.posSemidef b)) (Finset.mem_univ a)

theorem dis_nonneg {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : POVM Λ dA) (N : POVM Λ dB) :
    0 ≤ dis ψ M N :=
  sub_nonneg.mpr (sum_bornProb_diag_le hψ M N)

/-- **Data processing**: a common coarse-graining can only decrease the disagreement. -/
theorem dis_map_le {C : Type*} [Fintype C] [DecidableEq C] (ψ : dA × dB → ℂ) (M : POVM Λ dA)
    (N : POVM Λ dB) (f : Λ → C) : dis ψ (M.map f) (N.map f) ≤ dis ψ M N := by
  classical
  unfold dis
  have h := sum_bornProb_map (ψ := ψ) (MA := fun _ : Unit => M) (MB := fun _ : Unit => N)
    (x := ()) (y := ()) f f
  rw [h]
  have : ∑ a, bornProb ψ ((M.mats a).val) ((N.mats a).val)
      ≤ ∑ a, ∑ b, (if f a = f b then (1 : ℝ) else 0)
          * bornProb ψ ((M.mats a).val) ((N.mats b).val) := by
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), if_pos rfl, one_mul]
    have : 0 ≤ ∑ b ∈ Finset.univ.erase a, (if f a = f b then (1 : ℝ) else 0)
        * bornProb ψ ((M.mats a).val) ((N.mats b).val) :=
      Finset.sum_nonneg fun b _ => mul_nonneg (by split_ifs <;> norm_num)
        (bornProb_nonneg ψ (M.posSemidef a) (N.posSemidef b))
    linarith
  linarith

/-- The disagreement is the sum of the off-diagonal Born probabilities. -/
theorem dis_eq_sum_ne {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) [DecidableEq Λ] (M : POVM Λ dA)
    (N : POVM Λ dB) :
    dis ψ M N = ∑ a, ∑ b, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val) := by
  have h1 := sum_bornProb hψ M N
  have hsplit : ∀ a, ∑ b, bornProb ψ ((M.mats a).val) ((N.mats b).val)
      = bornProb ψ ((M.mats a).val) ((N.mats a).val)
        + ∑ b, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val) := by
    intro a
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _
      (Finset.mem_univ a), if_pos rfl, zero_add]
    congr 1
    exact Finset.sum_congr rfl fun b hb => by rw [if_neg (Finset.ne_of_mem_erase hb).symm]
  simp only [hsplit, Finset.sum_add_distrib] at h1
  unfold dis
  linarith

/-- **An event transfers across the parties**: its probability under Alice's measurement is at
most its probability under Bob's plus their disagreement. -/
theorem sum_ite_bornProb_one_le {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) [DecidableEq Λ]
    (M : POVM Λ dA) (N : POVM Λ dB) (E : Λ → Prop) [DecidablePred E] :
    ∑ a, (if E a then bornProb ψ ((M.mats a).val) (1 : Matrix dB dB ℂ) else 0)
      ≤ ∑ b, (if E b then bornProb ψ (1 : Matrix dA dA ℂ) ((N.mats b).val) else 0)
        + dis ψ M N := by
  have h0 : ∀ a b, 0 ≤ bornProb ψ ((M.mats a).val) ((N.mats b).val) := fun a b =>
    bornProb_nonneg ψ (M.posSemidef a) (N.posSemidef b)
  rw [dis_eq_sum_ne hψ]
  -- Alice's side: the diagonal plus the off-diagonal
  have hA : ∀ a, (if E a then bornProb ψ ((M.mats a).val) (1 : Matrix dB dB ℂ) else 0)
      ≤ (if E a then bornProb ψ ((M.mats a).val) ((N.mats a).val) else 0)
        + ∑ b, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val) := by
    intro a
    rw [bornProb_one_right ψ _ N]
    have hsplit : ∑ b, bornProb ψ ((M.mats a).val) ((N.mats b).val)
        = bornProb ψ ((M.mats a).val) ((N.mats a).val)
          + ∑ b, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _
        (Finset.mem_univ a), if_pos rfl, zero_add]
      congr 1
      exact Finset.sum_congr rfl fun b hb => by rw [if_neg (Finset.ne_of_mem_erase hb).symm]
    have hoff : 0 ≤ ∑ b, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val) :=
      Finset.sum_nonneg fun b _ => by split_ifs <;> simp [h0 a b]
    split_ifs
    · rw [hsplit]
    · linarith
  -- Bob's side: the diagonal is at most Bob's marginal
  have hB : ∀ a, (if E a then bornProb ψ ((M.mats a).val) ((N.mats a).val) else 0)
      ≤ (if E a then bornProb ψ (1 : Matrix dA dA ℂ) ((N.mats a).val) else 0) := by
    intro a
    split_ifs
    · rw [bornProb_one_left ψ M]
      exact Finset.single_le_sum (f := fun a' => bornProb ψ ((M.mats a').val) ((N.mats a).val))
        (fun a' _ => h0 a' a) (Finset.mem_univ a)
    · exact le_rfl
  calc ∑ a, (if E a then bornProb ψ ((M.mats a).val) (1 : Matrix dB dB ℂ) else 0)
      ≤ ∑ a, ((if E a then bornProb ψ ((M.mats a).val) ((N.mats a).val) else 0)
        + ∑ b, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val)) :=
        Finset.sum_le_sum fun a _ => hA a
    _ ≤ ∑ a, ((if E a then bornProb ψ (1 : Matrix dA dA ℂ) ((N.mats a).val) else 0)
        + ∑ b, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val)) :=
        Finset.sum_le_sum fun a _ => by linarith [hB a]
    _ = _ := Finset.sum_add_distrib

/-- The mirror image: an event transfers from Bob's measurement to Alice's. -/
theorem sum_ite_bornProb_one_le' {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) [DecidableEq Λ]
    (M : POVM Λ dA) (N : POVM Λ dB) (E : Λ → Prop) [DecidablePred E] :
    ∑ b, (if E b then bornProb ψ (1 : Matrix dA dA ℂ) ((N.mats b).val) else 0)
      ≤ ∑ a, (if E a then bornProb ψ ((M.mats a).val) (1 : Matrix dB dB ℂ) else 0)
        + dis ψ M N := by
  have h0 : ∀ a b, 0 ≤ bornProb ψ ((M.mats a).val) ((N.mats b).val) := fun a b =>
    bornProb_nonneg ψ (M.posSemidef a) (N.posSemidef b)
  rw [dis_eq_sum_ne hψ]
  have hB : ∀ b, (if E b then bornProb ψ (1 : Matrix dA dA ℂ) ((N.mats b).val) else 0)
      ≤ (if E b then bornProb ψ ((M.mats b).val) ((N.mats b).val) else 0)
        + ∑ a, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val) := by
    intro b
    rw [bornProb_one_left ψ M]
    have hsplit : ∑ a, bornProb ψ ((M.mats a).val) ((N.mats b).val)
        = bornProb ψ ((M.mats b).val) ((N.mats b).val)
          + ∑ a, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), ← Finset.add_sum_erase _ _
        (Finset.mem_univ b), if_pos rfl, zero_add]
      congr 1
      exact Finset.sum_congr rfl fun a ha => by rw [if_neg (Finset.ne_of_mem_erase ha)]
    have hoff : 0 ≤ ∑ a, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val) :=
      Finset.sum_nonneg fun a _ => by split_ifs <;> simp [h0 a b]
    split_ifs
    · rw [hsplit]
    · linarith
  have hA : ∀ b, (if E b then bornProb ψ ((M.mats b).val) ((N.mats b).val) else 0)
      ≤ (if E b then bornProb ψ ((M.mats b).val) (1 : Matrix dB dB ℂ) else 0) := by
    intro b
    split_ifs
    · rw [bornProb_one_right ψ _ N]
      exact Finset.single_le_sum (f := fun b' => bornProb ψ ((M.mats b).val) ((N.mats b').val))
        (fun b' _ => h0 b b') (Finset.mem_univ b)
    · exact le_rfl
  have hoffsum : ∑ b, ∑ a, (if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val))
      = ∑ a, ∑ b, (if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val)) :=
    Finset.sum_comm
  calc ∑ b, (if E b then bornProb ψ (1 : Matrix dA dA ℂ) ((N.mats b).val) else 0)
      ≤ ∑ b, ((if E b then bornProb ψ ((M.mats b).val) ((N.mats b).val) else 0)
        + ∑ a, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val)) :=
        Finset.sum_le_sum fun b _ => hB b
    _ ≤ ∑ b, ((if E b then bornProb ψ ((M.mats b).val) (1 : Matrix dB dB ℂ) else 0)
        + ∑ a, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val)) :=
        Finset.sum_le_sum fun b _ => by linarith [hA b]
    _ = _ := by rw [Finset.sum_add_distrib, hoffsum]

/-- **From evaluations to outcomes**: when distinct outcomes are separated by an evaluation map at
a point drawn from `ν`, colliding with probability at most `ε`, the disagreement of the outcomes is
at most the average disagreement of the evaluations, plus `ε`. Neither measurement need be
projective. -/
theorem dis_le_sum_dis_map_add {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) [DecidableEq Λ]
    (M : POVM Λ dA) (N : POVM Λ dB) {Y R : Type*} [Fintype Y] [Fintype R] [DecidableEq R]
    {ν : Y → ℝ} (hν0 : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (ev : Y → Λ → R) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsep : ∀ g g', g ≠ g' → ∑ y, ν y * (if ev y g = ev y g' then 1 else 0) ≤ ε) :
    dis ψ M N ≤ ∑ y, ν y * dis ψ (M.map (ev y)) (N.map (ev y)) + ε := by
  classical
  set β : Λ → Λ → ℝ := fun a b => bornProb ψ ((M.mats a).val) ((N.mats b).val) with hβ
  have hβ0 : ∀ a b, 0 ≤ β a b := fun a b => bornProb_nonneg ψ (M.posSemidef a) (N.posSemidef b)
  have hβ1 : ∑ a, ∑ b, β a b = 1 := sum_bornProb hψ M N
  -- the evaluated disagreement at one point
  have hy : ∀ y, dis ψ (M.map (ev y)) (N.map (ev y))
      = ∑ a, ∑ b, (if ev y a = ev y b then 0 else 1) * β a b := by
    intro y
    unfold dis
    have h := sum_bornProb_map (ψ := ψ) (MA := fun _ : Unit => M) (MB := fun _ : Unit => N)
      (x := ()) (y := ()) (ev y) (ev y)
    rw [h]
    have hsplit : ∀ a b, (if ev y a = ev y b then (0 : ℝ) else 1) * β a b
        = β a b - (if ev y a = ev y b then 1 else 0) * β a b := fun a b => by
      split_ifs <;> ring
    simp only [hsplit, Finset.sum_sub_distrib, hβ1]
    rfl
  -- the disagreement of the outcomes
  have hd : dis ψ M N = ∑ a, ∑ b, (if a = b then 0 else 1) * β a b := by
    rw [dis_eq_sum_ne hψ]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp [hβ]
  -- averaging over the point
  have havg : ∑ y, ν y * dis ψ (M.map (ev y)) (N.map (ev y))
      = ∑ a, ∑ b, (∑ y, ν y * (if ev y a = ev y b then 0 else 1)) * β a b := by
    simp only [hy, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hcoef : ∀ a b, (if a = b then (0 : ℝ) else 1) * (1 - ε)
      ≤ ∑ y, ν y * (if ev y a = ev y b then 0 else 1) := by
    intro a b
    by_cases h : a = b
    · rw [if_pos h, zero_mul]
      exact Finset.sum_nonneg fun y _ => mul_nonneg (hν0 y) (by split_ifs <;> norm_num)
    · rw [if_neg h, one_mul]
      have hs := hsep a b h
      have hc : ∑ y, ν y * (if ev y a = ev y b then (0 : ℝ) else 1)
          = ∑ y, ν y - ∑ y, ν y * (if ev y a = ev y b then 1 else 0) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ => by split_ifs <;> ring
      rw [hν1] at hc
      linarith
  have hlow : (1 - ε) * dis ψ M N ≤ ∑ y, ν y * dis ψ (M.map (ev y)) (N.map (ev y)) := by
    rw [havg, hd, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have := mul_le_mul_of_nonneg_right (hcoef a b) (hβ0 a b)
    linarith
  have hd1 : dis ψ M N ≤ 1 := by
    have := sum_bornProb_diag_le hψ M N
    have h0 : 0 ≤ ∑ a, bornProb ψ ((M.mats a).val) ((N.mats a).val) :=
      Finset.sum_nonneg fun a _ => hβ0 a a
    unfold dis
    linarith
  nlinarith [dis_nonneg hψ M N]

/-! ## Families on a uniform index -/

section Uniform

variable {X : Type*} [Fintype X] [Nonempty X]

theorem one_sub_agreeSum_uniform (ψ : dA × dB → ℂ) (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    1 - agreeSum (uniform X) ψ M N = (∑ x, dis ψ (M x) (N x)) / Fintype.card X := by
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  unfold agreeSum dis uniform
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, sub_div, div_self hc.ne', inv_mul_eq_div]

/-- **The disagreement triangle** across the two parties, on a uniform index: Alice's `A` against
Bob's `D`, through Bob's `B` and Alice's `C`. -/
theorem sum_dis_triangle {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (A C : X → POVM Λ dA)
    (B D : X → POVM Λ dB) :
    ∑ x, dis ψ (A x) (D x)
      ≤ 11 * (∑ x, dis ψ (A x) (B x) + ∑ x, dis ψ (C x) (B x) + ∑ x, dis ψ (C x) (D x)) := by
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hμ0 : ∀ x, 0 ≤ uniform X x := fun x => by simp [uniform]
  have hμ1 : ∑ x, uniform X x = 1 := by
    simp [uniform, Finset.card_univ]
  set δ := (∑ x, dis ψ (A x) (B x) + ∑ x, dis ψ (C x) (B x) + ∑ x, dis ψ (C x) (D x))
    / Fintype.card X
  have h1 := Finset.sum_nonneg fun x (_ : x ∈ univ) => dis_nonneg hψ (A x) (B x)
  have h2 := Finset.sum_nonneg fun x (_ : x ∈ univ) => dis_nonneg hψ (C x) (B x)
  have h3 := Finset.sum_nonneg fun x (_ : x ∈ univ) => dis_nonneg hψ (C x) (D x)
  have hAB : 1 - agreeSum (uniform X) ψ A B ≤ δ := by
    rw [one_sub_agreeSum_uniform]; exact div_le_div_of_nonneg_right (by linarith) hc.le
  have hCB : 1 - agreeSum (uniform X) ψ C B ≤ δ := by
    rw [one_sub_agreeSum_uniform]; exact div_le_div_of_nonneg_right (by linarith) hc.le
  have hCD : 1 - agreeSum (uniform X) ψ C D ≤ δ := by
    rw [one_sub_agreeSum_uniform]; exact div_le_div_of_nonneg_right (by linarith) hc.le
  have h := agreeSum_triangle hμ0 hμ1 hψ A C B D hAB hCB hCD
  rw [one_sub_agreeSum_uniform, div_le_iff₀ hc] at h
  simp only [δ] at h
  rw [mul_div_assoc', div_mul_cancel₀ _ hc.ne'] at h
  exact h

end Uniform

/-! ## Subtests -/

section Subtests

variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}

/-- **An agreement subtest bounds the disagreement of the two readings.** -/
theorem dis_map_le_condFail {x : X} {y : Y} (f : A → C) (g : B → C)
    (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    dis ψ ((MA x).map f) ((MB y).map g) ≤ condFail G ψ MA MB x y :=
  one_sub_sum_bornProb_le_condFail f g hD

/-- **A subtest excluding an event of Bob's answer bounds its probability.** -/
theorem sum_ite_bornProb_le_condFail (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (E : B → Prop)
    [DecidablePred E] (hD : ∀ a b, G.D x y a b = true → ¬ E b) :
    ∑ b, (if E b then bornProb ψ (1 : Matrix dA dA ℂ) (((MB y).mats b).val) else 0)
      ≤ condFail G ψ MA MB x y := by
  have h0 : ∀ a b, 0 ≤ bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := fun a b =>
    bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b)
  have htot := sum_bornProb hψ (MA x) (MB y)
  unfold condFail condWin
  have hle : ∑ a, ∑ b, (if G.D x y a b then (1 : ℝ) else 0)
        * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val)
      + ∑ b, (if E b then bornProb ψ (1 : Matrix dA dA ℂ) (((MB y).mats b).val) else 0)
      ≤ ∑ a, ∑ b, bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
    have hE : ∑ b, (if E b then bornProb ψ (1 : Matrix dA dA ℂ) (((MB y).mats b).val) else 0)
        = ∑ a, ∑ b, (if E b then bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val)
          else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · exact bornProb_one_left ψ (MA x) _
      · simp
    rw [hE, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun b _ => ?_
    by_cases hd : G.D x y a b = true
    · have := hD a b hd
      simp [hd, this]
    · have : (if G.D x y a b = true then (1 : ℝ) else 0) = 0 := by simp [hd]
      rw [this, zero_mul, zero_add]
      split_ifs <;> simp [h0 a b]
  linarith

/-- The mirror image, for an event of Alice's answer. -/
theorem sum_ite_bornProb_le_condFail' (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (E : A → Prop)
    [DecidablePred E] (hD : ∀ a b, G.D x y a b = true → ¬ E a) :
    ∑ a, (if E a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
      ≤ condFail G ψ MA MB x y := by
  have h0 : ∀ a b, 0 ≤ bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := fun a b =>
    bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b)
  have htot := sum_bornProb hψ (MA x) (MB y)
  unfold condFail condWin
  have hle : ∑ a, ∑ b, (if G.D x y a b then (1 : ℝ) else 0)
        * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val)
      + ∑ a, (if E a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
      ≤ ∑ a, ∑ b, bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    have hE : (if E a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
        = ∑ b, (if E a then bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) else 0) := by
      split_ifs
      · exact bornProb_one_right ψ _ (MB y)
      · simp
    rw [hE, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun b _ => ?_
    by_cases hd : G.D x y a b = true
    · have := hD a b hd
      simp [hd, this]
    · have : (if G.D x y a b = true then (1 : ℝ) else 0) = 0 := by simp [hd]
      rw [this, zero_mul, zero_add]
      split_ifs <;> simp [h0 a b]
  linarith

/-- The disagreement of two readings is the weight of the outcome pairs they read differently. -/
theorem dis_map_eq_sum {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : POVM A dA) (N : POVM B dB)
    (f : A → C) (g : B → C) :
    dis ψ (M.map f) (N.map g) = ∑ a, ∑ b, (if f a = g b then 0 else 1)
      * bornProb ψ ((M.mats a).val) ((N.mats b).val) := by
  unfold dis
  have h := sum_bornProb_map (ψ := ψ) (MA := fun _ : Unit => M) (MB := fun _ : Unit => N)
    (x := ()) (y := ()) f g
  rw [h]
  have h1 := sum_bornProb hψ M N
  have hsplit : ∀ a b, (if f a = g b then (0 : ℝ) else 1)
      * bornProb ψ ((M.mats a).val) ((N.mats b).val)
      = bornProb ψ ((M.mats a).val) ((N.mats b).val)
        - (if f a = g b then 1 else 0) * bornProb ψ ((M.mats a).val) ((N.mats b).val) :=
    fun a b => by split_ifs <;> ring
  simp only [hsplit, Finset.sum_sub_distrib, h1]

/-- **A subtest accepting when two events are avoided and two readings agree** fails at most the
events' probabilities plus the readings' disagreement. -/
theorem condFail_le_of (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (EA : A → Prop) (EB : B → Prop)
    [DecidablePred EA] [DecidablePred EB] (f : A → C) (g : B → C)
    (hD : ∀ a b, ¬ EA a → ¬ EB b → f a = g b → G.D x y a b = true) :
    condFail G ψ MA MB x y
      ≤ ∑ a, (if EA a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
        + ∑ b, (if EB b then bornProb ψ (1 : Matrix dA dA ℂ) (((MB y).mats b).val) else 0)
        + dis ψ ((MA x).map f) ((MB y).map g) := by
  have hβ0 : ∀ a b, 0 ≤ bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := fun a b =>
    bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b)
  have htot := sum_bornProb hψ (MA x) (MB y)
  have hfail : condFail G ψ MA MB x y
      = ∑ a, ∑ b, (if G.D x y a b then 0 else 1)
        * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
    have hsum : ∑ a, ∑ b, (if G.D x y a b then (0 : ℝ) else 1)
          * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val)
        + condWin G ψ MA MB x y
        = ∑ a, ∑ b, bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
      unfold condWin
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
    unfold condFail
    linarith
  have hA : ∑ a, (if EA a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
      = ∑ a, ∑ b, (if EA a then 1 else 0)
        * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · simp only [one_mul]; exact bornProb_one_right ψ _ (MB y)
    · simp
  have hB : ∑ b, (if EB b then bornProb ψ (1 : Matrix dA dA ℂ) (((MB y).mats b).val) else 0)
      = ∑ a, ∑ b, (if EB b then 1 else 0)
        * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · simp only [one_mul]; exact bornProb_one_left ψ (MA x) _
    · simp
  rw [hfail, hA, hB, dis_map_eq_sum hψ, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have h0 := hβ0 a b
  by_cases hd : G.D x y a b = true
  · have e1 : 0 ≤ (if EA a then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have e2 : 0 ≤ (if EB b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have e3 : 0 ≤ (if f a = g b then (0 : ℝ) else 1) := by split_ifs <;> norm_num
    rw [if_pos hd, zero_mul]
    positivity
  · rw [if_neg hd, one_mul]
    by_cases ha : EA a
    · have e2 : 0 ≤ (if EB b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      have e3 : 0 ≤ (if f a = g b then (0 : ℝ) else 1) := by split_ifs <;> norm_num
      rw [if_pos ha, one_mul]
      nlinarith
    · by_cases hb : EB b
      · have e3 : 0 ≤ (if f a = g b then (0 : ℝ) else 1) := by split_ifs <;> norm_num
        rw [if_neg ha, if_pos hb, zero_mul, one_mul, zero_add]
        nlinarith
      · have hfg : f a ≠ g b := fun h => hd (hD a b ha hb h)
        rw [if_neg ha, if_neg hb, if_neg hfg]
        simp

end Subtests

end MIPRE

end
