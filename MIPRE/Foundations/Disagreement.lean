/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.POVMMix

@[expose] public section

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

All of it is proved once, for a bipartite model (`BipartiteModel.dis` and the lemmas after it),
and the matrix statements are the instances in the tensor-product model (`dis_eq_tensor`).
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## In a bipartite model

The disagreement and its facts, for a bipartite model with the players' POVMs in their ordered
algebras; the matrix statements below are the instances in the tensor-product model
(`dis_eq_tensor`). -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)

section Basic

variable [PartialOrder 𝒜] [PartialOrder ℬ] {Λ : Type*} [Fintype Λ]

/-- **The disagreement** of the first player's POVM `P` and the second player's `Q`: the
probability that their outcomes differ. -/
def dis (P : POVMIn Λ 𝒜) (Q : POVMIn Λ ℬ) : ℝ :=
  1 - ∑ a, M.bornProb (P.op a) (Q.op a)

omit [PartialOrder 𝒜] in
theorem bornProb_one_right (e : 𝒜) (Q : POVMIn Λ ℬ) :
    M.bornProb e 1 = ∑ b, M.bornProb e (Q.op b) := by
  rw [← Q.sum_op, M.bornProb_sum_right]

omit [PartialOrder ℬ] in
theorem bornProb_one_left (P : POVMIn Λ 𝒜) (f : ℬ) :
    M.bornProb 1 f = ∑ a, M.bornProb (P.op a) f := by
  rw [← P.sum_op, M.bornProb_sum_left]

end Basic

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  {Λ : Type*} [Fintype Λ]

theorem sum_bornProb_diag_le (hψ : ‖M.ψ‖ = 1) (P : POVMIn Λ 𝒜) (Q : POVMIn Λ ℬ) :
    ∑ a, M.bornProb (P.op a) (Q.op a) ≤ 1 := by
  rw [← M.sum_bornProb hψ P Q]
  exact Finset.sum_le_sum fun a _ => Finset.single_le_sum
    (f := fun b => M.bornProb (P.op a) (Q.op b))
    (fun b _ => M.bornProb_nonneg (P.op_nonneg a) (Q.op_nonneg b)) (Finset.mem_univ a)

theorem dis_nonneg (hψ : ‖M.ψ‖ = 1) (P : POVMIn Λ 𝒜) (Q : POVMIn Λ ℬ) : 0 ≤ M.dis P Q :=
  sub_nonneg.mpr (M.sum_bornProb_diag_le hψ P Q)

/-- **Data processing**: a common coarse-graining can only decrease the disagreement. -/
theorem dis_map_le {C : Type*} [Fintype C] [DecidableEq C] (P : POVMIn Λ 𝒜) (Q : POVMIn Λ ℬ)
    (f : Λ → C) : M.dis (P.map f) (Q.map f) ≤ M.dis P Q := by
  classical
  unfold dis
  rw [M.sum_bornProb_map P Q f f]
  have : ∑ a, M.bornProb (P.op a) (Q.op a)
      ≤ ∑ a, ∑ b, (if f a = f b then (1 : ℝ) else 0) * M.bornProb (P.op a) (Q.op b) := by
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ite_eq_left rfl, one_mul]
    have : 0 ≤ ∑ b ∈ Finset.univ.erase a, (if f a = f b then (1 : ℝ) else 0)
        * M.bornProb (P.op a) (Q.op b) :=
      Finset.sum_nonneg fun b _ => mul_nonneg (by split_ifs <;> norm_num)
        (M.bornProb_nonneg (P.op_nonneg a) (Q.op_nonneg b))
    linarith
  linarith

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- The diagonal and the off-diagonal of a row of Born probabilities. -/
private theorem row_split [DecidableEq Λ] (P : POVMIn Λ 𝒜) (Q : POVMIn Λ ℬ) (a : Λ) :
    ∑ b, M.bornProb (P.op a) (Q.op b)
      = M.bornProb (P.op a) (Q.op a)
        + ∑ b, if a = b then 0 else M.bornProb (P.op a) (Q.op b) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _
    (Finset.mem_univ a), ite_eq_left rfl, zero_add]
  congr 1
  exact Finset.sum_congr rfl fun b hb => by rw [ite_eq_right (Finset.ne_of_mem_erase hb).symm]

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- The diagonal and the off-diagonal of a column of Born probabilities. -/
private theorem col_split [DecidableEq Λ] (P : POVMIn Λ 𝒜) (Q : POVMIn Λ ℬ) (b : Λ) :
    ∑ a, M.bornProb (P.op a) (Q.op b)
      = M.bornProb (P.op b) (Q.op b)
        + ∑ a, if a = b then 0 else M.bornProb (P.op a) (Q.op b) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), ← Finset.add_sum_erase _ _
    (Finset.mem_univ b), ite_eq_left rfl, zero_add]
  congr 1
  exact Finset.sum_congr rfl fun a ha => by rw [ite_eq_right (Finset.ne_of_mem_erase ha)]

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- The disagreement is the sum of the off-diagonal Born probabilities. -/
theorem dis_eq_sum_ne (hψ : ‖M.ψ‖ = 1) [DecidableEq Λ] (P : POVMIn Λ 𝒜) (Q : POVMIn Λ ℬ) :
    M.dis P Q = ∑ a, ∑ b, if a = b then 0 else M.bornProb (P.op a) (Q.op b) := by
  have h1 := M.sum_bornProb hψ P Q
  simp only [M.row_split P Q, Finset.sum_add_distrib] at h1
  unfold dis
  linarith

/-- **An event transfers across the parties**: its probability under the first player's
measurement is at most its probability under the second player's plus their disagreement. -/
theorem sum_ite_bornProb_one_le (hψ : ‖M.ψ‖ = 1) [DecidableEq Λ] (P : POVMIn Λ 𝒜)
    (Q : POVMIn Λ ℬ) (E : Λ → Prop) [DecidablePred E] :
    ∑ a, (if E a then M.bornProb (P.op a) 1 else 0)
      ≤ ∑ b, (if E b then M.bornProb 1 (Q.op b) else 0) + M.dis P Q := by
  have h0 : ∀ a b, 0 ≤ M.bornProb (P.op a) (Q.op b) := fun a b =>
    M.bornProb_nonneg (P.op_nonneg a) (Q.op_nonneg b)
  rw [M.dis_eq_sum_ne hψ]
  have hA : ∀ a, (if E a then M.bornProb (P.op a) 1 else 0)
      ≤ (if E a then M.bornProb (P.op a) (Q.op a) else 0)
        + ∑ b, if a = b then 0 else M.bornProb (P.op a) (Q.op b) := by
    intro a
    rw [M.bornProb_one_right _ Q]
    have hoff : 0 ≤ ∑ b, if a = b then 0 else M.bornProb (P.op a) (Q.op b) :=
      Finset.sum_nonneg fun b _ => by split_ifs <;> simp [h0 a b]
    split_ifs
    · rw [M.row_split P Q a]
    · linarith
  have hB : ∀ a, (if E a then M.bornProb (P.op a) (Q.op a) else 0)
      ≤ (if E a then M.bornProb 1 (Q.op a) else 0) := by
    intro a
    split_ifs
    · rw [M.bornProb_one_left P]
      exact Finset.single_le_sum (f := fun a' => M.bornProb (P.op a') (Q.op a))
        (fun a' _ => h0 a' a) (Finset.mem_univ a)
    · exact le_rfl
  calc ∑ a, (if E a then M.bornProb (P.op a) 1 else 0)
      ≤ ∑ a, ((if E a then M.bornProb (P.op a) (Q.op a) else 0)
        + ∑ b, if a = b then 0 else M.bornProb (P.op a) (Q.op b)) :=
        Finset.sum_le_sum fun a _ => hA a
    _ ≤ ∑ a, ((if E a then M.bornProb 1 (Q.op a) else 0)
        + ∑ b, if a = b then 0 else M.bornProb (P.op a) (Q.op b)) :=
        Finset.sum_le_sum fun a _ => by linarith [hB a]
    _ = _ := Finset.sum_add_distrib

/-- The mirror image: an event transfers from the second player's measurement to the first's. -/
theorem sum_ite_bornProb_one_le' (hψ : ‖M.ψ‖ = 1) [DecidableEq Λ] (P : POVMIn Λ 𝒜)
    (Q : POVMIn Λ ℬ) (E : Λ → Prop) [DecidablePred E] :
    ∑ b, (if E b then M.bornProb 1 (Q.op b) else 0)
      ≤ ∑ a, (if E a then M.bornProb (P.op a) 1 else 0) + M.dis P Q := by
  have h0 : ∀ a b, 0 ≤ M.bornProb (P.op a) (Q.op b) := fun a b =>
    M.bornProb_nonneg (P.op_nonneg a) (Q.op_nonneg b)
  rw [M.dis_eq_sum_ne hψ]
  have hB : ∀ b, (if E b then M.bornProb 1 (Q.op b) else 0)
      ≤ (if E b then M.bornProb (P.op b) (Q.op b) else 0)
        + ∑ a, if a = b then 0 else M.bornProb (P.op a) (Q.op b) := by
    intro b
    rw [M.bornProb_one_left P]
    have hoff : 0 ≤ ∑ a, if a = b then 0 else M.bornProb (P.op a) (Q.op b) :=
      Finset.sum_nonneg fun a _ => by split_ifs <;> simp [h0 a b]
    split_ifs
    · rw [M.col_split P Q b]
    · linarith
  have hA : ∀ b, (if E b then M.bornProb (P.op b) (Q.op b) else 0)
      ≤ (if E b then M.bornProb (P.op b) 1 else 0) := by
    intro b
    split_ifs
    · rw [M.bornProb_one_right _ Q]
      exact Finset.single_le_sum (f := fun b' => M.bornProb (P.op b) (Q.op b'))
        (fun b' _ => h0 b b') (Finset.mem_univ b)
    · exact le_rfl
  have hoffsum : ∑ b, ∑ a, (if a = b then 0 else M.bornProb (P.op a) (Q.op b))
      = ∑ a, ∑ b, (if a = b then 0 else M.bornProb (P.op a) (Q.op b)) :=
    Finset.sum_comm
  calc ∑ b, (if E b then M.bornProb 1 (Q.op b) else 0)
      ≤ ∑ b, ((if E b then M.bornProb (P.op b) (Q.op b) else 0)
        + ∑ a, if a = b then 0 else M.bornProb (P.op a) (Q.op b)) :=
        Finset.sum_le_sum fun b _ => hB b
    _ ≤ ∑ b, ((if E b then M.bornProb (P.op b) 1 else 0)
        + ∑ a, if a = b then 0 else M.bornProb (P.op a) (Q.op b)) :=
        Finset.sum_le_sum fun b _ => by linarith [hA b]
    _ = _ := by rw [Finset.sum_add_distrib, hoffsum]

/-- The disagreement of two readings is the weight of the outcome pairs they read differently. -/
theorem dis_map_eq_sum (hψ : ‖M.ψ‖ = 1) {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq C] (P : POVMIn A 𝒜) (Q : POVMIn B ℬ) (f : A → C) (g : B → C) :
    M.dis (P.map f) (Q.map g)
      = ∑ a, ∑ b, (if f a = g b then 0 else 1) * M.bornProb (P.op a) (Q.op b) := by
  unfold dis
  rw [M.sum_bornProb_map P Q f g]
  have h1 := M.sum_bornProb hψ P Q
  have hsplit : ∀ a b, (if f a = g b then (0 : ℝ) else 1) * M.bornProb (P.op a) (Q.op b)
      = M.bornProb (P.op a) (Q.op b)
        - (if f a = g b then 1 else 0) * M.bornProb (P.op a) (Q.op b) :=
    fun a b => by split_ifs <;> ring
  simp only [hsplit, Finset.sum_sub_distrib, h1]

/-- **From evaluations to outcomes**: when distinct outcomes are separated by an evaluation map at
a point drawn from `ν`, colliding with probability at most `ε`, the disagreement of the outcomes is
at most the average disagreement of the evaluations, plus `ε`. Neither measurement need be
projective. -/
theorem dis_le_sum_dis_map_add (hψ : ‖M.ψ‖ = 1) [DecidableEq Λ] (P : POVMIn Λ 𝒜)
    (Q : POVMIn Λ ℬ) {Y R : Type*} [Fintype Y] [Fintype R] [DecidableEq R] {ν : Y → ℝ}
    (hν0 : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (ev : Y → Λ → R) {ε : ℝ} (hε : 0 ≤ ε)
    (hsep : ∀ g g', g ≠ g' → ∑ y, ν y * (if ev y g = ev y g' then 1 else 0) ≤ ε) :
    M.dis P Q ≤ ∑ y, ν y * M.dis (P.map (ev y)) (Q.map (ev y)) + ε := by
  set β : Λ → Λ → ℝ := fun a b => M.bornProb (P.op a) (Q.op b) with hβ
  have hβ0 : ∀ a b, 0 ≤ β a b := fun a b => M.bornProb_nonneg (P.op_nonneg a) (Q.op_nonneg b)
  -- the evaluated disagreement at one point
  have hy : ∀ y, M.dis (P.map (ev y)) (Q.map (ev y))
      = ∑ a, ∑ b, (if ev y a = ev y b then 0 else 1) * β a b := fun y =>
    M.dis_map_eq_sum hψ P Q (ev y) (ev y)
  -- the disagreement of the outcomes
  have hd : M.dis P Q = ∑ a, ∑ b, (if a = b then 0 else 1) * β a b := by
    rw [M.dis_eq_sum_ne hψ]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp [hβ]
  -- averaging over the point
  have havg : ∑ y, ν y * M.dis (P.map (ev y)) (Q.map (ev y))
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
    · rw [ite_eq_left h, zero_mul]
      exact Finset.sum_nonneg fun y _ => mul_nonneg (hν0 y) (by split_ifs <;> norm_num)
    · rw [ite_eq_right h, one_mul]
      have hs := hsep a b h
      have hc : ∑ y, ν y * (if ev y a = ev y b then (0 : ℝ) else 1)
          = ∑ y, ν y - ∑ y, ν y * (if ev y a = ev y b then 1 else 0) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ => by split_ifs <;> ring
      rw [hν1] at hc
      linarith
  have hlow : (1 - ε) * M.dis P Q ≤ ∑ y, ν y * M.dis (P.map (ev y)) (Q.map (ev y)) := by
    rw [havg, hd, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have := mul_le_mul_of_nonneg_right (hcoef a b) (hβ0 a b)
    linarith
  have hd1 : M.dis P Q ≤ 1 := by
    have h0 : 0 ≤ ∑ a, M.bornProb (P.op a) (Q.op a) :=
      Finset.sum_nonneg fun a _ => hβ0 a a
    unfold dis
    linarith
  nlinarith [M.dis_nonneg hψ P Q]

/-! ### Families on a uniform index -/

section Uniform

variable {X : Type*} [Fintype X] [Nonempty X]

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
theorem one_sub_agreeSum_uniform (P : X → POVMIn Λ 𝒜) (Q : X → POVMIn Λ ℬ) :
    1 - M.agreeSum (uniform X) P Q = (∑ x, M.dis (P x) (Q x)) / Fintype.card X := by
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  unfold agreeSum dis uniform
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, sub_div, div_self hc.ne', inv_mul_eq_div]

/-- **The disagreement triangle** across the two parties, on a uniform index: the first player's
`A` against the second player's `D`, through the second player's `B` and the first player's
`C`. -/
theorem sum_dis_triangle (hψ : ‖M.ψ‖ = 1) (A C : X → POVMIn Λ 𝒜) (B D : X → POVMIn Λ ℬ) :
    ∑ x, M.dis (A x) (D x)
      ≤ 11 * (∑ x, M.dis (A x) (B x) + ∑ x, M.dis (C x) (B x) + ∑ x, M.dis (C x) (D x)) := by
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hμ0 : ∀ x, 0 ≤ uniform X x := fun x => by simp [uniform]
  have hμ1 : ∑ x, uniform X x = 1 := by
    simp [uniform, Finset.card_univ]
  set δ := (∑ x, M.dis (A x) (B x) + ∑ x, M.dis (C x) (B x) + ∑ x, M.dis (C x) (D x))
    / Fintype.card X
  have h1 := Finset.sum_nonneg fun x (_ : x ∈ univ) => M.dis_nonneg hψ (A x) (B x)
  have h2 := Finset.sum_nonneg fun x (_ : x ∈ univ) => M.dis_nonneg hψ (C x) (B x)
  have h3 := Finset.sum_nonneg fun x (_ : x ∈ univ) => M.dis_nonneg hψ (C x) (D x)
  have hAB : 1 - M.agreeSum (uniform X) A B ≤ δ := by
    rw [M.one_sub_agreeSum_uniform]; exact div_le_div_of_nonneg_right (by linarith) hc.le
  have hCB : 1 - M.agreeSum (uniform X) C B ≤ δ := by
    rw [M.one_sub_agreeSum_uniform]; exact div_le_div_of_nonneg_right (by linarith) hc.le
  have hCD : 1 - M.agreeSum (uniform X) C D ≤ δ := by
    rw [M.one_sub_agreeSum_uniform]; exact div_le_div_of_nonneg_right (by linarith) hc.le
  have h := M.agreeSum_triangle hμ0 hμ1 hψ A C B D hAB hCB hCD
  rw [M.one_sub_agreeSum_uniform, div_le_iff₀ hc] at h
  simp only [δ] at h
  rw [mul_div_assoc', div_mul_cancel₀ _ hc.ne'] at h
  exact h

end Uniform

/-! ### Subtests -/

section Subtests

variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {G : Game X Y A B} {MA : X → POVMIn A 𝒜} {MB : Y → POVMIn B ℬ}

/-- **An agreement subtest bounds the disagreement of the two readings.** -/
theorem dis_map_le_condFail {x : X} {y : Y} (f : A → C) (g : B → C)
    (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    M.dis ((MA x).map f) ((MB y).map g) ≤ M.condFail G MA MB x y :=
  M.one_sub_sum_bornProb_le_condFail f g hD

omit [DecidableEq C] in
/-- **A subtest excluding an event of the second player's answer bounds its probability.** -/
theorem sum_ite_bornProb_le_condFail (hψ : ‖M.ψ‖ = 1) {x : X} {y : Y} (E : B → Prop)
    [DecidablePred E] (hD : ∀ a b, G.D x y a b = true → ¬ E b) :
    ∑ b, (if E b then M.bornProb 1 ((MB y).op b) else 0) ≤ M.condFail G MA MB x y := by
  have h0 : ∀ a b, 0 ≤ M.bornProb ((MA x).op a) ((MB y).op b) := fun a b =>
    M.bornProb_nonneg ((MA x).op_nonneg a) ((MB y).op_nonneg b)
  have htot := M.sum_bornProb hψ (MA x) (MB y)
  unfold condFail condWin
  have hle : ∑ a, ∑ b, (if G.D x y a b then (1 : ℝ) else 0) * M.bornProb ((MA x).op a) ((MB y).op b)
      + ∑ b, (if E b then M.bornProb 1 ((MB y).op b) else 0)
      ≤ ∑ a, ∑ b, M.bornProb ((MA x).op a) ((MB y).op b) := by
    have hE : ∑ b, (if E b then M.bornProb 1 ((MB y).op b) else 0)
        = ∑ a, ∑ b, (if E b then M.bornProb ((MA x).op a) ((MB y).op b) else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · exact M.bornProb_one_left (MA x) _
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

omit [DecidableEq C] in
/-- The mirror image, for an event of the first player's answer. -/
theorem sum_ite_bornProb_le_condFail' (hψ : ‖M.ψ‖ = 1) {x : X} {y : Y} (E : A → Prop)
    [DecidablePred E] (hD : ∀ a b, G.D x y a b = true → ¬ E a) :
    ∑ a, (if E a then M.bornProb ((MA x).op a) 1 else 0) ≤ M.condFail G MA MB x y := by
  have h0 : ∀ a b, 0 ≤ M.bornProb ((MA x).op a) ((MB y).op b) := fun a b =>
    M.bornProb_nonneg ((MA x).op_nonneg a) ((MB y).op_nonneg b)
  have htot := M.sum_bornProb hψ (MA x) (MB y)
  unfold condFail condWin
  have hle : ∑ a, ∑ b, (if G.D x y a b then (1 : ℝ) else 0) * M.bornProb ((MA x).op a) ((MB y).op b)
      + ∑ a, (if E a then M.bornProb ((MA x).op a) 1 else 0)
      ≤ ∑ a, ∑ b, M.bornProb ((MA x).op a) ((MB y).op b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    have hE : (if E a then M.bornProb ((MA x).op a) 1 else 0)
        = ∑ b, (if E a then M.bornProb ((MA x).op a) ((MB y).op b) else 0) := by
      split_ifs
      · exact M.bornProb_one_right _ (MB y)
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

/-- **A subtest accepting when two events are avoided and two readings agree** fails at most the
events' probabilities plus the readings' disagreement. -/
theorem condFail_le_of (hψ : ‖M.ψ‖ = 1) {x : X} {y : Y} (EA : A → Prop) (EB : B → Prop)
    [DecidablePred EA] [DecidablePred EB] (f : A → C) (g : B → C)
    (hD : ∀ a b, ¬ EA a → ¬ EB b → f a = g b → G.D x y a b = true) :
    M.condFail G MA MB x y
      ≤ ∑ a, (if EA a then M.bornProb ((MA x).op a) 1 else 0)
        + ∑ b, (if EB b then M.bornProb 1 ((MB y).op b) else 0)
        + M.dis ((MA x).map f) ((MB y).map g) := by
  have hβ0 : ∀ a b, 0 ≤ M.bornProb ((MA x).op a) ((MB y).op b) := fun a b =>
    M.bornProb_nonneg ((MA x).op_nonneg a) ((MB y).op_nonneg b)
  have htot := M.sum_bornProb hψ (MA x) (MB y)
  have hfail : M.condFail G MA MB x y
      = ∑ a, ∑ b, (if G.D x y a b then 0 else 1) * M.bornProb ((MA x).op a) ((MB y).op b) := by
    have hsum : ∑ a, ∑ b, (if G.D x y a b then (0 : ℝ) else 1)
          * M.bornProb ((MA x).op a) ((MB y).op b)
        + M.condWin G MA MB x y
        = ∑ a, ∑ b, M.bornProb ((MA x).op a) ((MB y).op b) := by
      unfold condWin
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
    unfold condFail
    linarith
  have hA : ∑ a, (if EA a then M.bornProb ((MA x).op a) 1 else 0)
      = ∑ a, ∑ b, (if EA a then 1 else 0) * M.bornProb ((MA x).op a) ((MB y).op b) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · simp only [one_mul]; exact M.bornProb_one_right _ (MB y)
    · simp
  have hB : ∑ b, (if EB b then M.bornProb 1 ((MB y).op b) else 0)
      = ∑ a, ∑ b, (if EB b then 1 else 0) * M.bornProb ((MA x).op a) ((MB y).op b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · simp only [one_mul]; exact M.bornProb_one_left (MA x) _
    · simp
  rw [hfail, hA, hB, M.dis_map_eq_sum hψ, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have h0 := hβ0 a b
  by_cases hd : G.D x y a b = true
  · have e1 : 0 ≤ (if EA a then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have e2 : 0 ≤ (if EB b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have e3 : 0 ≤ (if f a = g b then (0 : ℝ) else 1) := by split_ifs <;> norm_num
    rw [ite_eq_left hd, zero_mul]
    positivity
  · rw [ite_eq_right hd, one_mul]
    by_cases ha : EA a
    · have e2 : 0 ≤ (if EB b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      have e3 : 0 ≤ (if f a = g b then (0 : ℝ) else 1) := by split_ifs <;> norm_num
      rw [ite_eq_left ha, one_mul]
      nlinarith
    · by_cases hb : EB b
      · have e3 : 0 ≤ (if f a = g b then (0 : ℝ) else 1) := by split_ifs <;> norm_num
        rw [ite_eq_right ha, ite_eq_left hb, zero_mul, one_mul, zero_add]
        nlinarith
      · have hfg : f a ≠ g b := fun h => hd (hD a b ha hb h)
        rw [ite_eq_right ha, ite_eq_right hb, ite_eq_right hfg]
        simp

end Subtests

end BipartiteModel

variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]

/-- **The disagreement** of Alice's POVM `M` and Bob's POVM `N` on the state `ψ`: the probability
that their outcomes differ. -/
def dis (ψ : dA × dB → ℂ) (M : POVM Λ dA) (N : POVM Λ dB) : ℝ :=
  1 - ∑ a, bornProb ψ ((M.mats a).val) ((N.mats a).val)

/-- **The matrix disagreement is that of the tensor-product model.** -/
theorem dis_eq_tensor (ψ : dA × dB → ℂ) (M : POVM Λ dA) (N : POVM Λ dB) :
    dis ψ M N = (BipartiteModel.tensor ψ).dis M.toIn N.toIn := by
  simp only [dis, BipartiteModel.dis, bornProb_eq_tensor, POVM.toIn_op]

theorem bornProb_one_right (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) (N : POVM Λ dB) :
    bornProb ψ EA (1 : Matrix dB dB ℂ) = ∑ b, bornProb ψ EA ((N.mats b).val) := by
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).bornProb_one_right EA N.toIn

theorem bornProb_one_left (ψ : dA × dB → ℂ) (M : POVM Λ dA) (EB : Matrix dB dB ℂ) :
    bornProb ψ (1 : Matrix dA dA ℂ) EB = ∑ a, bornProb ψ ((M.mats a).val) EB := by
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).bornProb_one_left M.toIn EB

theorem sum_bornProb_diag_le {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : POVM Λ dA)
    (N : POVM Λ dB) : ∑ a, bornProb ψ ((M.mats a).val) ((N.mats a).val) ≤ 1 := by
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_bornProb_diag_le (norm_evec_eq_one hψ) M.toIn N.toIn

theorem dis_nonneg {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : POVM Λ dA) (N : POVM Λ dB) :
    0 ≤ dis ψ M N := by
  rw [dis_eq_tensor]
  exact (BipartiteModel.tensor ψ).dis_nonneg (norm_evec_eq_one hψ) M.toIn N.toIn

/-- **Data processing**: a common coarse-graining can only decrease the disagreement. -/
theorem dis_map_le {C : Type*} [Fintype C] [DecidableEq C] (ψ : dA × dB → ℂ) (M : POVM Λ dA)
    (N : POVM Λ dB) (f : Λ → C) : dis ψ (M.map f) (N.map f) ≤ dis ψ M N := by
  rw [dis_eq_tensor, dis_eq_tensor]
  exact (BipartiteModel.tensor ψ).dis_map_le M.toIn N.toIn f

/-- The disagreement is the sum of the off-diagonal Born probabilities. -/
theorem dis_eq_sum_ne {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) [DecidableEq Λ] (M : POVM Λ dA)
    (N : POVM Λ dB) :
    dis ψ M N = ∑ a, ∑ b, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val) := by
  rw [dis_eq_tensor]
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).dis_eq_sum_ne (norm_evec_eq_one hψ) M.toIn N.toIn

/-- **An event transfers across the parties**: its probability under Alice's measurement is at
most its probability under Bob's plus their disagreement. -/
theorem sum_ite_bornProb_one_le {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) [DecidableEq Λ]
    (M : POVM Λ dA) (N : POVM Λ dB) (E : Λ → Prop) [DecidablePred E] :
    ∑ a, (if E a then bornProb ψ ((M.mats a).val) (1 : Matrix dB dB ℂ) else 0)
      ≤ ∑ b, (if E b then bornProb ψ (1 : Matrix dA dA ℂ) ((N.mats b).val) else 0)
        + dis ψ M N := by
  rw [dis_eq_tensor]
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_ite_bornProb_one_le (norm_evec_eq_one hψ) M.toIn N.toIn E

/-- The mirror image: an event transfers from Bob's measurement to Alice's. -/
theorem sum_ite_bornProb_one_le' {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) [DecidableEq Λ]
    (M : POVM Λ dA) (N : POVM Λ dB) (E : Λ → Prop) [DecidablePred E] :
    ∑ b, (if E b then bornProb ψ (1 : Matrix dA dA ℂ) ((N.mats b).val) else 0)
      ≤ ∑ a, (if E a then bornProb ψ ((M.mats a).val) (1 : Matrix dB dB ℂ) else 0)
        + dis ψ M N := by
  rw [dis_eq_tensor]
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_ite_bornProb_one_le' (norm_evec_eq_one hψ) M.toIn N.toIn E

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
  simp only [dis_eq_tensor]
  exact (BipartiteModel.tensor ψ).dis_le_sum_dis_map_add (norm_evec_eq_one hψ) M.toIn N.toIn
    hν0 hν1 ev hε hsep

/-! ## Families on a uniform index -/

section Uniform

variable {X : Type*} [Fintype X] [Nonempty X]

theorem one_sub_agreeSum_uniform (ψ : dA × dB → ℂ) (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    1 - agreeSum (uniform X) ψ M N = (∑ x, dis ψ (M x) (N x)) / Fintype.card X := by
  rw [agreeSum_eq_tensor]
  simp only [dis_eq_tensor]
  exact (BipartiteModel.tensor ψ).one_sub_agreeSum_uniform _ _

/-- **The disagreement triangle** across the two parties, on a uniform index: Alice's `A` against
Bob's `D`, through Bob's `B` and Alice's `C`. -/
theorem sum_dis_triangle {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (A C : X → POVM Λ dA)
    (B D : X → POVM Λ dB) :
    ∑ x, dis ψ (A x) (D x)
      ≤ 11 * (∑ x, dis ψ (A x) (B x) + ∑ x, dis ψ (C x) (B x) + ∑ x, dis ψ (C x) (D x)) := by
  simp only [dis_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_dis_triangle (norm_evec_eq_one hψ) (fun x => (A x).toIn)
    (fun x => (C x).toIn) (fun x => (B x).toIn) (fun x => (D x).toIn)

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
  rw [condFail_eq_tensor]
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_ite_bornProb_le_condFail (MA := fun x => (MA x).toIn)
    (MB := fun y => (MB y).toIn) (norm_evec_eq_one hψ) E hD

/-- The mirror image, for an event of Alice's answer. -/
theorem sum_ite_bornProb_le_condFail' (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (E : A → Prop)
    [DecidablePred E] (hD : ∀ a b, G.D x y a b = true → ¬ E a) :
    ∑ a, (if E a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
      ≤ condFail G ψ MA MB x y := by
  rw [condFail_eq_tensor]
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_ite_bornProb_le_condFail' (MA := fun x => (MA x).toIn)
    (MB := fun y => (MB y).toIn) (norm_evec_eq_one hψ) E hD

/-- The disagreement of two readings is the weight of the outcome pairs they read differently. -/
theorem dis_map_eq_sum {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : POVM A dA) (N : POVM B dB)
    (f : A → C) (g : B → C) :
    dis ψ (M.map f) (N.map g) = ∑ a, ∑ b, (if f a = g b then 0 else 1)
      * bornProb ψ ((M.mats a).val) ((N.mats b).val) := by
  rw [dis_eq_tensor]
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).dis_map_eq_sum (norm_evec_eq_one hψ) M.toIn N.toIn f g

/-- **A subtest accepting when two events are avoided and two readings agree** fails at most the
events' probabilities plus the readings' disagreement. -/
theorem condFail_le_of (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (EA : A → Prop) (EB : B → Prop)
    [DecidablePred EA] [DecidablePred EB] (f : A → C) (g : B → C)
    (hD : ∀ a b, ¬ EA a → ¬ EB b → f a = g b → G.D x y a b = true) :
    condFail G ψ MA MB x y
      ≤ ∑ a, (if EA a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
        + ∑ b, (if EB b then bornProb ψ (1 : Matrix dA dA ℂ) (((MB y).mats b).val) else 0)
        + dis ψ ((MA x).map f) ((MB y).map g) := by
  rw [condFail_eq_tensor, dis_eq_tensor]
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).condFail_le_of (MA := fun x => (MA x).toIn)
    (MB := fun y => (MB y).toIn) (norm_evec_eq_one hψ) EA EB f g hD

end Subtests

end MIPRE

end

end
