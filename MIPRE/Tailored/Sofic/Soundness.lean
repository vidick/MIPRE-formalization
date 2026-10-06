/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Perturb

@[expose] public section

/-!
# An almost optimal action is near one passing Checks 1–3

Paper I, the soundness of Theorem I:2126 up to Proposition I:2279: Propositions I:2267
(perturbation) and I:2283 (significance), combined through the robustness claim I:1480. If a
finite action `σ` has value at least `1 - ε` in the associated test `assocTest g`, some finite
action `σ'` passes Checks 1–3 at every point and has value at least
`1 - 300 (Λ + 1)⁴ 2^{4(Λ + 1)} ε`, `Λ = g.ansLen` (`exists_checks_of_value`).

The proof: `σ'` is the perturbation (`MIPRE/Tailored/Sofic/Perturb.lean`) of the doubled action
`τ = σ ⊕ σ`, which has the same value. Writing `Lose = Σ_{x,y} w(x, y) · #{points failing the
challenge at (x, y)}`, the value bound says `Lose ≤ ε |τ| W`. `J₀` fixes, and `J₀²` moves, no
more points than fail any challenge, so `d(J₂, J₀) ≤ 3 Lose / W`. At the vertex `x`, every
relation of Checks 1–3 fails at no more points than fail the challenge at `(x, y)` or at
`(y, x)`, so weighting by `m(x) = Σ_y (w(x, y) + w(y, x))` gives
`m(x) · #bad(x) ≤ (Λ² + 3Λ) D_x + 3Λ m(x) d(J₂, J₀)` with `Σ_x D_x = 2 Lose`. The significance of
`X(x, i)` carries the factor `m(x) / W` (`sig_genX_le`), which turns these per-vertex bounds into
a bound in terms of `Lose`, and so of `ε`. These are the paper's per-vertex losing probabilities
`ε_x`, with `m(x) ε_x = D_x / |τ|`.
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue Finset

variable {g : TailoredGameData}

/-! ## Reindexing the generators -/

private theorem sum_range_mul (L : ℕ) (h : ℕ → ℝ) :
    ∀ a, ∑ j ∈ range (a * L), h j = ∑ x ∈ range a, ∑ i ∈ range L, h (x * L + i)
  | 0 => by simp
  | a + 1 => by
    rw [Nat.succ_mul, sum_range_add, sum_range_mul L h a, sum_range_succ]

/-- The generators are `J` and the `X(x, i)`, `x ≤ nV`, `i < Λ`. -/
theorem sum_gens (F : ℕ → ℝ) :
    ∑ k : Fin (nGen g), F k = F genJ +
      ∑ x ∈ range (g.nV + 1), ∑ i ∈ range g.ansLen, F (genX g x i) := by
  rw [Fin.sum_univ_eq_sum_range F (nGen g)]
  unfold nGen
  rw [add_comm 1, sum_range_succ', sum_range_mul g.ansLen (fun k => F (k + 1)), add_comm]
  congr 1
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro i _
  unfold genX
  congr 1
  ring

/-! ## The losing mass -/

variable (τ : FiniteAction (nGen g))

/-- The weighted number of (challenge, point) pairs failing: `Lose = Σ_{x,y} w(x, y) · #fail`. -/
def lose (g : TailoredGameData) (τ : FiniteAction (nGen g)) : ℕ :=
  ∑ x ∈ range (g.nV + 1), ∑ y ∈ range (g.nV + 1), qw g x y * npass τ g x y

theorem one_sub_value : 1 - (assocTest g).value τ = (lose g τ : ℝ) / (τ.N * qwTot g) := by
  have hN : (0 : ℝ) < τ.N := by exact_mod_cast τ.N_pos
  have hW : (0 : ℝ) < qwTot g := by exact_mod_cast qwTot_pos g
  have hp : ∀ x y, τ.passProb (words g x y) (clauses g x y) = 1 - (npass τ g x y : ℝ) / τ.N := by
    intro x y
    unfold FiniteAction.passProb npass
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin τ.N)))
      (fun q => τ.Passes (words g x y) (clauses g x y) q)
    rw [card_univ, Fintype.card_fin] at this
    field_simp
    rw [eq_sub_iff_add_eq]
    exact_mod_cast this
  have hsum : ∑ x ∈ range (g.nV + 1), ∑ y ∈ range (g.nV + 1),
      (qw g x y : ℝ) * (1 - (npass τ g x y : ℝ) / τ.N) = (qwTot g : ℝ) - (lose g τ : ℝ) / τ.N := by
    unfold lose qwTot
    push_cast
    rw [Finset.sum_div, ← sum_sub_distrib]
    apply sum_congr rfl; intro x _
    rw [Finset.sum_div, ← sum_sub_distrib]
    apply sum_congr rfl; intro y _
    ring
  rw [value_eq]
  simp only [hp]
  rw [hsum]
  field_simp
  ring

theorem lose_le {ε : ℝ} (h : 1 - ε ≤ (assocTest g).value τ) :
    (lose g τ : ℝ) ≤ ε * τ.N * qwTot g := by
  have hN : (0 : ℝ) < τ.N := by exact_mod_cast τ.N_pos
  have hW : (0 : ℝ) < qwTot g := by exact_mod_cast qwTot_pos g
  have := one_sub_value τ
  have h2 : (lose g τ : ℝ) / (τ.N * qwTot g) ≤ ε := by linarith
  rw [div_le_iff₀ (by positivity)] at h2
  linarith

/-- A count bounded by every challenge's failures is bounded by `Lose / W`. -/
theorem mul_qwTot_le_lose {c : ℕ} (h : ∀ x y, c ≤ npass τ g x y) : c * qwTot g ≤ lose g τ := by
  unfold lose qwTot
  rw [mul_comm, sum_mul]
  apply sum_le_sum; intro x _
  rw [sum_mul]
  apply sum_le_sum; intro y _
  exact Nat.mul_le_mul_left _ (h x y)

theorem diffCard_J₂_mul_le (S : SwapData τ) :
    diffCard (J₂ τ S) (J₀ τ) * qwTot g ≤ 3 * lose g τ := by
  have h1 := mul_qwTot_le_lose τ (c := fixJ τ) (fun x y => card_J_fixed_le τ g x y)
  have h2 := mul_qwTot_le_lose τ (c := sqJ τ) (fun x y => card_J_sq_le τ g x y)
  have h3 := Nat.mul_le_mul_right (qwTot g) (diffCard_J₂_le τ S)
  nlinarith

/-- The weighted failures at the vertex `x`. -/
def loseAt (g : TailoredGameData) (τ : FiniteAction (nGen g)) (x : ℕ) : ℕ :=
  ∑ y ∈ range (g.nV + 1), (qw g x y * npass τ g x y + qw g y x * npass τ g y x)

theorem sum_loseAt : ∑ x ∈ range (g.nV + 1), loseAt g τ x = 2 * lose g τ := by
  unfold loseAt lose
  simp only [sum_add_distrib]
  rw [sum_comm (f := fun x y => qw g y x * npass τ g y x)]
  ring

theorem mdeg_mul_bad_le (S : SwapData τ) {x : ℕ} (hx : x < g.nV + 1) :
    mdeg g x * badX τ S x ≤ (g.ansLen ^ 2 + 3 * g.ansLen) * loseAt g τ x +
      3 * g.ansLen * diffCard (J₂ τ S) (J₀ τ) * mdeg g x := by
  have hL := lenAt_le_ansLen hx
  have hb : ∀ B, LocalBounds τ x B → badX τ S x ≤ (g.ansLen ^ 2 + 3 * g.ansLen) * B +
      3 * g.ansLen * diffCard (J₂ τ S) (J₀ τ) := by
    intro B hB
    refine (card_bad_le τ S hB).trans ?_
    have : g.lenAt x ^ 2 ≤ g.ansLen ^ 2 := Nat.pow_le_pow_left hL 2
    have h1 : (g.lenAt x ^ 2 + 3 * g.lenAt x) * B ≤ (g.ansLen ^ 2 + 3 * g.ansLen) * B :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : 3 * g.lenAt x * diffCard (J₂ τ S) (J₀ τ) ≤
        3 * g.ansLen * diffCard (J₂ τ S) (J₀ τ) := Nat.mul_le_mul_right _ (by omega)
    omega
  unfold mdeg loseAt
  rw [sum_mul, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro y _
  have h1 := Nat.mul_le_mul_left (qw g x y) (hb _ (localBounds_left τ x y))
  have h2 := Nat.mul_le_mul_left (qw g y x) (hb _ (localBounds_right τ x y))
  nlinarith

/-! ## The weighted distance -/

/-- The significance-weighted distance from `τ` to its perturbation, generator by generator:
`J` contributes `sig(J) d(J₂, J₀)`, the variables at `x` at most `Λ` times
`sig(X(x, ·)) · 2^{Λ+1} #bad(x) / |τ|`. -/
theorem weighted_dist_le (S : SwapData τ) :
    ∑ k : Fin (nGen g), sig (assocTest g) k * dH (τ.σ k) (ρPert τ S k) ≤
      (sigBound g : ℝ) * diffCard (J₂ τ S) (J₀ τ) / τ.N +
        g.ansLen * (sigBound g * 2 ^ (g.ansLen + 1) / (qwTot g * τ.N)) *
          ∑ x ∈ range (g.nV + 1), (mdeg g x * badX τ S x : ℝ) := by
  classical
  have hN : (0 : ℝ) < τ.N := by exact_mod_cast τ.N_pos
  have hW : (0 : ℝ) < qwTot g := by exact_mod_cast qwTot_pos g
  have hsB : (0 : ℝ) ≤ sigBound g := Nat.cast_nonneg _
  set F : ℕ → ℝ := fun k => if h : k < nGen g then
    sig (assocTest g) k * dH (τ.σ ⟨k, h⟩) (ρPert τ S ⟨k, h⟩) else 0 with hF
  have hsum : ∑ k : Fin (nGen g), sig (assocTest g) k * dH (τ.σ k) (ρPert τ S k) =
      ∑ k : Fin (nGen g), F k := by
    apply sum_congr rfl; intro k _
    simp only [hF, dite_eq_left k.2]
  rw [hsum, sum_gens F]
  have hdH : ∀ (a b : Equiv.Perm (Fin τ.N)), dH a b = (diffCard b a : ℝ) / τ.N := by
    intro a b; simp [dH, diffCard_comm]
  -- the generator `J`
  have hJ : F genJ ≤ (sigBound g : ℝ) * diffCard (J₂ τ S) (J₀ τ) / τ.N := by
    simp only [hF, dite_eq_left genJ_lt_nGen]
    have e1 : τ.σ ⟨genJ, genJ_lt_nGen⟩ = J₀ τ := (genPerm_eq τ genJ_lt_nGen).symm
    have e2 : ρPert τ S ⟨genJ, genJ_lt_nGen⟩ = J₂ τ S := by simp [ρPert]
    rw [e1, e2, hdH, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (sig_le genJ) (by positivity)
  -- the variables
  have hX : ∀ x ∈ range (g.nV + 1), ∀ i ∈ range g.ansLen, F (genX g x i) ≤
      sigBound g * 2 ^ (g.ansLen + 1) / (qwTot g * τ.N) * (mdeg g x * badX τ S x : ℝ) := by
    intro x hx i hi
    have hx' := mem_range.mp hx
    have hi' := mem_range.mp hi
    have hlt := genX_lt_nGen hx' hi'
    have hRHS : (0 : ℝ) ≤ sigBound g * 2 ^ (g.ansLen + 1) / (qwTot g * τ.N) *
        (mdeg g x * badX τ S x : ℝ) := by positivity
    simp only [hF, dite_eq_left hlt]
    have e1 : τ.σ ⟨genX g x i, hlt⟩ = genPerm τ (genX g x i) := (genPerm_eq τ hlt).symm
    by_cases hix : i < g.lenAt x
    · have e2 : ρPert τ S ⟨genX g x i, hlt⟩ = Xfix τ S x i := by
        rw [← perturbed_X τ S hx' hix, genPerm_eq _ hlt]; rfl
      rw [e1, e2, hdH]
      have h1 := sig_genX_le hx' hix
      have h2 : (diffCard (Xfix τ S x i) (genPerm τ (genX g x i)) : ℝ) ≤
          2 ^ (g.ansLen + 1) * badX τ S x := by
        have := diffCard_Xfix_le τ S hix
        have h3 : 2 ^ (g.lenAt x + 1) ≤ 2 ^ (g.ansLen + 1) :=
          Nat.pow_le_pow_right (by norm_num) (by have := lenAt_le_ansLen hx'; omega)
        exact_mod_cast this.trans (Nat.mul_le_mul_right _ h3)
      have hsig0 : 0 ≤ sig (assocTest g) (genX g x i) := sig_nonneg _ _
      calc sig (assocTest g) (genX g x i) * ((diffCard (Xfix τ S x i)
            (genPerm τ (genX g x i)) : ℝ) / τ.N)
          ≤ (sigBound g * mdeg g x / qwTot g) * ((2 ^ (g.ansLen + 1) * badX τ S x : ℝ) / τ.N) := by
            gcongr
        _ = _ := by field_simp
    · have e2 : ρPert τ S ⟨genX g x i, hlt⟩ = τ.σ ⟨genX g x i, hlt⟩ := by
        apply perturbed_other τ S _ (genX_ne_genJ x i)
        obtain ⟨d1, d2⟩ := genX_decode (g := g) (x := x) hi'
        simp only [d1, d2]
        exact fun h => hix h.2
      rw [e2, hdH, diffCard_self]
      simpa using hRHS
  have hXsum : ∑ x ∈ range (g.nV + 1), ∑ i ∈ range g.ansLen, F (genX g x i) ≤
      g.ansLen * (sigBound g * 2 ^ (g.ansLen + 1) / (qwTot g * τ.N)) *
        ∑ x ∈ range (g.nV + 1), (mdeg g x * badX τ S x : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum; intro x hx
    refine (sum_le_sum (hX x hx)).trans (le_of_eq ?_)
    rw [sum_const, card_range, nsmul_eq_mul]
    ring
  linarith

/-- **Perturbation and robustness combined**: if `τ` has value at least `1 - ε`, its
perturbation has value at least `1 - sigBound · ε (3 + 2^{Λ+1}(2Λ³ + 24Λ²))`. -/
theorem value_perturbed_ge (S : SwapData τ) {ε : ℝ} (h : 1 - ε ≤ (assocTest g).value τ) :
    1 - (1 + (sigBound g : ℝ) * (3 + 2 ^ (g.ansLen + 1) *
      (2 * (g.ansLen : ℝ) ^ 3 + 24 * (g.ansLen : ℝ) ^ 2))) * ε ≤
        (assocTest g).value (perturbed τ S) := by
  have hN : (0 : ℝ) < τ.N := by exact_mod_cast τ.N_pos
  have hW : (0 : ℝ) < qwTot g := by exact_mod_cast qwTot_pos g
  have hL := lose_le τ h
  have hε : 0 ≤ ε := by
    have : (0 : ℝ) ≤ lose g τ := Nat.cast_nonneg _
    have : 0 ≤ ε * (τ.N * qwTot g) := by nlinarith
    exact nonneg_of_mul_nonneg_left this (by positivity)
  -- the distance of `J`
  have hdJ : (diffCard (J₂ τ S) (J₀ τ) : ℝ) ≤ 3 * ε * τ.N := by
    have := diffCard_J₂_mul_le τ S
    have h' : (diffCard (J₂ τ S) (J₀ τ) : ℝ) * qwTot g ≤ 3 * lose g τ := by exact_mod_cast this
    have : (diffCard (J₂ τ S) (J₀ τ) : ℝ) * qwTot g ≤ (3 * ε * τ.N) * qwTot g := by nlinarith
    exact le_of_mul_le_mul_right this hW
  -- the bad points
  have hbad : ∑ x ∈ range (g.nV + 1), (mdeg g x * badX τ S x : ℝ) ≤
      ((g.ansLen : ℝ) ^ 2 + 3 * g.ansLen) * (2 * (ε * τ.N * qwTot g)) +
        3 * g.ansLen * (3 * ε * τ.N) * (2 * qwTot g) := by
    have h1 : ∑ x ∈ range (g.nV + 1), (mdeg g x * badX τ S x : ℝ) ≤
        ∑ x ∈ range (g.nV + 1), (((g.ansLen : ℝ) ^ 2 + 3 * g.ansLen) * loseAt g τ x +
          3 * g.ansLen * diffCard (J₂ τ S) (J₀ τ) * mdeg g x) := by
      apply sum_le_sum; intro x hx
      exact_mod_cast mdeg_mul_bad_le τ S (mem_range.mp hx)
    refine h1.trans ?_
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have e1 : ∑ x ∈ range (g.nV + 1), (loseAt g τ x : ℝ) = 2 * lose g τ := by
      exact_mod_cast sum_loseAt τ
    have e2 : ∑ x ∈ range (g.nV + 1), (mdeg g x : ℝ) = 2 * qwTot g := by
      exact_mod_cast sum_mdeg g
    rw [e1, e2]
    have hL0 : (0 : ℝ) ≤ g.ansLen := Nat.cast_nonneg _
    have hq : (0 : ℝ) ≤ (g.ansLen : ℝ) ^ 2 + 3 * g.ansLen := by positivity
    gcongr
  have hrob : |(assocTest g).value τ - (assocTest g).value (withPerms τ (ρPert τ S))| ≤
      ∑ k : Fin (nGen g), sig (assocTest g) k * dH (τ.σ k) (ρPert τ S k) :=
    abs_value_sub_le (assocTest g) τ (ρPert τ S)
  have hdist := weighted_dist_le τ S
  have hsB : (0 : ℝ) ≤ sigBound g := Nat.cast_nonneg _
  have hA : (0 : ℝ) ≤ 2 ^ (g.ansLen + 1) := by positivity
  have hL0 : (0 : ℝ) ≤ g.ansLen := Nat.cast_nonneg _
  -- bound the two terms of the weighted distance
  have t1 : (sigBound g : ℝ) * diffCard (J₂ τ S) (J₀ τ) / τ.N ≤ sigBound g * (3 * ε) := by
    rw [div_le_iff₀ hN]
    nlinarith
  have t2 : g.ansLen * (sigBound g * 2 ^ (g.ansLen + 1) / (qwTot g * τ.N)) *
      ∑ x ∈ range (g.nV + 1), (mdeg g x * badX τ S x : ℝ) ≤
      sigBound g * 2 ^ (g.ansLen + 1) *
        (2 * (g.ansLen : ℝ) ^ 3 + 24 * (g.ansLen : ℝ) ^ 2) * ε := by
    have hc : (0 : ℝ) ≤ g.ansLen * (sigBound g * 2 ^ (g.ansLen + 1) / (qwTot g * τ.N)) := by
      positivity
    refine (mul_le_mul_of_nonneg_left hbad hc).trans (le_of_eq ?_)
    field_simp
    ring
  have hval : (assocTest g).value (perturbed τ S) = (assocTest g).value (withPerms τ (ρPert τ S)) :=
    rfl
  rw [hval]
  have := (abs_le.mp hrob).2
  have e : 1 - (1 + (sigBound g : ℝ) * (3 + 2 ^ (g.ansLen + 1) *
      (2 * (g.ansLen : ℝ) ^ 3 + 24 * (g.ansLen : ℝ) ^ 2))) * ε =
      (1 - ε) - ((sigBound g : ℝ) * (3 * ε) + sigBound g * 2 ^ (g.ansLen + 1) *
        (2 * (g.ansLen : ℝ) ^ 3 + 24 * (g.ansLen : ℝ) ^ 2) * ε) := by ring
  rw [e]
  linarith

/-- `1 + sigBound · (3 + 2^{Λ+1}(2Λ³ + 24Λ²)) ≤ 300 (Λ + 1)⁴ 2^{4(Λ + 1)}`. -/
theorem numeric_bound (L : ℕ) :
    1 + (((2 * L + 4) * (3 + 8 * L + 2 * L ^ 2 + 2 * 4 ^ L) : ℕ) : ℝ) *
      (3 + 2 ^ (L + 1) * (2 * (L : ℝ) ^ 3 + 24 * (L : ℝ) ^ 2)) ≤
      300 * ((L : ℝ) + 1) ^ 4 * 2 ^ (4 * (L + 1)) := by
  set A : ℝ := 2 ^ L with hA
  have hA1 : 1 ≤ A := one_le_pow₀ (by norm_num)
  have hLA : (L : ℝ) + 1 ≤ A := by
    have h := (Nat.cast_le (α := ℝ)).mpr (Nat.lt_two_pow_self (n := L))
    push_cast at h
    rw [hA]; exact h
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have h2 : (2 : ℝ) ^ (L + 1) = 2 * A := by rw [pow_succ, mul_comm]
  have h16 : (2 : ℝ) ^ (4 * (L + 1)) = 16 * A ^ 4 := by
    rw [show 4 * (L + 1) = 4 * L + 4 by ring, pow_add, pow_mul', ← hA]; norm_num; ring
  have hsig : (((2 * L + 4) * (3 + 8 * L + 2 * L ^ 2 + 2 * 4 ^ L) : ℕ) : ℝ) ≤ 60 * A ^ 3 := by
    push_cast
    rw [show ((4 : ℝ)) ^ L = A ^ 2 by rw [hA, ← pow_mul, mul_comm, pow_mul]; norm_num]
    have e1 : 2 * (L : ℝ) + 4 ≤ 4 * A := by linarith
    have e2 : 3 + 8 * (L : ℝ) + 2 * (L : ℝ) ^ 2 + 2 * A ^ 2 ≤ 15 * A ^ 2 := by nlinarith
    calc (2 * (L : ℝ) + 4) * (3 + 8 * L + 2 * L ^ 2 + 2 * A ^ 2) ≤ (4 * A) * (15 * A ^ 2) := by
          apply mul_le_mul e1 e2 (by positivity) (by positivity)
      _ = 60 * A ^ 3 := by ring
  rw [h2, h16]
  have hpos : (0 : ℝ) ≤ 3 + 2 * A * (2 * (L : ℝ) ^ 3 + 24 * (L : ℝ) ^ 2) := by positivity
  calc 1 + (((2 * L + 4) * (3 + 8 * L + 2 * L ^ 2 + 2 * 4 ^ L) : ℕ) : ℝ) *
        (3 + 2 * A * (2 * (L : ℝ) ^ 3 + 24 * (L : ℝ) ^ 2))
      ≤ 1 + 60 * A ^ 3 * (3 + 2 * A * (2 * (L : ℝ) ^ 3 + 24 * (L : ℝ) ^ 2)) := by
        gcongr
    _ ≤ 300 * ((L : ℝ) + 1) ^ 4 * (16 * A ^ 4) := by
        have hA3 : A ^ 3 ≤ A ^ 4 := pow_le_pow_right₀ hA1 (by norm_num)
        have hA4 : 1 ≤ A ^ 4 := one_le_pow₀ hA1
        have hL4 : 0 ≤ A ^ 4 * (L : ℝ) ^ 4 := by positivity
        have hL1 : 0 ≤ A ^ 4 * (L : ℝ) := by positivity
        have hL3 : 0 ≤ A ^ 4 * (L : ℝ) ^ 3 := by positivity
        have hL2 : 0 ≤ A ^ 4 * (L : ℝ) ^ 2 := by positivity
        nlinarith

/-- The constant of `exists_checks_of_value`. -/
def Cp : ℝ := 300

/-- **An action of value `≥ 1 - ε` in the associated test is near one passing Checks 1–3**
(Propositions I:2267 and I:2283 with Claim I:1480): some finite action passes Checks 1–3 at every
point and has value at least `1 - Cp (Λ + 1)⁴ 2^{4(Λ + 1)} ε`, `Λ = g.ansLen`, `Cp = 300`. -/
theorem exists_checks_of_value (g : TailoredGameData) (σ : FiniteAction (nGen g)) (ε : ℝ)
    (h : 1 - ε ≤ (assocTest g).value σ) :
    ∃ σ' : FiniteAction (nGen g), Checks g σ' ∧
      1 - Cp * ((g.ansLen : ℝ) + 1) ^ 4 * 2 ^ (4 * (g.ansLen + 1)) * ε ≤
        (assocTest g).value σ' := by
  have hτ : 1 - ε ≤ (assocTest g).value (double σ) :=
    h.trans_eq (value_double (assocTest g) σ).symm
  set τ := double σ
  refine ⟨perturbed τ (dblSwapData σ), checks_perturbed τ (dblSwapData σ), ?_⟩
  have h1 := value_perturbed_ge τ (dblSwapData σ) hτ
  have hε : 0 ≤ ε := by
    have hL := lose_le τ hτ
    have hN : (0 : ℝ) < τ.N := by exact_mod_cast τ.N_pos
    have hW : (0 : ℝ) < qwTot g := by exact_mod_cast qwTot_pos g
    have : (0 : ℝ) ≤ lose g τ := Nat.cast_nonneg _
    have : 0 ≤ ε * (τ.N * qwTot g) := by nlinarith
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have h2 := numeric_bound g.ansLen
  unfold sigBound at h1
  unfold Cp
  nlinarith

end MIPRE.Tailored.Sofic

end
