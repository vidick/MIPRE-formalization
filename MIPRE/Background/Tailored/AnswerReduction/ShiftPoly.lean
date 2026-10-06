/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Coefficients

@[expose] public section

/-!
# Shifting a low-individual-degree polynomial along an axis

Let `g` be a polynomial in `n` variables of individual degree at most `d` over a finite field `F`
with `q` elements, given by its coefficient vector, and suppose `g` has a nonzero coefficient on a
monomial `∏ₖ Xₖ^(eₖ)` containing `Xᵢ` (`eᵢ ≠ 0`). Then `g` changes value along most axis-parallel
steps in direction `i`: `g(u + t eᵢ) ≠ g(u)` for at least `q^n (q - (n + 1) d)` of the pairs
`(u, t) ∈ F^n × F` (`card_shift_ne_ge`).

The proof restricts `g` to the axis-parallel line through `u` in direction `i`: a univariate
polynomial `g.onAxis i u` of degree at most `d` in the `i`-th coordinate, whose coefficients are
the coefficient vectors `g.coef {i} t` evaluated at `u`. Its coefficient on `X^(eᵢ)` is a nonzero
coefficient vector `G` evaluated at `u`. Where `G(u) ≠ 0` the restriction is nonconstant, so it
takes the value `g(u)` at most `d` times (`card_shift_eq_le`); and by Schwartz--Zippel
(`card_eval_eq_zero_le`) `G(u) = 0` for at most `n d q^(n - 1)` points `u`.
-/

noncomputable section

namespace MIPRE.LIDT

open Finset

section OnAxis

variable {F : Type*} [Field F] {n d : ℕ}

/-- The restriction of `g` to the axis-parallel line through `u` in direction `i`, as a univariate
polynomial in the `i`-th coordinate: its value at `u i + t` is `g(u + t eᵢ)`. -/
def LowIndDegPoly.onAxis (g : LowIndDegPoly (F := F) (m := n) (d := d)) (i : Fin n)
    (u : Point F n) : Polynomial F :=
  ∑ t : Fin n → Fin (d + 1), Polynomial.C ((g.coef {i} t).eval u) * Polynomial.X ^ (t i : ℕ)

/-- Evaluation of the restriction to an axis-parallel line. -/
theorem LowIndDegPoly.eval_onAxis (g : LowIndDegPoly (F := F) (m := n) (d := d)) (i : Fin n)
    (u : Point F n) (x : F) :
    (g.onAxis i u).eval x = ∑ t : Fin n → Fin (d + 1), (g.coef {i} t).eval u * x ^ (t i : ℕ) := by
  simp only [LowIndDegPoly.onAxis, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- Along the axis-parallel line through `u` in direction `i`, `g` is its restriction. -/
theorem LowIndDegPoly.eval_shift_eq_eval_onAxis (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (i : Fin n) (u : Point F n) (t : F) :
    g.eval (u + t • Pi.single i 1) = (g.onAxis i u).eval (u i + t) := by
  rw [LowIndDegPoly.eval_onAxis, LowIndDegPoly.eval_eq_sum_coef g {i}]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hoff : ∀ k ∉ ({i} : Finset (Fin n)), (u + t • Pi.single i 1 : Point F n) k = u k := by
    intro k hk
    rw [Finset.mem_singleton] at hk
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero, add_zero]
  rw [Finset.prod_singleton, LowIndDegPoly.eval_coef_of_eq_off g {i} s hoff, mul_comm]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]

/-- At `u` itself, `g` is its restriction evaluated at `u i`. -/
theorem LowIndDegPoly.eval_eq_eval_onAxis (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (i : Fin n) (u : Point F n) : g.eval u = (g.onAxis i u).eval (u i) := by
  have h := g.eval_shift_eq_eval_onAxis i u 0
  rwa [zero_smul, add_zero, add_zero] at h

/-- The restriction to an axis-parallel line has degree at most `d`. -/
theorem LowIndDegPoly.natDegree_onAxis_le (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (i : Fin n) (u : Point F n) : (g.onAxis i u).natDegree ≤ d :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun t _ =>
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (t i).isLt)

/-- The coefficient of `X^(e i)` in the restriction is the coefficient vector of the pattern
`Xᵢ^(e i)`, evaluated at `u`. -/
theorem LowIndDegPoly.coeff_onAxis (g : LowIndDegPoly (F := F) (m := n) (d := d)) (i : Fin n)
    (u : Point F n) (e : Fin n → Fin (d + 1)) :
    (g.onAxis i u).coeff (e i) = (g.coef {i} (maskOn {i} e)).eval u := by
  have hi : maskOn {i} e i = e i := ite_eq_left (Finset.mem_singleton_self i)
  simp only [LowIndDegPoly.onAxis, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (maskOn {i} e), ite_eq_left (by rw [hi])]
  · intro t _ ht
    split_ifs with h
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp ht
      have hki : k ∉ ({i} : Finset (Fin n)) := by
        intro hki
        rw [Finset.mem_singleton.mp hki, hi] at hk
        exact hk (Fin.ext h.symm)
      have hz : g.coef {i} t = 0 := by
        funext e'
        rw [LowIndDegPoly.coef, ite_eq_right]
        · rfl
        · rintro ⟨-, h2⟩
          exact hk (by rw [h2 k hki, maskOn_apply_of_not e hki])
      rw [hz]
      simp only [LowIndDegPoly.eval, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    · rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

end OnAxis

/-- Where the coefficient vector of the pattern `Xᵢ^(e i)`, `e i ≠ 0`, does not vanish at `u`, `g`
takes the value `g(u)` at most `d` times along the axis-parallel line through `u` in
direction `i`. -/
theorem card_shift_eq_le {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}
    (g : LowIndDegPoly (F := F) (m := n) (d := d)) {i : Fin n} {e : Fin n → Fin (d + 1)}
    (hi : (e i : ℕ) ≠ 0) {u : Point F n} (hu : (g.coef {i} (maskOn {i} e)).eval u ≠ 0) :
    (univ.filter fun t : F => g.eval (u + t • Pi.single i 1) = g.eval u).card ≤ d := by
  have hψ : g.onAxis i u - Polynomial.C ((g.onAxis i u).eval (u i)) ≠ 0 := by
    intro h
    apply hu
    have := congrArg (fun p => Polynomial.coeff p (e i)) h
    simpa only [Polynomial.coeff_sub, Polynomial.coeff_C_of_ne_zero hi, sub_zero,
      Polynomial.coeff_zero, LowIndDegPoly.coeff_onAxis] using this
  calc (univ.filter fun t : F => g.eval (u + t • Pi.single i 1) = g.eval u).card
      ≤ (g.onAxis i u - Polynomial.C ((g.onAxis i u).eval (u i))).roots.toFinset.card := by
        refine Finset.card_le_card_of_injOn (fun t => u i + t) ?_
          (fun t₁ _ t₂ _ h => add_left_cancel h)
        intro t ht
        rw [Finset.mem_coe, Finset.mem_filter] at ht
        rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hψ,
          Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C,
          ← LowIndDegPoly.eval_shift_eq_eval_onAxis, ← LowIndDegPoly.eval_eq_eval_onAxis, ht.2,
          sub_self]
    _ ≤ Multiset.card (g.onAxis i u - Polynomial.C ((g.onAxis i u).eval (u i))).roots :=
        Multiset.toFinset_card_le _
    _ ≤ (g.onAxis i u - Polynomial.C ((g.onAxis i u).eval (u i))).natDegree :=
        Polynomial.card_roots' _
    _ = (g.onAxis i u).natDegree := Polynomial.natDegree_sub_C
    _ ≤ d := g.natDegree_onAxis_le i u

/-- **The pairs along which `g` does not change**: if `g` has a nonzero coefficient on a monomial
containing `Xᵢ`, then `g(u + t eᵢ) = g(u)` for at most `(n + 1) d q^n` of the pairs `(u, t)`. -/
theorem card_pairs_shift_eq_le {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}
    (g : LowIndDegPoly (F := F) (m := n) (d := d)) {i : Fin n} {e : Fin n → Fin (d + 1)}
    (he : g e ≠ 0) (hi : (e i : ℕ) ≠ 0) :
    ((univ.filter fun p : Point F n × F =>
        g.eval (p.1 + p.2 • Pi.single i 1) = g.eval p.1).card : ℝ) ≤
      (n + 1) * d * (Fintype.card F : ℝ) ^ n := by
  -- the coefficient vector `G` of the pattern `Xᵢ^(e i)` is nonzero, so by Schwartz--Zippel it
  -- vanishes at no more than `n d q^(n - 1)` points
  have hG : g.coef {i} (maskOn {i} e) ≠ 0 := fun h => he (by
    rw [← LowIndDegPoly.coef_maskOff g {i} e, h]
    rfl)
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hZ := card_eval_eq_zero_le hG
  rw [div_le_div_iff₀ (by positivity) hq] at hZ
  -- fibre by fibre over `u`: at most `d` pairs where `G(u) ≠ 0`, at most `q` where `G(u) = 0`
  have hfib : (univ.filter fun p : Point F n × F =>
      g.eval (p.1 + p.2 • Pi.single i 1) = g.eval p.1).card =
      ∑ u : Point F n,
        (univ.filter fun t : F => g.eval (u + t • Pi.single i 1) = g.eval u).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp only [Finset.card_filter]
  have hE : (univ.filter fun p : Point F n × F =>
      g.eval (p.1 + p.2 • Pi.single i 1) = g.eval p.1).card ≤
      Fintype.card F ^ n * d +
        (univ.filter fun u : Point F n => (g.coef {i} (maskOn {i} e)).eval u = 0).card *
          Fintype.card F := by
    rw [hfib]
    calc ∑ u : Point F n,
          (univ.filter fun t : F => g.eval (u + t • Pi.single i 1) = g.eval u).card
        ≤ ∑ u : Point F n,
            (d + if (g.coef {i} (maskOn {i} e)).eval u = 0 then Fintype.card F else 0) := by
          refine Finset.sum_le_sum fun u _ => ?_
          split_ifs with h
          · exact (Finset.card_filter_le _ _).trans
              (Finset.card_univ.trans_le (Nat.le_add_left _ _))
          · rw [add_zero]
            exact card_shift_eq_le g hi h
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
            ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Fintype.card_fun,
            Fintype.card_fin]
  have hE' : ((univ.filter fun p : Point F n × F =>
      g.eval (p.1 + p.2 • Pi.single i 1) = g.eval p.1).card : ℝ) ≤
      (Fintype.card F : ℝ) ^ n * d +
        ((univ.filter fun u : Point F n => (g.coef {i} (maskOn {i} e)).eval u = 0).card : ℝ) *
          Fintype.card F := by
    exact_mod_cast hE
  linarith

/-- **Shifts along an axis change a polynomial that depends on the axis variable**: if `g` has a
nonzero coefficient on a monomial containing `Xᵢ`, then `g(u + t eᵢ) ≠ g(u)` for at least
`q^n (q - (n + 1) d)` of the pairs `(u, t) ∈ F^n × F`. -/
theorem card_shift_ne_ge {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}
    (g : LowIndDegPoly (F := F) (m := n) (d := d)) {i : Fin n} {e : Fin n → Fin (d + 1)}
    (he : g e ≠ 0) (hi : (e i : ℕ) ≠ 0) :
    (Fintype.card F : ℝ) ^ n * ((Fintype.card F : ℝ) - (n + 1) * d) ≤
      ((univ.filter fun p : Point F n × F =>
        g.eval (p.1 + p.2 • Pi.single i 1) ≠ g.eval p.1).card : ℝ) := by
  -- the pairs along which `g` changes are the complement of those along which it does not
  have hcompl : ((univ.filter fun p : Point F n × F =>
      g.eval (p.1 + p.2 • Pi.single i 1) = g.eval p.1).card : ℝ) +
      ((univ.filter fun p : Point F n × F =>
        g.eval (p.1 + p.2 • Pi.single i 1) ≠ g.eval p.1).card : ℝ) =
      (Fintype.card F : ℝ) ^ n * Fintype.card F := by
    rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
  linarith [card_pairs_shift_eq_le g he hi]

end MIPRE.LIDT

end

end
