/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Products

/-!
# Linearity in the two combining coefficients (`lem:qld-global-linear`)

An outcome `g` of the global measurement is a polynomial on `F^{4m}`; read at the padded point
`u = (x, z, α, β, w)` it is a polynomial in `(α, β)` whose coefficients are polynomials in the other
coordinates. The good outcomes are those of the form `g = α g₁(x, z) + β g₂(x, z)`: linear in
`(α, β)` with no constant term and no other monomial. This file bounds the weight of the others
(`IsLinAB` fails) from the ordered-product estimate of `lem:qld-global-products` for the order
`X_a Z_b`.

## The polynomial side

`LowIndDegPoly.coef g T t` is the coefficient vector, in the variables outside `T`, of the
monomial pattern `t` on the coordinates `T` (`eval_eq_sum_coef`): `g(u) = ∑_t u^t_T · coef(u)`.
With `T = {aIdx, bIdx}` the patterns are pairs `(i, j)`, and `pAB g u₀` is the bivariate
polynomial `(α, β) ↦ g(setAB u₀ α β)` as a coefficient vector on `Fin 2` (`eval_pAB`). If `g` is
not of the good form, some coefficient `G_{i₀ j₀}` with `(i₀, j₀) ∉ {(1, 0), (0, 1)}` is a nonzero
polynomial, so by Schwartz--Zippel it vanishes at a uniform `u₀` with probability at most
`4md/q` (`sum_uniform_eval_eq_zero_le`); where it does not vanish, `pAB g u₀` differs from every
linear form `α a + β b` (`pAB_ne_linAB`), so they agree at a uniform `(α, β)` with probability at
most `2d/q` (`sum_agree_two_le`).

## The operator side

For `β ≠ 0` the fibre `{αa + βb = c}` has one `b` per `a`, so
`‖(G_g ⊗ ∑_{fibre} X_a Z_b) Φ‖² = ∑_{fibre} ‖(G_g ⊗ X_a Z_b) Φ‖²` (Pythagoras, the `X_a` being
orthogonal projectors), and the weights `W_g(a, b) = ‖(G_g ⊗ X_a Z_b) Φ‖²` do not depend on
`(α, β)` and sum to `⟨G_g⟩`. Averaging over `(α, β)` and then over the other coordinates
(`sum_uniform_setAB` reads the uniform padded point as a uniform base point with a fresh uniform
pair), an outcome that is not of the good form has `E_u ‖(G_g ⊗ B_u(g(u))) Φ‖² ≤ η ⟨G_g⟩` with
`η = (1 + 2d + 4md)/q` (`sum_uniform_snorm_sq_ordComb_le_of_not_isLinAB`). On the other hand
`⟨G_g⟩ ≤ 2 ‖(G_g ⊗ B_u) Φ‖² + 2 ‖(G_g ⊗ (1 - B_u)) Φ‖²` for every `u`, and the second terms are
what the product estimate bounds by `Δ` in total; hence
`(1 - 2η) · (weight of the bad outcomes) ≤ 2Δ` (`sum_bad_linear_mass_le`). This is the linear
bound the paper's `cnote` at `eq:qld-g-prime-bound` describes, rather than the displayed `√Δ`.
-/

noncomputable section

/-! ## Coefficients of a monomial pattern -/

namespace MIPRE.LIDT

open Finset

variable {F : Type*} [Field F] {n d : ℕ}

/-- The exponent vector `e` with its coordinates in `T` replaced by those of the pattern `t`. -/
def patch (T : Finset (Fin n)) (t e : Fin n → Fin (d + 1)) : Fin n → Fin (d + 1) :=
  fun k => if k ∈ T then t k else e k

/-- The part of an exponent vector on `T`. -/
def maskOn (T : Finset (Fin n)) (e : Fin n → Fin (d + 1)) : Fin n → Fin (d + 1) :=
  fun k => if k ∈ T then e k else 0

/-- The part of an exponent vector off `T`. -/
def maskOff (T : Finset (Fin n)) (e : Fin n → Fin (d + 1)) : Fin n → Fin (d + 1) :=
  fun k => if k ∈ T then 0 else e k

theorem patch_maskOn_maskOff (T : Finset (Fin n)) (e : Fin n → Fin (d + 1)) :
    patch T (maskOn T e) (maskOff T e) = e := by
  funext k
  simp only [patch, maskOn, maskOff]
  split_ifs <;> rfl

theorem maskOn_patch (T : Finset (Fin n)) (t e : Fin n → Fin (d + 1)) :
    maskOn T (patch T t e) = maskOn T t := by
  funext k
  simp only [maskOn, patch]
  split_ifs <;> rfl

theorem maskOff_patch (T : Finset (Fin n)) (t e : Fin n → Fin (d + 1)) :
    maskOff T (patch T t e) = maskOff T e := by
  funext k
  simp only [maskOff, patch]
  split_ifs <;> rfl

theorem maskOn_eq_self {T : Finset (Fin n)} {t : Fin n → Fin (d + 1)} (h : ∀ k ∉ T, t k = 0) :
    maskOn T t = t := by
  funext k
  simp only [maskOn]
  split_ifs with hk
  · rfl
  · exact (h k hk).symm

theorem maskOff_eq_self {T : Finset (Fin n)} {e : Fin n → Fin (d + 1)} (h : ∀ k ∈ T, e k = 0) :
    maskOff T e = e := by
  funext k
  simp only [maskOff]
  split_ifs with hk
  · exact (h k hk).symm
  · rfl

theorem maskOn_apply_of_not {T : Finset (Fin n)} (e : Fin n → Fin (d + 1)) {k : Fin n}
    (hk : k ∉ T) : maskOn T e k = 0 := if_neg hk

theorem maskOff_apply_of {T : Finset (Fin n)} (e : Fin n → Fin (d + 1)) {k : Fin n}
    (hk : k ∈ T) : maskOff T e k = 0 := if_pos hk

/-- **The coefficient of a monomial pattern**: the coefficient vector, in the variables outside
`T`, of the monomial `∏_{k ∈ T} u_k^{t k}` in `g`; zero unless the pattern is supported in `T`. -/
def LowIndDegPoly.coef (g : LowIndDegPoly (F := F) (m := n) (d := d)) (T : Finset (Fin n))
    (t : Fin n → Fin (d + 1)) : LowIndDegPoly (F := F) (m := n) (d := d) :=
  fun e => if (∀ k ∈ T, e k = 0) ∧ (∀ k ∉ T, t k = 0) then g (patch T t e) else 0

/-- The product of powers splits along `T`. -/
theorem prod_pow_patch (T : Finset (Fin n)) (u : Point F n) {t e : Fin n → Fin (d + 1)}
    (he : ∀ k ∈ T, e k = 0) :
    (∏ k ∈ T, u k ^ (t k : ℕ)) * ∏ k, u k ^ (e k : ℕ)
      = ∏ k, u k ^ ((patch T t e k : Fin (d + 1)) : ℕ) := by
  classical
  have h1 : ∏ k, u k ^ (e k : ℕ) = ∏ k ∈ univ.filter (fun k => k ∉ T), u k ^ (e k : ℕ) := by
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun k => k ∈ T)]
    rw [Finset.prod_eq_one fun k hk => by rw [he k (Finset.mem_filter.mp hk).2]; simp, one_mul]
  have h2 : ∏ k, u k ^ ((patch T t e k : Fin (d + 1)) : ℕ)
      = (∏ k ∈ univ.filter (fun k => k ∈ T), u k ^ (t k : ℕ))
        * ∏ k ∈ univ.filter (fun k => k ∉ T), u k ^ (e k : ℕ) := by
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun k => k ∈ T)]
    congr 1
    · exact Finset.prod_congr rfl fun k hk => by rw [patch, if_pos (Finset.mem_filter.mp hk).2]
    · exact Finset.prod_congr rfl fun k hk => by rw [patch, if_neg (Finset.mem_filter.mp hk).2]
  have hT : univ.filter (fun k : Fin n => k ∈ T) = T := by
    ext k
    simp
  rw [h1, h2, hT]

/-- **Decomposition along the patterns on `T`**: `g(u) = ∑_t u^t_T · (coef g T t)(u)`. -/
theorem LowIndDegPoly.eval_eq_sum_coef (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (T : Finset (Fin n)) (u : Point F n) :
    g.eval u = ∑ t : Fin n → Fin (d + 1), (∏ k ∈ T, u k ^ (t k : ℕ)) * (g.coef T t).eval u := by
  classical
  simp only [LowIndDegPoly.eval, LowIndDegPoly.coef, Finset.mul_sum]
  -- both sides as sums over pairs `(t, e)`
  have hterm : ∀ (t e : Fin n → Fin (d + 1)),
      (∏ k ∈ T, u k ^ (t k : ℕ))
          * ((if (∀ k ∈ T, e k = 0) ∧ (∀ k ∉ T, t k = 0) then g (patch T t e) else 0)
            * ∏ k, u k ^ (e k : ℕ))
        = if (∀ k ∈ T, e k = 0) ∧ (∀ k ∉ T, t k = 0) then
            g (patch T t e) * ∏ k, u k ^ ((patch T t e k : Fin (d + 1)) : ℕ) else 0 := by
    intro t e
    split_ifs with h
    · rw [← prod_pow_patch T u h.1]
      ring
    · simp
  simp_rw [hterm]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => patch T p.1 p.2) (fun _ _ _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro p₁ _ h₁ p₂ _ h₂ heq
    have hC₁ : (∀ k ∈ T, p₁.2 k = 0) ∧ (∀ k ∉ T, p₁.1 k = 0) := by
      by_contra hc
      exact h₁ (if_neg hc)
    have hC₂ : (∀ k ∈ T, p₂.2 k = 0) ∧ (∀ k ∉ T, p₂.1 k = 0) := by
      by_contra hc
      exact h₂ (if_neg hc)
    have hon := congrArg (maskOn T) heq
    have hoff := congrArg (maskOff T) heq
    rw [maskOn_patch, maskOn_patch, maskOn_eq_self hC₁.2, maskOn_eq_self hC₂.2] at hon
    rw [maskOff_patch, maskOff_patch, maskOff_eq_self hC₁.1, maskOff_eq_self hC₂.1] at hoff
    exact Prod.ext hon hoff
  · intro e _ he
    have hC : (∀ k ∈ T, maskOff T e k = 0) ∧ (∀ k ∉ T, maskOn T e k = 0) :=
      ⟨fun k hk => maskOff_apply_of e hk, fun k hk => maskOn_apply_of_not e hk⟩
    refine ⟨(maskOn T e, maskOff T e), Finset.mem_univ _, ?_, patch_maskOn_maskOff T e⟩
    rw [if_pos hC, patch_maskOn_maskOff]
    exact he
  · intro p _ hp
    have hC : (∀ k ∈ T, p.2 k = 0) ∧ (∀ k ∉ T, p.1 k = 0) := by
      by_contra hc
      exact hp (if_neg hc)
    rw [if_pos hC]

/-- A coefficient vector on `T` reads no coordinate in `T`. -/
theorem LowIndDegPoly.eval_coef_of_eq_off (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (T : Finset (Fin n)) (t : Fin n → Fin (d + 1)) {u u' : Point F n}
    (h : ∀ k ∉ T, u k = u' k) : (g.coef T t).eval u = (g.coef T t).eval u' := by
  classical
  simp only [LowIndDegPoly.eval, LowIndDegPoly.coef]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs with he
  · congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : k ∈ T
    · rw [he.1 k hk]
      simp
    · rw [h k hk]
  · simp

/-- A coefficient vector is nonzero where the polynomial has a nonzero coefficient with the
pattern. -/
theorem LowIndDegPoly.coef_maskOff (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (T : Finset (Fin n)) (e : Fin n → Fin (d + 1)) :
    g.coef T (maskOn T e) (maskOff T e) = g e := by
  rw [LowIndDegPoly.coef, if_pos ⟨fun k hk => maskOff_apply_of e hk,
    fun k hk => maskOn_apply_of_not e hk⟩, patch_maskOn_maskOff]

/-- **Schwartz--Zippel for a nonzero coefficient vector**: it vanishes at a uniform point with
probability at most `n d / q`. -/
theorem card_eval_eq_zero_le [Fintype F] [DecidableEq F]
    {G : LowIndDegPoly (F := F) (m := n) (d := d)} (hG : G ≠ 0) :
    ((univ.filter fun u : Point F n => G.eval u = 0).card : ℝ) / (Fintype.card F : ℝ) ^ n
      ≤ (n : ℝ) * d / Fintype.card F := by
  classical
  have hne : G.toMv ≠ 0 := by
    intro h
    apply hG
    funext e
    have := LowIndDegPoly.coeff_toMv G e
    rw [h, MvPolynomial.coeff_zero] at this
    exact this.symm
  have h := LowDegree.prob_agree_le_individualDegree hne (d := d) (LowIndDegPoly.degreeOf_toMv_le G)
    (fun i => by rw [MvPolynomial.degreeOf_zero]; exact Nat.zero_le _)
  have hcard : LowDegree.agree G.toMv 0 = univ.filter fun u : Point F n => G.eval u = 0 := by
    ext u
    simp [LowDegree.mem_agree, LowIndDegPoly.eval_toMv]
  rw [hcard] at h
  exact h

end MIPRE.LIDT

namespace MIPRE

open Matrix
open scoped ComplexOrder MatrixOrder

/-- A self-adjoint idempotent is positive semidefinite. -/
theorem posSemidef_of_proj {N : Type*} [Fintype N] {P : Matrix N N ℂ} (hsa : Pᴴ = P)
    (hidem : P * P = P) : P.PosSemidef := by
  have : P = Pᴴ * P := by rw [hsa, hidem]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem uniform_nonneg (X : Type*) [Fintype X] (x : X) : 0 ≤ uniform X x :=
  inv_nonneg.mpr (Nat.cast_nonneg _)

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## The polynomial in the two combining coefficients -/

section AB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-- The two combining coordinates. -/
def abSet : Finset (Fin (4 * m)) := {aIdx m, bIdx m}

omit [Field F] [Fintype F] [DecidableEq F] in
theorem mem_abSet {k : Fin (4 * m)} : k ∈ abSet ↔ k = aIdx m ∨ k = bIdx m := by
  simp [abSet]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem xIdx_notMem_abSet (i : Fin m) : xIdx m i ∉ abSet := by
  rw [mem_abSet]
  push Not
  exact ⟨xIdx_ne_aIdx i, xIdx_ne_bIdx i⟩

omit [Field F] [Fintype F] [DecidableEq F] in
theorem zIdx_notMem_abSet (i : Fin m) : zIdx m i ∉ abSet := by
  rw [mem_abSet]
  push Not
  exact ⟨zIdx_ne_aIdx i, zIdx_ne_bIdx i⟩

/-- The pattern with exponents `i` at `α` and `j` at `β`. -/
def patAB (i j : Fin (d + 1)) : Fin (4 * m) → Fin (d + 1) :=
  fun k => if k = aIdx m then i else if k = bIdx m then j else 0

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem patAB_aIdx (i j : Fin (d + 1)) : patAB (m := m) i j (aIdx m) = i := if_pos rfl

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem patAB_bIdx (i j : Fin (d + 1)) : patAB (m := m) i j (bIdx m) = j := by
  rw [patAB, if_neg aIdx_ne_bIdx.symm, if_pos rfl]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem patAB_of_notMem (i j : Fin (d + 1)) {k : Fin (4 * m)} (hk : k ∉ abSet) :
    patAB (m := m) i j k = 0 := by
  rw [mem_abSet] at hk
  push Not at hk
  rw [patAB, if_neg hk.1, if_neg hk.2]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem patAB_injective : Function.Injective fun t2 : Fin 2 → Fin (d + 1) =>
    patAB (m := m) (t2 0) (t2 1) := by
  intro s s' h
  have h0 := congrArg (fun t => t (aIdx m)) h
  have h1 := congrArg (fun t => t (bIdx m)) h
  simp only [patAB_aIdx, patAB_bIdx] at h0 h1
  funext k
  fin_cases k
  · exact h0
  · exact h1

/-- **The outcome read at `(α, β)`**, with the other coordinates fixed at those of `u₀`: a
polynomial in two variables, as a coefficient vector. -/
def pAB (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) (u₀ : Point F (4 * m)) :
    LowIndDegPoly (F := F) (m := 2) (d := d) :=
  fun t2 => (g.coef abSet (patAB (t2 0) (t2 1))).eval u₀

omit [Fintype F] [DecidableEq F] in
/-- The coefficient vectors on `abSet` do not read `α, β`. -/
theorem eval_coef_abSet_setAB (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d))
    (t : Fin (4 * m) → Fin (d + 1)) (u₀ : Point F (4 * m)) (α β : F) :
    (g.coef abSet t).eval (setAB u₀ α β) = (g.coef abSet t).eval u₀ := by
  refine LowIndDegPoly.eval_coef_of_eq_off g abSet t fun k hk => ?_
  rw [mem_abSet] at hk
  push Not at hk
  simp only [setAB]
  rw [Function.update_of_ne hk.2, Function.update_of_ne hk.1]

omit [Fintype F] [DecidableEq F] in
/-- **`pAB g u₀` evaluated at `(α, β)` is `g` at `setAB u₀ α β`.** -/
theorem eval_pAB (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) (u₀ : Point F (4 * m))
    (α β : F) : (pAB g u₀).eval ![α, β] = g.eval (setAB u₀ α β) := by
  classical
  rw [LowIndDegPoly.eval_eq_sum_coef g abSet (setAB u₀ α β)]
  have hprod : ∀ t : Fin (4 * m) → Fin (d + 1),
      ∏ k ∈ abSet, setAB u₀ α β k ^ (t k : ℕ) = α ^ (t (aIdx m) : ℕ) * β ^ (t (bIdx m) : ℕ) := by
    intro t
    rw [abSet, Finset.prod_pair aIdx_ne_bIdx]
    show alph (setAB u₀ α β) ^ _ * bet (setAB u₀ α β) ^ _ = _
    rw [alph_setAB, bet_setAB]
  simp_rw [hprod, eval_coef_abSet_setAB]
  -- the unsupported patterns contribute nothing; the supported ones are the `patAB`
  rw [← Finset.sum_subset (Finset.subset_univ
      (Finset.image (fun t2 : Fin 2 → Fin (d + 1) => patAB (m := m) (t2 0) (t2 1)) univ))
    (fun t _ ht => ?_), Finset.sum_image (fun s _ s' _ h => patAB_injective h)]
  · show (∑ t2 : Fin 2 → Fin (d + 1), pAB g u₀ t2 * ∏ i, ![α, β] i ^ (t2 i : ℕ)) = _
    refine Finset.sum_congr rfl fun t2 _ => ?_
    simp only [pAB, patAB_aIdx, patAB_bIdx, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  · -- `t` is not a `patAB`: some coordinate off `abSet` is nonzero, so the coefficient vanishes
    have hns : ¬ ∀ k ∉ abSet, t k = 0 := by
      intro hsupp
      apply ht
      rw [Finset.mem_image]
      refine ⟨![t (aIdx m), t (bIdx m)], Finset.mem_univ _, ?_⟩
      funext k
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      by_cases hk : k ∈ abSet
      · rw [mem_abSet] at hk
        rcases hk with rfl | rfl
        · exact patAB_aIdx _ _
        · exact patAB_bIdx _ _
      · rw [patAB_of_notMem _ _ hk, hsupp k hk]
    have hzero : (g.coef abSet t).eval u₀ = 0 := by
      unfold LowIndDegPoly.eval LowIndDegPoly.coef
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [if_neg fun h => hns h.2, zero_mul]
    rw [hzero, mul_zero]

end AB

/-! ## Linear forms in the two combining coefficients -/

section Lin

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}

omit [Field F] [Fintype F] [DecidableEq F] in
theorem vec_two_eq {α : Type*} (v : Fin 2 → α) : ![v 0, v 1] = v := by
  funext i
  fin_cases i <;> rfl

/-- Pairs as functions on two indices. -/
def fin2Equiv (α : Type*) : (Fin 2 → α) ≃ α × α where
  toFun v := (v 0, v 1)
  invFun p := ![p.1, p.2]
  left_inv v := vec_two_eq v
  right_inv _ := rfl

/-- The pattern `α^1 β^0`. -/
def e10 (hd : 1 ≤ d) : Fin 2 → Fin (d + 1) := ![⟨1, Nat.lt_succ_of_le hd⟩, 0]

/-- The pattern `α^0 β^1`. -/
def e01 (hd : 1 ≤ d) : Fin 2 → Fin (d + 1) := ![0, ⟨1, Nat.lt_succ_of_le hd⟩]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem e10_ne_e01 (hd : 1 ≤ d) : e10 hd ≠ e01 hd := by
  intro h
  have := congrArg (fun t => (t 0 : ℕ)) h
  simp [e10, e01] at this

/-- **The linear form `α a + β b`**, as a coefficient vector on two variables. -/
def linAB (hd : 1 ≤ d) (a b : F) : LowIndDegPoly (F := F) (m := 2) (d := d) :=
  fun t2 => if t2 = e10 hd then a else if t2 = e01 hd then b else 0

omit [Fintype F] [DecidableEq F] in
theorem eval_linAB (hd : 1 ≤ d) (a b α β : F) :
    (linAB hd a b).eval ![α, β] = α * a + β * b := by
  classical
  unfold LowIndDegPoly.eval linAB
  have hterm : ∀ t2 : Fin 2 → Fin (d + 1),
      (if t2 = e10 hd then a else if t2 = e01 hd then b else 0) * ∏ i, ![α, β] i ^ (t2 i : ℕ)
        = (if t2 = e10 hd then a * ∏ i, ![α, β] i ^ (t2 i : ℕ) else 0)
          + (if t2 = e01 hd then b * ∏ i, ![α, β] i ^ (t2 i : ℕ) else 0) := by
    intro t2
    by_cases h1 : t2 = e10 hd
    · have h2 : t2 ≠ e01 hd := by
        rw [h1]
        exact e10_ne_e01 hd
      simp only [if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : t2 = e01 hd
      · simp only [if_neg h1, if_pos h2, zero_add]
      · simp only [if_neg h1, if_neg h2, zero_mul, add_zero]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' univ (e10 hd), Finset.sum_ite_eq' univ (e01 hd),
    if_pos (mem_univ _), if_pos (mem_univ _)]
  simp only [e10, e01, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_mk,
    Fin.val_zero, pow_one, pow_zero, mul_one]
  ring

/-- **Schwartz--Zippel on two variables**: two different coefficient vectors agree at a uniform
pair with probability at most `2d/q`. -/
theorem sum_agree_two_le {p q : LowIndDegPoly (F := F) (m := 2) (d := d)} (hpq : p ≠ q) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * (if p.eval ![ab.1, ab.2] = q.eval ![ab.1, ab.2] then (1 : ℝ) else 0)
      ≤ 2 * d / Fintype.card F := by
  have hne : p.toMv ≠ q.toMv := fun h => hpq (funext fun e => by
    rw [← LowIndDegPoly.coeff_toMv p e, ← LowIndDegPoly.coeff_toMv q e, h])
  have h := LowDegree.prob_agreeOn_le_individualDegree hne (d := d)
    (LowIndDegPoly.degreeOf_toMv_le p) (LowIndDegPoly.degreeOf_toMv_le q)
  rw [Fintype.card_fin] at h
  have hcard : (LowDegree.agreeOn p.toMv q.toMv).card
      = (univ.filter fun ab : F × F => p.eval ![ab.1, ab.2] = q.eval ![ab.1, ab.2]).card := by
    refine Finset.card_equiv (fin2Equiv F) fun v => ?_
    rw [LowDegree.mem_agreeOn, mem_filter, LowIndDegPoly.eval_toMv, LowIndDegPoly.eval_toMv]
    have hv : fin2Equiv F v = (v 0, v 1) := rfl
    rw [hv]
    simp only [mem_univ, true_and]
    rw [vec_two_eq v]
  rw [← Finset.mul_sum, Finset.sum_boole, ← hcard]
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have : ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
      * ((LowDegree.agreeOn p.toMv q.toMv).card : ℝ)
      = ((LowDegree.agreeOn p.toMv q.toMv).card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
    field_simp
  rw [this]
  push_cast at h
  exact h

end Lin

/-! ## The linear outcomes and the two probability bounds -/

section LinAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-- **Linear in `(α, β)`**: every monomial of `g` has exponents `(1, 0)` or `(0, 1)` on the two
combining coordinates, so `g = α g₁ + β g₂` with `g₁`, `g₂` not reading `α, β`. -/
def IsLinAB (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) : Prop :=
  ∀ e : Fin (4 * m) → Fin (d + 1),
    ¬ (((e (aIdx m) : ℕ) = 1 ∧ (e (bIdx m) : ℕ) = 0)
      ∨ ((e (aIdx m) : ℕ) = 0 ∧ (e (bIdx m) : ℕ) = 1)) → g e = 0

instance : DecidablePred (IsLinAB (F := F) (m := m) (d := d)) := fun g =>
  inferInstanceAs (Decidable (∀ e : Fin (4 * m) → Fin (d + 1),
    ¬ (((e (aIdx m) : ℕ) = 1 ∧ (e (bIdx m) : ℕ) = 0)
      ∨ ((e (aIdx m) : ℕ) = 0 ∧ (e (bIdx m) : ℕ) = 1)) → g e = 0))

omit [Field F] [Fintype F] [DecidableEq F] in
theorem patAB_eq_maskOn (e : Fin (4 * m) → Fin (d + 1)) :
    patAB (e (aIdx m)) (e (bIdx m)) = maskOn abSet e := by
  funext k
  simp only [patAB, maskOn]
  by_cases ha : k = aIdx m
  · subst ha
    simp [mem_abSet]
  · by_cases hb : k = bIdx m
    · subst hb
      simp [ha, mem_abSet]
    · simp [ha, hb, mem_abSet]

omit [Fintype F] [DecidableEq F] in
/-- An outcome that is not linear in `(α, β)` has a nonzero coefficient vector at a non-linear
pattern. -/
theorem exists_bad_coef {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : ¬ IsLinAB g) :
    ∃ e₀ : Fin (4 * m) → Fin (d + 1),
      ¬ (((e₀ (aIdx m) : ℕ) = 1 ∧ (e₀ (bIdx m) : ℕ) = 0)
        ∨ ((e₀ (aIdx m) : ℕ) = 0 ∧ (e₀ (bIdx m) : ℕ) = 1))
      ∧ g.coef abSet (patAB (e₀ (aIdx m)) (e₀ (bIdx m))) ≠ 0 := by
  unfold IsLinAB at hg
  obtain ⟨e₀, h⟩ := not_forall.mp hg
  obtain ⟨hpat, hne⟩ := Classical.not_imp.mp h
  refine ⟨e₀, hpat, fun h => hne ?_⟩
  have := congrArg (fun G : LowIndDegPoly (F := F) (m := 4 * m) (d := d) =>
    G (maskOff abSet e₀)) h
  simp only [patAB_eq_maskOn, LowIndDegPoly.coef_maskOff, Pi.zero_apply] at this
  exact this

omit [Fintype F] [DecidableEq F] in
/-- Where a non-linear coefficient does not vanish, the outcome read at `(α, β)` differs from every
linear form. -/
theorem pAB_ne_linAB (hd : 1 ≤ d) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    {e₀ : Fin (4 * m) → Fin (d + 1)}
    (hpat : ¬ (((e₀ (aIdx m) : ℕ) = 1 ∧ (e₀ (bIdx m) : ℕ) = 0)
      ∨ ((e₀ (aIdx m) : ℕ) = 0 ∧ (e₀ (bIdx m) : ℕ) = 1)))
    {u₀ : Point F (4 * m)} (hu : (g.coef abSet (patAB (e₀ (aIdx m)) (e₀ (bIdx m)))).eval u₀ ≠ 0)
    (a b : F) : pAB g u₀ ≠ linAB hd a b := by
  intro h
  have := congrArg (fun p : LowIndDegPoly (F := F) (m := 2) (d := d) =>
    p ![e₀ (aIdx m), e₀ (bIdx m)]) h
  simp only [pAB, linAB, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  have h10 : (![e₀ (aIdx m), e₀ (bIdx m)] : Fin 2 → Fin (d + 1)) ≠ e10 hd := by
    intro h'
    apply hpat
    left
    have h0 : (e₀ (aIdx m) : ℕ) = 1 := by
      simpa [e10] using congrArg (fun t => (t 0 : ℕ)) h'
    have h1 : (e₀ (bIdx m) : ℕ) = 0 := by
      simpa [e10] using congrArg (fun t => (t 1 : ℕ)) h'
    exact ⟨h0, h1⟩
  have h01 : (![e₀ (aIdx m), e₀ (bIdx m)] : Fin 2 → Fin (d + 1)) ≠ e01 hd := by
    intro h'
    apply hpat
    right
    have h0 : (e₀ (aIdx m) : ℕ) = 0 := by
      simpa [e01] using congrArg (fun t => (t 0 : ℕ)) h'
    have h1 : (e₀ (bIdx m) : ℕ) = 1 := by
      simpa [e01] using congrArg (fun t => (t 1 : ℕ)) h'
    exact ⟨h0, h1⟩
  rw [if_neg h10, if_neg h01] at this
  exact hu this

omit [NeZero m] in
/-- **The bad base points**: a nonzero coefficient vector vanishes at a uniform padded point with
probability at most `4md/q`. -/
theorem sum_uniform_eval_eq_zero_le {G : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hG : G ≠ 0) :
    ∑ u : Point F (4 * m), uniform (Point F (4 * m)) u * (if G.eval u = 0 then (1 : ℝ) else 0)
      ≤ 4 * m * d / Fintype.card F := by
  have h := card_eval_eq_zero_le hG
  simp only [uniform]
  rw [← Finset.mul_sum, Finset.sum_boole, Fintype.card_fun, Fintype.card_fin]
  push_cast at h ⊢
  rw [inv_mul_eq_div]
  exact h

end LinAB

/-! ## The operator side: the fibre weights -/

section Weights

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {RA RB : Type*} [Fintype RA]
  [DecidableEq RA] [Fintype RB] [DecidableEq RB]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem bOp_mul_aOp_comm (U : Matrix RA RA ℂ) (V : Matrix RB RB ℂ) :
    (bOp V : Matrix (RA × RB) _ ℂ) * aOp U = aOp U * bOp V := by
  rw [aOp_mul_bOp_eq, bOp, aOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

variable {X' Z' : F → Matrix RB RB ℂ}

omit [Field F] in
/-- **The weights sum to the outcome's mass**: `∑_{a,b} ‖(S ⊗ X_a Z_b) Φ‖² = ⟨S ⊗ 1⟩`. -/
theorem sum_snorm_sq_ordXZ_eq (Φ : RA × RB → ℂ) {S : Matrix RA RA ℂ} (hsa : Sᴴ = S)
    (hidem : S * S = S) (hX : IsPVM X') (hZ : IsPVM Z') :
    ∑ p : F × F, snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' p.1 * Z' p.2)) ^ 2
      = bornProb Φ S 1 := by
  simp_rw [snorm_sq_aOp_mul_bOp Φ hsa hidem, ← sand_eq_gram hX hZ]
  rw [← bornProb_sum_right, sum_sand hX hZ]

/-- The fibre `{αa + βb = c}` parametrized by `a`, for `β ≠ 0`. -/
def fibMap (α β c a : F) : F × F := (a, (c - α * a) * β⁻¹)

omit [Fintype F] [DecidableEq F] in
theorem fibMap_injective (α β c : F) : Function.Injective (fibMap α β c) :=
  fun _ _ h => congrArg Prod.fst h

theorem fiber_eq_image {α β c : F} (hβ : β ≠ 0) :
    (univ.filter fun p : F × F => α * p.1 + β * p.2 = c) = univ.image (fibMap α β c) := by
  ext p
  simp only [mem_filter, mem_univ, true_and, mem_image, fibMap]
  constructor
  · intro h
    refine ⟨p.1, Prod.ext rfl ?_⟩
    show (c - α * p.1) * β⁻¹ = p.2
    field_simp
    linear_combination -h
  · rintro ⟨a, rfl⟩
    show α * a + β * ((c - α * a) * β⁻¹) = c
    field_simp
    ring

/-- **Pythagoras on the fibre**: for `β ≠ 0` the fibre has one `b` per `a`, and the `X_a` are
orthogonal projectors. -/
theorem snorm_sq_ordComb_ordXZ_of_ne (Φ : RA × RB → ℂ) (S : Matrix RA RA ℂ) (hX : IsPVM X')
    {α β c : F} (hβ : β ≠ 0) :
    snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (ptComb (ordXZ X' Z') α β c)) ^ 2
      = ∑ p ∈ univ.filter (fun p : F × F => α * p.1 + β * p.2 = c),
          snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' p.1 * Z' p.2)) ^ 2 := by
  rw [ptComb, fiber_eq_image hβ, Finset.sum_image fun a _ a' _ h => fibMap_injective α β c h,
    Finset.sum_image fun a _ a' _ h => fibMap_injective α β c h]
  have hrw : (aOp S : Matrix (RA × RB) _ ℂ) * bOp (∑ a, ordXZ X' Z' (fibMap α β c a))
      = ∑ a, (bOp (X' a) : Matrix (RA × RB) _ ℂ) * (aOp S * bOp (Z' ((c - α * a) * β⁻¹))) := by
    rw [bOp_sum, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [ordXZ, fibMap]
    rw [bOp_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, bOp_mul_aOp_comm]
  rw [hrw, snorm_sq_sum_proj_mul Φ (fun a => by rw [bOp_conjTranspose, hX.isSelfAdjoint])
    (fun a a' h => by rw [← bOp_mul, hX.orthogonal h, bOp_zero]) _ univ]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [fibMap]
  rw [← Matrix.mul_assoc, bOp_mul_aOp_comm, Matrix.mul_assoc, ← bOp_mul]

/-- For `β = 0` the combination is a sub-sum of `X`. -/
theorem ordComb_ordXZ_bet_zero (hZ : IsPVM Z') (α c : F) :
    ptComb (ordXZ X' Z') α 0 c = fibSum X' (fun a => α * a) c := by
  rw [ptComb, fibSum]
  have hset : (univ.filter fun p : F × F => α * p.1 + 0 * p.2 = c)
      = (univ.filter fun a => α * a = c) ×ˢ univ := by
    ext p
    simp [Finset.mem_product]
  rw [hset, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [ordXZ]
  rw [← Matrix.mul_sum, hZ.sum_eq_one, Matrix.mul_one]

/-- **The combination is a contraction**: `‖(S ⊗ B) Φ‖² ≤ ⟨S ⊗ 1⟩` for every `(α, β, c)`. -/
theorem snorm_sq_ordComb_ordXZ_le (Φ : RA × RB → ℂ) {S : Matrix RA RA ℂ} (hsa : Sᴴ = S)
    (hidem : S * S = S) (hX : IsPVM X') (hZ : IsPVM Z') (α β c : F) :
    snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (ptComb (ordXZ X' Z') α β c)) ^ 2
      ≤ bornProb Φ S 1 := by
  by_cases hβ : β = 0
  · subst hβ
    rw [ordComb_ordXZ_bet_zero hZ, snorm_sq_aOp_mul_bOp Φ hsa hidem]
    have hP := isPVM_fibSum hX (fun a => α * a)
    rw [hP.isSelfAdjoint c, hP.idem c]
    exact bornProb_mono_right Φ (posSemidef_of_proj hsa hidem)
      (proj_le_one (hP.isSelfAdjoint c) (hP.idem c))
  · rw [snorm_sq_ordComb_ordXZ_of_ne Φ S hX hβ, ← sum_snorm_sq_ordXZ_eq Φ hsa hidem hX hZ]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => sq_nonneg _

/-- The pairs with `β = 0` number `q`. -/
theorem card_filter_snd_eq_zero :
    (univ.filter fun ab : F × F => ab.2 = 0).card = Fintype.card F := by
  have : (univ.filter fun ab : F × F => ab.2 = 0) = (univ : Finset F) ×ˢ ({0} : Finset F) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_univ, true_and, Finset.mem_product, Finset.mem_singleton]
  rw [this, Finset.card_product, Finset.card_univ, Finset.card_singleton, mul_one]

/-- **The fibre weights over `β ≠ 0`, exchanged**: each pair `(a, b)` is counted once for every
`(α, β)` that puts it on the sampled fibre `{αa + βb = v(α, β)}`. -/
theorem sum_filter_snorm_sq_ordComb_eq (Φ : RA × RB → ℂ) (S : Matrix RA RA ℂ) (hX : IsPVM X')
    (v : F × F → F) :
    ∑ ab ∈ univ.filter (fun ab : F × F => ¬ ab.2 = 0),
        snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (ptComb (ordXZ X' Z') ab.1 ab.2 (v ab))) ^ 2
      = ∑ p : F × F, ∑ ab ∈ univ.filter (fun ab : F × F => ¬ ab.2 = 0),
          (if ab.1 * p.1 + ab.2 * p.2 = v ab then (1 : ℝ) else 0)
            * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' p.1 * Z' p.2)) ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ab hab => ?_
  rw [snorm_sq_ordComb_ordXZ_of_ne Φ S hX (mem_filter.mp hab).2, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

end Weights

/-! ## Reading a padded point as a base point and a fresh combining pair -/

section Reparam

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]

omit [Field F] [DecidableEq F] in
/-- The map `(u₀, α, β) ↦ setAB u₀ α β` is `q²`-to-one. -/
theorem sum_setAB (f : Point F (4 * m) → ℝ) :
    ∑ u₀ : Point F (4 * m), ∑ ab : F × F, f (setAB u₀ ab.1 ab.2)
      = ((Fintype.card F : ℝ) * Fintype.card F) * ∑ u : Point F (4 * m), f u := by
  have h := Equiv.sum_comp abSwap (fun p : Point F (4 * m) × F × F => f p.1)
  simp only [abSwap, Equiv.coe_fn_mk] at h
  rw [← Fintype.sum_prod_type', h, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul]
  rw [Finset.mul_sum]

omit [DecidableEq F] in
/-- **The uniform padded point is a uniform base point with a fresh uniform combining pair.** -/
theorem sum_uniform_setAB (f : Point F (4 * m) → ℝ) :
    ∑ u, uniform (Point F (4 * m)) u * f u
      = ∑ u₀, uniform (Point F (4 * m)) u₀
          * ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
            * f (setAB u₀ ab.1 ab.2) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [uniform, ← Finset.mul_sum]
  rw [sum_setAB, ← mul_assoc ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹),
    show ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
      * ((Fintype.card F : ℝ) * Fintype.card F) = 1 by field_simp, one_mul]

end Reparam

/-! ## The two averages and the assembly -/

section Good

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m] {RA RB : Type*}
  [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]

/-- **A good base point**: where a non-linear coefficient of `g` does not vanish, the average over
the combining pair `(α, β)` of `‖(S ⊗ B_{α,β}(g(setAB u₀ α β))) Φ‖²` is at most
`(1 + 2d)/q · ⟨S ⊗ 1⟩`: the pairs with `β = 0` contribute `1/q`, and for `β ≠ 0` each weight
`W(a, b)` is counted with the probability, at most `2d/q`, that `(α, β)` puts `(a, b)` on the
sampled fibre. -/
theorem sum_ab_snorm_sq_ordComb_le_of_good {X' Z' : F → Matrix RB RB ℂ} (hd : 1 ≤ d)
    (Φ : RA × RB → ℂ) {S : Matrix RA RA ℂ} (hsa : Sᴴ = S) (hidem : S * S = S) (hX : IsPVM X')
    (hZ : IsPVM Z') {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    {e₀ : Fin (4 * m) → Fin (d + 1)}
    (hpat : ¬ (((e₀ (aIdx m) : ℕ) = 1 ∧ (e₀ (bIdx m) : ℕ) = 0)
      ∨ ((e₀ (aIdx m) : ℕ) = 0 ∧ (e₀ (bIdx m) : ℕ) = 1)))
    {u₀ : Point F (4 * m)} (hu : (g.coef abSet (patAB (e₀ (aIdx m)) (e₀ (bIdx m)))).eval u₀ ≠ 0) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ)
          * bOp (ptComb (ordXZ X' Z') ab.1 ab.2 ((pAB g u₀).eval ![ab.1, ab.2]))) ^ 2
      ≤ (1 + 2 * d) / Fintype.card F * bornProb Φ S 1 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hq0 : (0 : ℝ) ≤ (Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹ := by positivity
  have hwsum := sum_snorm_sq_ordXZ_eq Φ hsa hidem hX hZ
  have hW0 : 0 ≤ bornProb Φ S 1 := by
    rw [← hwsum]
    exact Finset.sum_nonneg fun p _ => sq_nonneg _
  have hagree : ∀ p : F × F, ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
      * (if ab.1 * p.1 + ab.2 * p.2 = (pAB g u₀).eval ![ab.1, ab.2] then (1 : ℝ) else 0)
      ≤ 2 * d / Fintype.card F := fun p => by
    have h := sum_agree_two_le (pAB_ne_linAB hd hpat hu p.1 p.2).symm
    simpa only [eval_linAB] using h
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun ab : F × F => ab.2 = 0)]
  have h0 : ∑ ab ∈ univ.filter (fun ab : F × F => ab.2 = 0),
      ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ)
          * bOp (ptComb (ordXZ X' Z') ab.1 ab.2 ((pAB g u₀).eval ![ab.1, ab.2]))) ^ 2
      ≤ 1 / Fintype.card F * bornProb Φ S 1 := by
    calc _ ≤ ∑ ab ∈ univ.filter (fun ab : F × F => ab.2 = 0),
          ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) * bornProb Φ S 1 :=
          Finset.sum_le_sum fun ab _ => mul_le_mul_of_nonneg_left
            (snorm_sq_ordComb_ordXZ_le Φ hsa hidem hX hZ _ _ _) hq0
      _ = 1 / Fintype.card F * bornProb Φ S 1 := by
          rw [Finset.sum_const, card_filter_snd_eq_zero, nsmul_eq_mul]
          field_simp
  have h1 : ∑ ab ∈ univ.filter (fun ab : F × F => ¬ ab.2 = 0),
      ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ)
          * bOp (ptComb (ordXZ X' Z') ab.1 ab.2 ((pAB g u₀).eval ![ab.1, ab.2]))) ^ 2
      ≤ 2 * d / Fintype.card F * bornProb Φ S 1 := by
    rw [← Finset.mul_sum, sum_filter_snorm_sq_ordComb_eq Φ S hX]
    calc _ ≤ ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, ∑ ab : F × F,
            (if ab.1 * p.1 + ab.2 * p.2 = (pAB g u₀).eval ![ab.1, ab.2] then (1 : ℝ) else 0)
              * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' p.1 * Z' p.2)) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ =>
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun ab _ _ =>
              mul_nonneg (by split_ifs <;> norm_num) (sq_nonneg _)) hq0
      _ = ∑ p : F × F, (∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
            * (if ab.1 * p.1 + ab.2 * p.2 = (pAB g u₀).eval ![ab.1, ab.2] then (1 : ℝ) else 0))
              * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' p.1 * Z' p.2)) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ab _ => ?_
          ring
      _ ≤ ∑ p : F × F, (2 * d / Fintype.card F)
            * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' p.1 * Z' p.2)) ^ 2 :=
          Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hagree p) (sq_nonneg _)
      _ = 2 * d / Fintype.card F * bornProb Φ S 1 := by rw [← Finset.mul_sum, hwsum]
  calc _ ≤ 1 / Fintype.card F * bornProb Φ S 1 + 2 * d / Fintype.card F * bornProb Φ S 1 :=
        add_le_add h0 h1
    _ = (1 + 2 * d) / Fintype.card F * bornProb Φ S 1 := by ring

variable {X Z : Point F m → F → Matrix RB RB ℂ}

/-- **A bad outcome carries little of its own weight through `B_u`**: if `g` is not linear in
`(α, β)`, then `E_u ‖(S ⊗ B_u(g(u))) Φ‖² ≤ (1 + 2d + 4md)/q · ⟨S ⊗ 1⟩`, the `4md/q` being the
probability that the witnessing non-linear coefficient vanishes at the base point. -/
theorem sum_uniform_snorm_sq_ordComb_le_of_not_isLinAB (hd : 1 ≤ d) (Φ : RA × RB → ℂ)
    {S : Matrix RA RA ℂ} (hsa : Sᴴ = S) (hidem : S * S = S) (hX : ∀ x, IsPVM (X x))
    (hZ : ∀ z, IsPVM (Z z)) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hg : ¬ IsLinAB g) :
    ∑ u, uniform (Point F (4 * m)) u
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordXZ X Z u (g.eval u))) ^ 2
      ≤ (1 + 2 * d + 4 * m * d) / Fintype.card F * bornProb Φ S 1 := by
  obtain ⟨e₀, hpat, hcoef⟩ := exists_bad_coef hg
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hq0 : (0 : ℝ) ≤ (Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹ := by positivity
  have hW0 : 0 ≤ bornProb Φ S 1 :=
    bornProb_nonneg Φ (posSemidef_of_proj hsa hidem) Matrix.PosSemidef.one
  have hη0 : (0 : ℝ) ≤ (1 + 2 * d) / Fintype.card F := by positivity
  rw [sum_uniform_setAB]
  have hinner : ∀ u₀ : Point F (4 * m),
      ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordXZ X Z (setAB u₀ ab.1 ab.2)
          (g.eval (setAB u₀ ab.1 ab.2)))) ^ 2
      ≤ ((if (g.coef abSet (patAB (e₀ (aIdx m)) (e₀ (bIdx m)))).eval u₀ = 0 then (1 : ℝ) else 0)
          + (1 + 2 * d) / Fintype.card F) * bornProb Φ S 1 := by
    intro u₀
    have hre : ∀ ab : F × F, ordComb ordXZ X Z (setAB u₀ ab.1 ab.2) (g.eval (setAB u₀ ab.1 ab.2))
        = ptComb (ordXZ (X (xBlk u₀)) (Z (zBlk u₀))) ab.1 ab.2 ((pAB g u₀).eval ![ab.1, ab.2]) :=
      fun ab => by rw [ordComb, xBlk_setAB, zBlk_setAB, alph_setAB, bet_setAB, eval_pAB]
    simp only [hre]
    split_ifs with h0
    · calc _ ≤ ∑ _ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
            * bornProb Φ S 1 :=
            Finset.sum_le_sum fun ab _ => mul_le_mul_of_nonneg_left
              (snorm_sq_ordComb_ordXZ_le Φ hsa hidem (hX _) (hZ _) _ _ _) hq0
        _ = 1 * bornProb Φ S 1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
            push_cast
            field_simp
        _ ≤ (1 + (1 + 2 * d) / Fintype.card F) * bornProb Φ S 1 :=
            mul_le_mul_of_nonneg_right (by linarith) hW0
    · rw [zero_add]
      exact sum_ab_snorm_sq_ordComb_le_of_good hd Φ hsa hidem (hX _) (hZ _) hpat h0
  calc _ ≤ ∑ u₀, uniform (Point F (4 * m)) u₀
        * (((if (g.coef abSet (patAB (e₀ (aIdx m)) (e₀ (bIdx m)))).eval u₀ = 0 then (1 : ℝ)
          else 0) + (1 + 2 * d) / Fintype.card F) * bornProb Φ S 1) :=
        Finset.sum_le_sum fun u₀ _ => mul_le_mul_of_nonneg_left (hinner u₀) (uniform_nonneg _ _)
    _ = (∑ u₀, uniform (Point F (4 * m)) u₀
          * (if (g.coef abSet (patAB (e₀ (aIdx m)) (e₀ (bIdx m)))).eval u₀ = 0 then (1 : ℝ)
            else 0)) * bornProb Φ S 1
        + (1 + 2 * d) / Fintype.card F * (∑ u₀, uniform (Point F (4 * m)) u₀)
          * bornProb Φ S 1 := by
        rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun u₀ _ => by ring
    _ ≤ 4 * m * d / Fintype.card F * bornProb Φ S 1
        + (1 + 2 * d) / Fintype.card F * 1 * bornProb Φ S 1 := by
        rw [sum_uniform_eq_one]
        exact add_le_add (mul_le_mul_of_nonneg_right (sum_uniform_eval_eq_zero_le hcoef) hW0)
          le_rfl
    _ = (1 + 2 * d + 4 * m * d) / Fintype.card F * bornProb Φ S 1 := by ring

/-- **`lem:qld-global-linear`, abstract form.** If the global measurement `G` satisfies the
`X_a Z_b` products estimate `∑_g E_u ‖(G_g ⊗ (1 - B_u(g(u)))) Φ‖² ≤ Δ`, then the outcomes that
are not linear in the combining coordinates `(α, β)` have total weight
`W ≤ 2Δ / (1 - 2η)`, `η = (1 + 2d + 4md)/q`: for each of them
`⟨G_g⟩ ≤ 2 ‖(G_g ⊗ B_u) Φ‖² + 2 ‖(G_g ⊗ (1 - B_u)) Φ‖²`, and the first term averages to at most
`2η ⟨G_g⟩`. -/
theorem sum_bad_linear_mass_le (hd : 1 ≤ d) (Φ : RA × RB → ℂ)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z)) {Δ : ℝ}
    (hprod : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2
      ≤ Δ) :
    (1 - 2 * ((1 + 2 * d + 4 * m * d) / Fintype.card F))
        * ∑ g ∈ univ.filter (fun g => ¬ IsLinAB g), bornProb Φ (G.M () g) 1 ≤ 2 * Δ := by
  have hsa : ∀ g, (G.M () g)ᴴ = G.M () g := fun g => G.selfAdjoint () g
  have hidem : ∀ g, G.M () g * G.M () g = G.M () g := fun g => G.projective () g
  have hbad : ∀ g : LowIndDegPoly (F := F) (m := 4 * m) (d := d), ¬ IsLinAB g →
      (1 - 2 * ((1 + 2 * d + 4 * m * d) / Fintype.card F)) * bornProb Φ (G.M () g) 1
        ≤ 2 * ∑ u, uniform (Point F (4 * m)) u * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2 := by
    intro g hg
    have hB := sum_uniform_snorm_sq_ordComb_le_of_not_isLinAB hd Φ (hsa g) (hidem g) hX hZ hg
    have hterm : ∀ u : Point F (4 * m), bornProb Φ (G.M () g) 1
        ≤ 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (ordComb ordXZ X Z u (g.eval u))) ^ 2
          + 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2 := by
      intro u
      have h := snorm_sq_add_le Φ
        ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordXZ X Z u (g.eval u)))
        ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - ordComb ordXZ X Z u (g.eval u)))
      rwa [← Matrix.mul_add, ← bOp_add,
        show ordComb ordXZ X Z u (g.eval u) + (1 - ordComb ordXZ X Z u (g.eval u))
          = (1 : Matrix RB RB ℂ) by abel,
        snorm_sq_aOp_mul_bOp Φ (hsa g) (hidem g), Matrix.conjTranspose_one, Matrix.one_mul] at h
    have hw : bornProb Φ (G.M () g) 1
        = ∑ u, uniform (Point F (4 * m)) u * bornProb Φ (G.M () g) 1 := by
      rw [← Finset.sum_mul, sum_uniform_eq_one, one_mul]
    have h1 : bornProb Φ (G.M () g) 1 ≤ ∑ u, uniform (Point F (4 * m)) u
        * (2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (ordComb ordXZ X Z u (g.eval u))) ^ 2
          + 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2) := by
      rw [hw]
      exact Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hterm u) (uniform_nonneg _ _)
    have h2 : ∑ u, uniform (Point F (4 * m)) u
        * (2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (ordComb ordXZ X Z u (g.eval u))) ^ 2
          + 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2)
        = 2 * ∑ u, uniform (Point F (4 * m)) u * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (ordComb ordXZ X Z u (g.eval u))) ^ 2
          + 2 * ∑ u, uniform (Point F (4 * m)) u * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    linarith [h1, h2, hB]
  calc (1 - 2 * ((1 + 2 * d + 4 * m * d) / Fintype.card F))
        * ∑ g ∈ univ.filter (fun g => ¬ IsLinAB g), bornProb Φ (G.M () g) 1
      = ∑ g ∈ univ.filter (fun g => ¬ IsLinAB g),
          (1 - 2 * ((1 + 2 * d + 4 * m * d) / Fintype.card F)) * bornProb Φ (G.M () g) 1 :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ g ∈ univ.filter (fun g => ¬ IsLinAB g), 2 * ∑ u, uniform (Point F (4 * m)) u
          * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2 :=
        Finset.sum_le_sum fun g hg => hbad g (mem_filter.mp hg).2
    _ ≤ ∑ g, 2 * ∑ u, uniform (Point F (4 * m)) u
          * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun g _ _ =>
          mul_nonneg (by norm_num) (Finset.sum_nonneg fun u _ =>
            mul_nonneg (uniform_nonneg _ _) (sq_nonneg _))
    _ = 2 * ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
          ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * Δ := by linarith [hprod]

end Good

end MIPRE.QLD

end
