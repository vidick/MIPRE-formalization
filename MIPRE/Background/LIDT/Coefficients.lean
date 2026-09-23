/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Game
import MIPRE.Foundations.LowDegree.SchwartzZippel

/-!
# Coefficient vectors of low-individual-degree polynomials

`LowIndDegPoly F n d` is a coefficient vector indexed by exponent vectors with entries at most `d`.
This file is the algebra of those vectors that more than one analysis needs, moved here from the
Pauli basis test's `Dummy.lean` and `Linear.lean` (where it was first written) so that the
simultaneous low-degree test, which sits below the Pauli test in the import graph, can use it.
The names are unchanged.

* **Schwartz--Zippel for any finite variable type** (`prob_agreeOn_le_individualDegree`), and the
  bridge `LowIndDegPoly.toMv` to `MvPolynomial` with its evaluation, coefficient and
  individual-degree facts; `card_eval_eq_zero_le` is the form a nonzero coefficient vector needs.
* **Coefficients of a monomial pattern.** `LowIndDegPoly.coef g T t` is the coefficient vector, in
  the variables outside `T`, of the monomial `∏_{k ∈ T} u_k^{t k}`, and `eval_eq_sum_coef` is the
  decomposition `g(u) = ∑_t u^t_T · (coef g T t)(u)`.
-/

noncomputable section

/-! ## Schwartz--Zippel for any finite variable type -/

namespace MIPRE.LowDegree

open Finset MvPolynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The points of `F^σ` at which two polynomials agree. -/
def agreeOn (f g : MvPolynomial σ F) : Finset (σ → F) := {x ∈ univ | eval x f = eval x g}

@[simp] theorem mem_agreeOn {f g : MvPolynomial σ F} {x : σ → F} :
    x ∈ agreeOn f g ↔ eval x f = eval x g := by
  simp [agreeOn]

/-- **Schwartz--Zippel, individual-degree form, for any finite variable type**: two unequal
polynomials of individual degree at most `d` in the variables `σ` agree at a uniformly random
point of `F^σ` with probability at most `|σ| d / q`. -/
theorem prob_agreeOn_le_individualDegree {f g : MvPolynomial σ F} (hfg : f ≠ g) {d : ℕ}
    (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d) :
    ((agreeOn f g).card : ℝ) / (Fintype.card F : ℝ) ^ Fintype.card σ
      ≤ (Fintype.card σ : ℝ) * d / Fintype.card F := by
  set e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  have hne : rename e f ≠ rename e g := fun h => hfg (rename_injective e e.injective h)
  have hdeg : ∀ p : MvPolynomial σ F, (∀ i, p.degreeOf i ≤ d) →
      ∀ j, (rename e p).degreeOf j ≤ d := fun p hp j => by
    have := degreeOf_rename_of_injective (p := p) e.injective (e.symm j)
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    exact hp _
  have h := prob_agree_le_individualDegree hne (hdeg f hf) (hdeg g hg)
  have hcard : (agreeOn f g).card = (agree (rename e f) (rename e g)).card := by
    refine Finset.card_equiv (Equiv.arrowCongr e (Equiv.refl F)) fun x => ?_
    rw [mem_agreeOn, mem_agree, eval_rename, eval_rename]
    have hx : ((Equiv.arrowCongr e (Equiv.refl F)) x) ∘ e = x := by
      funext i
      simp [Equiv.arrowCongr_apply]
    rw [hx]
  rw [hcard]
  exact h

end MIPRE.LowDegree

/-! ## Coefficient vectors as polynomials -/

namespace MIPRE.LIDT

open Finset MvPolynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}

/-- An exponent vector with entries at most `d`, as a finitely supported function. -/
def expFinsupp (e : Fin n → Fin (d + 1)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)

@[simp] theorem expFinsupp_apply (e : Fin n → Fin (d + 1)) (i : Fin n) :
    expFinsupp e i = (e i : ℕ) := rfl

theorem expFinsupp_injective : Function.Injective (expFinsupp (n := n) (d := d)) :=
  fun _ _ h => funext fun i => Fin.ext (congrArg (fun v : Fin n →₀ ℕ => v i) h)

/-- **The polynomial a coefficient vector denotes.** -/
def LowIndDegPoly.toMv (g : LowIndDegPoly (F := F) (m := n) (d := d)) : MvPolynomial (Fin n) F :=
  ∑ e, monomial (expFinsupp e) (g e)

omit [Fintype F] [DecidableEq F] in
theorem LowIndDegPoly.eval_toMv (g : LowIndDegPoly (F := F) (m := n) (d := d)) (u : Point F n) :
    MvPolynomial.eval u g.toMv = g.eval u := by
  simp only [LowIndDegPoly.toMv, map_sum, MvPolynomial.eval_monomial, LowIndDegPoly.eval]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finsupp.prod_fintype _ _ fun i => pow_zero _]
  rfl

omit [Fintype F] [DecidableEq F] in
theorem LowIndDegPoly.coeff_toMv (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (e : Fin n → Fin (d + 1)) : coeff (expFinsupp e) g.toMv = g e := by
  simp only [LowIndDegPoly.toMv, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single e (fun e' _ hne => if_neg (expFinsupp_injective.ne hne))
    (fun h => absurd (mem_univ e) h)]
  exact if_pos rfl

omit [Fintype F] [DecidableEq F] in
theorem LowIndDegPoly.degreeOf_toMv_le (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (i : Fin n) : g.toMv.degreeOf i ≤ d := by
  rw [degreeOf_le_iff]
  intro s hs
  rw [mem_support_iff, LowIndDegPoly.toMv, coeff_sum] at hs
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  rw [coeff_monomial] at he
  split_ifs at he with h
  · rw [← h, expFinsupp_apply]
    exact Nat.lt_succ_iff.mp (e i).isLt
  · exact absurd rfl he

omit [Fintype F] [DecidableEq F] in
/-- Renaming along an injection keeps individual degrees bounded, at every target variable. -/
theorem degreeOf_rename_le {σ τ : Type*} {p : MvPolynomial σ F} {f : σ → τ}
    (hf : Function.Injective f) {d : ℕ} (hp : ∀ i, p.degreeOf i ≤ d) (j : τ) :
    (rename f p).degreeOf j ≤ d := by
  rw [degreeOf_le_iff]
  intro s hs
  obtain ⟨v, rfl, hv⟩ := coeff_rename_ne_zero f p s (mem_support_iff.mp hs)
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hj
    rw [Finsupp.mapDomain_apply hf]
    exact degreeOf_le_iff.mp (hp i) v (mem_support_iff.mpr hv)
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hj]
    exact Nat.zero_le _

end MIPRE.LIDT

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

end
