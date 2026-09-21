/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Linear

/-!
# Separating the two point variables (`lem:qld-global-separate`)

An outcome `g = α g₁ + β g₂` of the global measurement that is linear in the combining
coordinates (`IsLinAB`, `lem:qld-global-linear`) is *good* when `g₁` reads only the `x` block and
`g₂` only the `z` block: `g = α g_X(x) + β g_Z(z)` (`IsGood`). This file bounds the weight of the
linear outcomes that are not good, from the two ordered-product estimates of
`lem:qld-global-products`: the order `X_a Z_b` controls the outcomes whose `g₂` reads a coordinate
outside the `z` block, and the order `Z_b X_a` those whose `g₁` reads a coordinate outside the `x`
block.

## The argument

For a linear outcome and a base point `u₀`, the fibre `{αa + βb = α g₁(u₀) + β g₂(u₀)}` always
contains the diagonal pair `(g₁(u₀), g₂(u₀))`, and contains any other pair for at most `q` of the
`q²` values of `(α, β)`. So the average over `(α, β)` of `‖(S ⊗ B_u(g(u))) Φ‖²` is at most
`2/q · ⟨S⟩ + W(g₁(u₀), g₂(u₀))`, with `W(a, b) = ‖(S ⊗ X_a Z_b) Φ‖² ≤ ⟨S ⊗ Z_b⟩`. Averaging over
`u₀`, read as a uniform `z` block with the other coordinates uniform and independent
(`sum_uniform_mixOn`): for fixed `z`, `u ↦ g₂(u)` is a polynomial in the other coordinates
(`LowIndDegPoly.restrictOff`) which, if `g₂` reads a coordinate outside the `z` block, is
non-constant except for a set of `z` of probability at most `4md/q` (Schwartz--Zippel on a
nonzero coefficient), and where it is non-constant each value `b` is taken with probability at
most `4md/q`, so `E ⟨S ⊗ Z_{g₂(u)}(z)⟩ ≤ 8md/q · ⟨S⟩`. Altogether
`E_u ‖(S ⊗ B_u(g(u))) Φ‖² ≤ η ⟨S⟩` with `η = (2 + 8md)/q`, and the assembly of
`lem:qld-global-linear` gives `(1 - 2η) · (weight of these outcomes) ≤ 2Δ`. The other block is
the mirror image, with the roles of `(X, a, α)` and `(Z, b, β)` exchanged.
-/

noncomputable section

/-! ## Coefficient vectors: constants, differences, restriction to a block -/

namespace MIPRE.LIDT

open Finset

variable {F : Type*} [Field F] {n d : ℕ}

theorem LowIndDegPoly.eval_zero (u : Point F n) :
    (0 : LowIndDegPoly (F := F) (m := n) (d := d)).eval u = 0 := by
  simp [LowIndDegPoly.eval]

theorem LowIndDegPoly.eval_sub (p q : LowIndDegPoly (F := F) (m := n) (d := d)) (u : Point F n) :
    (p - q).eval u = p.eval u - q.eval u := by
  simp only [LowIndDegPoly.eval, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The constant coefficient vector. -/
def LowIndDegPoly.const (c : F) : LowIndDegPoly (F := F) (m := n) (d := d) :=
  fun e => if e = 0 then c else 0

theorem LowIndDegPoly.eval_const (c : F) (u : Point F n) :
    (LowIndDegPoly.const (n := n) (d := d) c).eval u = c := by
  classical
  simp only [LowIndDegPoly.eval, LowIndDegPoly.const]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro e _ he
    simp [he]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A coefficient vector on a pattern not supported in `T` is zero. -/
theorem LowIndDegPoly.coef_eq_zero_of_not (g : LowIndDegPoly (F := F) (m := n) (d := d))
    {T : Finset (Fin n)} {t : Fin n → Fin (d + 1)} (h : ¬ ∀ k ∉ T, t k = 0) : g.coef T t = 0 := by
  funext e
  rw [LowIndDegPoly.coef, if_neg fun hc => h hc.2]
  rfl

/-- **Substituting the coordinates in `T` by those of `z`**: the coefficient vector, in the
variables off `T`, of `u ↦ g(z on T, u off T)`. -/
def LowIndDegPoly.restrictOff (g : LowIndDegPoly (F := F) (m := n) (d := d)) (T : Finset (Fin n))
    (z : Point F n) : LowIndDegPoly (F := F) (m := n) (d := d) :=
  fun e => if ∀ k ∈ T, e k = 0 then (g.coef Tᶜ e).eval z else 0

theorem LowIndDegPoly.restrictOff_apply_of (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (T : Finset (Fin n)) (z : Point F n) {e : Fin n → Fin (d + 1)} (h : ∀ k ∈ T, e k = 0) :
    g.restrictOff T z e = (g.coef Tᶜ e).eval z := if_pos h

/-- The restricted vector evaluates as `g` at the point with the `T` coordinates from `z`. -/
theorem LowIndDegPoly.eval_restrictOff (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (T : Finset (Fin n)) (z u : Point F n) :
    (g.restrictOff T z).eval u = g.eval (fun k => if k ∈ T then z k else u k) := by
  classical
  show (∑ e, g.restrictOff T z e * ∏ k, u k ^ (e k : ℕ)) = _
  rw [LowIndDegPoly.eval_eq_sum_coef g Tᶜ]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : ∀ k ∈ T, t k = 0
  · rw [LowIndDegPoly.restrictOff, if_pos h,
      LowIndDegPoly.eval_coef_of_eq_off g Tᶜ t (u' := z)
        (fun k hk => if_pos (not_not.mp (mt Finset.mem_compl.mpr hk)))]
    have hprod : ∏ k ∈ Tᶜ, (if k ∈ T then z k else u k) ^ (t k : ℕ) = ∏ k, u k ^ (t k : ℕ) := by
      rw [Finset.prod_congr rfl fun k hk => by rw [if_neg (Finset.mem_compl.mp hk)]]
      exact Finset.prod_subset (Finset.subset_univ _) fun k _ hk => by
        rw [h k (not_not.mp (mt Finset.mem_compl.mpr hk)), Fin.val_zero, pow_zero]
    rw [hprod, mul_comm]
  · have h' : ¬ ∀ k ∉ Tᶜ, t k = 0 := fun h' =>
      h fun k hk => h' k fun hc => Finset.mem_compl.mp hc hk
    rw [LowIndDegPoly.restrictOff, if_neg h, LowIndDegPoly.coef_eq_zero_of_not g h',
      LowIndDegPoly.eval_zero, zero_mul, mul_zero]

/-- **Dependence on a coordinate outside `T`**: some monomial of `g` has a nonzero exponent off
`T`. -/
def LowIndDegPoly.DepOutside (g : LowIndDegPoly (F := F) (m := n) (d := d)) (T : Finset (Fin n)) :
    Prop :=
  ∃ e, g e ≠ 0 ∧ ∃ k ∉ T, e k ≠ 0

/-- A vector depending on a coordinate off `T` has a nonzero coefficient vector at a nonzero pattern
supported off `T`. -/
theorem LowIndDegPoly.exists_coef_ne_zero_of_depOutside
    {g : LowIndDegPoly (F := F) (m := n) (d := d)} {T : Finset (Fin n)} (h : g.DepOutside T) :
    ∃ t : Fin n → Fin (d + 1), (∀ k ∈ T, t k = 0) ∧ t ≠ 0 ∧ g.coef Tᶜ t ≠ 0 := by
  classical
  obtain ⟨e, he, k, hk, hek⟩ := h
  refine ⟨maskOn Tᶜ e, fun k' hk' => maskOn_apply_of_not e fun hc => Finset.mem_compl.mp hc hk',
    ?_, ?_⟩
  · intro h0
    apply hek
    have := congrArg (fun t => t k) h0
    simp only [maskOn, if_pos (Finset.mem_compl.mpr hk), Pi.zero_apply] at this
    exact this
  · intro h0
    apply he
    rw [← LowIndDegPoly.coef_maskOff g Tᶜ e, h0]
    rfl

instance [DecidableEq F] (g : LowIndDegPoly (F := F) (m := n) (d := d)) (T : Finset (Fin n)) :
    Decidable (g.DepOutside T) :=
  inferInstanceAs (Decidable (∃ e, g e ≠ 0 ∧ ∃ k ∉ T, e k ≠ 0))

end MIPRE.LIDT

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## Exchanging a block of coordinates -/

section Mix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]

/-- The point with the coordinates in `T` taken from `u'` and the others from `u`. -/
def mixOn (T : Finset (Fin (4 * m))) (u u' : Point F (4 * m)) : Point F (4 * m) :=
  fun i => if i ∈ T then u' i else u i

omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
theorem mixOn_mixOn (T : Finset (Fin (4 * m))) (u u' : Point F (4 * m)) :
    mixOn T (mixOn T u u') (mixOn T u' u) = u := by
  funext i
  unfold mixOn
  split_ifs <;> rfl

/-- The involution of pairs of points that exchanges their coordinates in `T`. -/
def mixOnSwap (T : Finset (Fin (4 * m))) :
    Point F (4 * m) × Point F (4 * m) ≃ Point F (4 * m) × Point F (4 * m) where
  toFun p := (mixOn T p.1 p.2, mixOn T p.2 p.1)
  invFun p := (mixOn T p.1 p.2, mixOn T p.2 p.1)
  left_inv p := Prod.ext (mixOn_mixOn T p.1 p.2) (mixOn_mixOn T p.2 p.1)
  right_inv p := Prod.ext (mixOn_mixOn T p.1 p.2) (mixOn_mixOn T p.2 p.1)

omit [Field F] [DecidableEq F] [NeZero m] in
theorem sum_mixOn (T : Finset (Fin (4 * m))) (f : Point F (4 * m) → ℝ) :
    ∑ u' : Point F (4 * m), ∑ u : Point F (4 * m), f (mixOn T u u')
      = (Fintype.card (Point F (4 * m)) : ℝ) * ∑ u, f u := by
  have h := Equiv.sum_comp (mixOnSwap T) (fun p : Point F (4 * m) × Point F (4 * m) => f p.1)
  simp only [mixOnSwap, Equiv.coe_fn_mk] at h
  rw [Finset.sum_comm, ← Fintype.sum_prod_type', h, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]

omit [DecidableEq F] [NeZero m] in
/-- **A uniform point is a uniform block with the other coordinates uniform and independent.** -/
theorem sum_uniform_mixOn (T : Finset (Fin (4 * m))) (f : Point F (4 * m) → ℝ) :
    ∑ u, uniform (Point F (4 * m)) u * f u
      = ∑ u', uniform (Point F (4 * m)) u'
          * ∑ u, uniform (Point F (4 * m)) u * f (mixOn T u u') := by
  have hN : (Fintype.card (Point F (4 * m)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [uniform, ← Finset.mul_sum]
  rw [sum_mixOn]
  congr 1
  rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem eval_mixOn {d : ℕ} (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d))
    (T : Finset (Fin (4 * m))) (u u' : Point F (4 * m)) :
    g.eval (mixOn T u u') = (g.restrictOff T u').eval u :=
  (LowIndDegPoly.eval_restrictOff g T u' u).symm

/-- The positions of the `z` block. -/
def zSet : Finset (Fin (4 * m)) := univ.image (zIdx m)

/-- The positions of the `x` block. -/
def xSet : Finset (Fin (4 * m)) := univ.image (xIdx m)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem zIdx_mem_zSet (i : Fin m) : zIdx m i ∈ zSet := Finset.mem_image_of_mem _ (mem_univ i)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem xIdx_mem_xSet (i : Fin m) : xIdx m i ∈ xSet := Finset.mem_image_of_mem _ (mem_univ i)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem zBlk_mixOn_zSet (u u' : Point F (4 * m)) : zBlk (mixOn zSet u u') = zBlk u' :=
  funext fun i => if_pos (zIdx_mem_zSet i)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem xBlk_mixOn_xSet (u u' : Point F (4 * m)) : xBlk (mixOn xSet u u') = xBlk u' :=
  funext fun i => if_pos (xIdx_mem_xSet i)

end Mix

/-! ## The two coefficient polynomials of a linear outcome -/

section Lin

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-- The exponent `1`. -/
def oneD (hd : 1 ≤ d) : Fin (d + 1) := ⟨1, Nat.lt_succ_of_le hd⟩

/-- The coefficient of `α` in an outcome: a polynomial in the coordinates other than `α, β`. -/
def gA (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) :
    LowIndDegPoly (F := F) (m := 4 * m) (d := d) :=
  g.coef abSet (patAB (oneD hd) 0)

/-- The coefficient of `β` in an outcome. -/
def gB (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) :
    LowIndDegPoly (F := F) (m := 4 * m) (d := d) :=
  g.coef abSet (patAB 0 (oneD hd))

omit [Field F] [Fintype F] [DecidableEq F] in
theorem patch_abSet_aIdx (t e : Fin (4 * m) → Fin (d + 1)) :
    patch abSet t e (aIdx m) = t (aIdx m) := if_pos (mem_abSet.mpr (Or.inl rfl))

omit [Field F] [Fintype F] [DecidableEq F] in
theorem patch_abSet_bIdx (t e : Fin (4 * m) → Fin (d + 1)) :
    patch abSet t e (bIdx m) = t (bIdx m) := if_pos (mem_abSet.mpr (Or.inr rfl))

omit [Fintype F] [DecidableEq F] in
/-- A linear outcome has no coefficient at a non-linear pattern. -/
theorem coef_patAB_eq_zero_of_isLinAB {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hg : IsLinAB g) {i j : Fin (d + 1)}
    (hij : ¬ (((i : ℕ) = 1 ∧ (j : ℕ) = 0) ∨ ((i : ℕ) = 0 ∧ (j : ℕ) = 1))) :
    g.coef abSet (patAB i j) = 0 := by
  funext e
  rw [LowIndDegPoly.coef]
  split_ifs with h
  · refine hg _ ?_
    rw [patch_abSet_aIdx, patch_abSet_bIdx, patAB_aIdx, patAB_bIdx]
    exact hij
  · rfl

omit [Fintype F] [DecidableEq F] in
/-- **A linear outcome read at the combining coordinates is the linear form of its two
coefficients.** -/
theorem pAB_eq_linAB_of_isLinAB (hd : 1 ≤ d) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hg : IsLinAB g) (u₀ : Point F (4 * m)) :
    pAB g u₀ = linAB hd ((gA hd g).eval u₀) ((gB hd g).eval u₀) := by
  funext t2
  simp only [pAB, linAB]
  by_cases h1 : t2 = e10 hd
  · subst h1
    rw [if_pos rfl]
    simp only [e10, Matrix.cons_val_zero, Matrix.cons_val_one, gA, oneD]
  · rw [if_neg h1]
    by_cases h2 : t2 = e01 hd
    · subst h2
      rw [if_pos rfl]
      simp only [e01, Matrix.cons_val_zero, Matrix.cons_val_one, gB, oneD]
    · rw [if_neg h2]
      have hij : ¬ (((t2 0 : ℕ) = 1 ∧ (t2 1 : ℕ) = 0) ∨ ((t2 0 : ℕ) = 0 ∧ (t2 1 : ℕ) = 1)) := by
        rintro (⟨h0, h1'⟩ | ⟨h0, h1'⟩)
        · apply h1
          rw [← vec_two_eq t2]
          simp only [e10]
          congr 1
          · exact Fin.ext h0
          · congr 1
            exact Fin.ext h1'
        · apply h2
          rw [← vec_two_eq t2]
          simp only [e01]
          congr 1
          · exact Fin.ext h0
          · congr 1
            exact Fin.ext h1'
      rw [coef_patAB_eq_zero_of_isLinAB hg hij, LowIndDegPoly.eval_zero]

omit [Fintype F] [DecidableEq F] in
theorem eval_setAB_of_isLinAB (hd : 1 ≤ d) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hg : IsLinAB g) (u₀ : Point F (4 * m)) (α β : F) :
    g.eval (setAB u₀ α β) = α * (gA hd g).eval u₀ + β * (gB hd g).eval u₀ := by
  rw [← eval_pAB, pAB_eq_linAB_of_isLinAB hd hg, eval_linAB]

/-- **The good outcomes**: `g = α g_X(x) + β g_Z(z)`, with `g_X` reading only the `x` block and
`g_Z` only the `z` block. -/
def IsGood (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) : Prop :=
  ∀ e : Fin (4 * m) → Fin (d + 1), g e ≠ 0 →
    ((e (aIdx m) : ℕ) = 1 ∧ (e (bIdx m) : ℕ) = 0 ∧ ∀ k, k ∉ xSet → k ≠ aIdx m → e k = 0)
    ∨ ((e (aIdx m) : ℕ) = 0 ∧ (e (bIdx m) : ℕ) = 1 ∧ ∀ k, k ∉ zSet → k ≠ bIdx m → e k = 0)

instance : DecidablePred (IsGood (F := F) (m := m) (d := d)) := fun g =>
  inferInstanceAs (Decidable (∀ e : Fin (4 * m) → Fin (d + 1), g e ≠ 0 →
    ((e (aIdx m) : ℕ) = 1 ∧ (e (bIdx m) : ℕ) = 0 ∧ ∀ k, k ∉ xSet → k ≠ aIdx m → e k = 0)
    ∨ ((e (aIdx m) : ℕ) = 0 ∧ (e (bIdx m) : ℕ) = 1 ∧ ∀ k, k ∉ zSet → k ≠ bIdx m → e k = 0)))

omit [Fintype F] [DecidableEq F] in
/-- A linear outcome whose coefficient of `α` reads only the `x` block and whose coefficient of
`β` reads only the `z` block is good. -/
theorem isGood_of (hd : 1 ≤ d) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hlin : IsLinAB g) (hA : ¬ (gA hd g).DepOutside xSet) (hB : ¬ (gB hd g).DepOutside zSet) :
    IsGood g := by
  intro e he
  have hpat : (((e (aIdx m) : ℕ) = 1 ∧ (e (bIdx m) : ℕ) = 0)
      ∨ ((e (aIdx m) : ℕ) = 0 ∧ (e (bIdx m) : ℕ) = 1)) := by
    by_contra h
    exact he (hlin e h)
  have hcoef : ∀ t : Fin (4 * m) → Fin (d + 1), patAB (e (aIdx m)) (e (bIdx m)) = t →
      g.coef abSet t (maskOff abSet e) = g e := fun t ht => by
    rw [← ht, patAB_eq_maskOn, LowIndDegPoly.coef_maskOff]
  rcases hpat with ⟨h1, h0⟩ | ⟨h0, h1⟩
  · have ha : e (aIdx m) = oneD hd := Fin.ext h1
    have hb : e (bIdx m) = 0 := Fin.ext (by rw [h0, Fin.val_zero])
    left
    refine ⟨h1, h0, fun k hk hka => ?_⟩
    by_contra hek
    apply hA
    refine ⟨maskOff abSet e, ?_, k, hk, ?_⟩
    · rw [gA, hcoef (patAB (oneD hd) 0) (by rw [ha, hb])]
      exact he
    · have hkb : k ≠ bIdx m := fun hkb => hek (by rw [hkb, hb])
      rw [maskOff, if_neg (fun hk' => (mem_abSet.mp hk').elim hka hkb)]
      exact hek
  · have ha : e (aIdx m) = 0 := Fin.ext (by rw [h0, Fin.val_zero])
    have hb : e (bIdx m) = oneD hd := Fin.ext h1
    right
    refine ⟨h0, h1, fun k hk hkb => ?_⟩
    by_contra hek
    apply hB
    refine ⟨maskOff abSet e, ?_, k, hk, ?_⟩
    · rw [gB, hcoef (patAB 0 (oneD hd)) (by rw [ha, hb])]
      exact he
    · have hka : k ≠ aIdx m := fun hka => hek (by rw [hka, ha])
      rw [maskOff, if_neg (fun hk' => (mem_abSet.mp hk').elim hka hkb)]
      exact hek

omit [Fintype F] [DecidableEq F] in
/-- An outcome that is not good is not linear, or is linear with a coefficient reading a
coordinate outside its block. -/
theorem not_isGood_cases (hd : 1 ≤ d) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hg : ¬ IsGood g) :
    ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet)
      ∨ (IsLinAB g ∧ (gA hd g).DepOutside xSet) := by
  by_cases hlin : IsLinAB g
  · by_cases hB : (gB hd g).DepOutside zSet
    · exact Or.inr (Or.inl ⟨hlin, hB⟩)
    · by_cases hA : (gA hd g).DepOutside xSet
      · exact Or.inr (Or.inr ⟨hlin, hA⟩)
      · exact absurd (isGood_of hd hlin hA hB) hg
  · exact Or.inl hlin

end Lin

/-! ## The linear fibre and the diagonal weight -/

section Fibre

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {RA RB : Type*} [Fintype RA]
  [DecidableEq RA] [Fintype RB] [DecidableEq RB] {X' Z' : F → Matrix RB RB ℂ}

omit [DecidableEq RA] [Fintype RB] [DecidableEq RB] in
/-- A nontrivial linear form on `F²` vanishes on at most `q` pairs. -/
theorem card_filter_linear_le {c₁ c₂ : F} (h : ¬ (c₁ = 0 ∧ c₂ = 0)) :
    (univ.filter fun ab : F × F => ab.1 * c₁ + ab.2 * c₂ = 0).card ≤ Fintype.card F := by
  by_cases hc₂ : c₂ = 0
  · have hc₁ : c₁ ≠ 0 := fun hc₁ => h ⟨hc₁, hc₂⟩
    subst hc₂
    refine (Finset.card_le_card_of_injOn (fun ab : F × F => ab.2) (fun _ _ => Finset.mem_univ _)
      ?_).trans_eq Finset.card_univ
    intro ab hab ab' hab' he
    have he' : ab.2 = ab'.2 := he
    have h1 : ab.1 = 0 := by
      have := (mem_filter.mp hab).2
      rw [mul_zero, add_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hc₁
    have h2 : ab'.1 = 0 := by
      have := (mem_filter.mp hab').2
      rw [mul_zero, add_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hc₁
    exact Prod.ext (h1.trans h2.symm) he'
  · refine (Finset.card_le_card_of_injOn (fun ab : F × F => ab.1) (fun _ _ => Finset.mem_univ _)
      ?_).trans_eq Finset.card_univ
    intro ab hab ab' hab' he
    have he' : ab.1 = ab'.1 := he
    have h1 := (mem_filter.mp hab).2
    have h2 := (mem_filter.mp hab').2
    refine Prod.ext he' (mul_right_cancel₀ hc₂ ?_)
    linear_combination h1 - h2 - c₁ * he'

omit [DecidableEq RA] in
/-- The order `Z_b X_a` along `(α, β)` is the order `X_a Z_b` with the roles exchanged. -/
theorem ptComb_ordZX_eq (X' Z' : F → Matrix RB RB ℂ) (α β c : F) :
    ptComb (ordZX X' Z') α β c = ptComb (ordXZ Z' X') β α c := by
  simp only [ptComb, ordZX, ordXZ]
  refine Finset.sum_equiv (Equiv.prodComm F F) (fun r => ?_) (fun r _ => ?_)
  · simp only [mem_filter, mem_univ, true_and, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [add_comm]
  · simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]

omit [Field F] [DecidableEq F] in
/-- **The diagonal weight**: `‖(S ⊗ X_a Z_b) Φ‖² = ⟨S ⊗ Z_b X_a Z_b⟩ ≤ ⟨S ⊗ Z_b⟩`. -/
theorem snorm_sq_ordXZ_le_bornProb (Φ : RA × RB → ℂ) {S : Matrix RA RA ℂ} (hsa : Sᴴ = S)
    (hidem : S * S = S) (hX : IsPVM X') (hZ : IsPVM Z') (a b : F) :
    snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' a * Z' b)) ^ 2 ≤ bornProb Φ S (Z' b) := by
  rw [snorm_sq_aOp_mul_bOp Φ hsa hidem, Matrix.conjTranspose_mul, hX.isSelfAdjoint,
    hZ.isSelfAdjoint, Matrix.mul_assoc, ← Matrix.mul_assoc (X' a), hX.idem, ← Matrix.mul_assoc]
  refine bornProb_mono_right Φ (posSemidef_of_proj hsa hidem) ?_
  have h1 : (0 : Matrix RB RB ℂ) ≤ 1 - X' a :=
    sub_nonneg.mpr (proj_le_one (hX.isSelfAdjoint a) (hX.idem a))
  have h2 := (Matrix.nonneg_iff_posSemidef.mp h1).conjTranspose_mul_mul_same (Z' b)
  rw [hZ.isSelfAdjoint, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hZ.idem] at h2
  exact sub_nonneg.mp (Matrix.nonneg_iff_posSemidef.mpr h2)

/-- **The linear fibre**: for the linear form `α a₀ + β b₀`, the fibre always contains the diagonal
pair `(a₀, b₀)`, and any other pair for at most `q` of the `q²` values of `(α, β)`; so the average
over `(α, β)` of the fibre weights is at most `2/q · ⟨S ⊗ 1⟩` plus the diagonal weight. -/
theorem sum_ab_snorm_sq_ordComb_le_of_lin (Φ : RA × RB → ℂ) {S : Matrix RA RA ℂ} (hsa : Sᴴ = S)
    (hidem : S * S = S) (hX : IsPVM X') (hZ : IsPVM Z') (a₀ b₀ : F) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ)
          * bOp (ptComb (ordXZ X' Z') ab.1 ab.2 (ab.1 * a₀ + ab.2 * b₀))) ^ 2
      ≤ 2 / Fintype.card F * bornProb Φ S 1
        + snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' a₀ * Z' b₀)) ^ 2 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hq0 : (0 : ℝ) ≤ (Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹ := by positivity
  have hqi : (0 : ℝ) ≤ (Fintype.card F : ℝ)⁻¹ := by positivity
  have hwsum := sum_snorm_sq_ordXZ_eq Φ hsa hidem hX hZ
  have hW0 : 0 ≤ bornProb Φ S 1 := by
    rw [← hwsum]
    exact Finset.sum_nonneg fun p _ => sq_nonneg _
  have hcount : ∀ p : F × F, ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
      * (if ab.1 * p.1 + ab.2 * p.2 = ab.1 * a₀ + ab.2 * b₀ then (1 : ℝ) else 0)
      ≤ (if p = (a₀, b₀) then (1 : ℝ) else 0) + (Fintype.card F : ℝ)⁻¹ := fun p => by
    rw [← Finset.mul_sum, Finset.sum_boole]
    by_cases hp : p = (a₀, b₀)
    · rw [if_pos hp]
      calc ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
            * ((univ.filter fun ab : F × F =>
                ab.1 * p.1 + ab.2 * p.2 = ab.1 * a₀ + ab.2 * b₀).card : ℝ)
          ≤ ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
              * ((univ : Finset (F × F)).card : ℝ) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_filter_le _ _) hq0
        _ = 1 := by
            rw [Finset.card_univ, Fintype.card_prod]
            push_cast
            field_simp
        _ ≤ 1 + (Fintype.card F : ℝ)⁻¹ := by linarith
    · rw [if_neg hp, zero_add]
      have hset : (univ.filter fun ab : F × F => ab.1 * p.1 + ab.2 * p.2 = ab.1 * a₀ + ab.2 * b₀)
          = univ.filter fun ab : F × F => ab.1 * (p.1 - a₀) + ab.2 * (p.2 - b₀) = 0 := by
        refine Finset.filter_congr fun ab _ => ?_
        constructor <;> intro h <;> linear_combination h
      have hne : ¬ (p.1 - a₀ = 0 ∧ p.2 - b₀ = 0) := fun h =>
        hp (Prod.ext (sub_eq_zero.mp h.1) (sub_eq_zero.mp h.2))
      calc ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
            * ((univ.filter fun ab : F × F =>
                ab.1 * p.1 + ab.2 * p.2 = ab.1 * a₀ + ab.2 * b₀).card : ℝ)
          ≤ ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) * (Fintype.card F : ℝ) := by
            rw [hset]
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_filter_linear_le hne) hq0
        _ = (Fintype.card F : ℝ)⁻¹ := by field_simp
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun ab : F × F => ab.2 = 0)]
  have h0 : ∑ ab ∈ univ.filter (fun ab : F × F => ab.2 = 0),
      ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ)
          * bOp (ptComb (ordXZ X' Z') ab.1 ab.2 (ab.1 * a₀ + ab.2 * b₀))) ^ 2
      ≤ (Fintype.card F : ℝ)⁻¹ * bornProb Φ S 1 := by
    calc _ ≤ ∑ ab ∈ univ.filter (fun ab : F × F => ab.2 = 0),
          ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) * bornProb Φ S 1 :=
          Finset.sum_le_sum fun ab _ => mul_le_mul_of_nonneg_left
            (snorm_sq_ordComb_ordXZ_le Φ hsa hidem hX hZ _ _ _) hq0
      _ = (Fintype.card F : ℝ)⁻¹ * bornProb Φ S 1 := by
          rw [Finset.sum_const, card_filter_snd_eq_zero, nsmul_eq_mul, ← mul_assoc, ← mul_assoc,
            mul_inv_cancel₀ hq, one_mul]
  have h1 : ∑ ab ∈ univ.filter (fun ab : F × F => ¬ ab.2 = 0),
      ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ)
          * bOp (ptComb (ordXZ X' Z') ab.1 ab.2 (ab.1 * a₀ + ab.2 * b₀))) ^ 2
      ≤ (Fintype.card F : ℝ)⁻¹ * bornProb Φ S 1
        + snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' a₀ * Z' b₀)) ^ 2 := by
    rw [← Finset.mul_sum, sum_filter_snorm_sq_ordComb_eq Φ S hX]
    calc _ ≤ ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, ∑ ab : F × F,
            (if ab.1 * p.1 + ab.2 * p.2 = ab.1 * a₀ + ab.2 * b₀ then (1 : ℝ) else 0)
              * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' p.1 * Z' p.2)) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ =>
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun ab _ _ =>
              mul_nonneg (by split_ifs <;> norm_num) (sq_nonneg _)) hq0
      _ = ∑ p : F × F, (∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
            * (if ab.1 * p.1 + ab.2 * p.2 = ab.1 * a₀ + ab.2 * b₀ then (1 : ℝ) else 0))
              * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' p.1 * Z' p.2)) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ab _ => ?_
          ring
      _ ≤ ∑ p : F × F, ((if p = (a₀, b₀) then (1 : ℝ) else 0) + (Fintype.card F : ℝ)⁻¹)
            * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' p.1 * Z' p.2)) ^ 2 :=
          Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hcount p) (sq_nonneg _)
      _ = snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' a₀ * Z' b₀)) ^ 2
            + (Fintype.card F : ℝ)⁻¹ * bornProb Φ S 1 := by
          simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
            Finset.sum_ite_eq', mem_univ, if_true]
          rw [← Finset.mul_sum, hwsum]
      _ = _ := add_comm _ _
  calc _ ≤ (Fintype.card F : ℝ)⁻¹ * bornProb Φ S 1 + ((Fintype.card F : ℝ)⁻¹ * bornProb Φ S 1
        + snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (X' a₀ * Z' b₀)) ^ 2) := add_le_add h0 h1
    _ = _ := by ring

end Fibre

/-! ## Conditioning on a block, the two averages and the assembly -/

section Blocks

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m] {RA RB : Type*}
  [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]

omit [NeZero m] in
/-- **Conditioning on a block**: if `Op` reads only the coordinates in `T` and the polynomial `H`
reads some coordinate outside `T`, then `E_u ⟨S ⊗ Op_u(H(u))⟩ ≤ 8md/q · ⟨S ⊗ 1⟩`: for fixed `T`
coordinates, `H` is a non-constant polynomial in the others except with probability `4md/q`, and a
non-constant polynomial takes each value with probability at most `4md/q`. -/
theorem sum_uniform_bornProb_readOn_le {T : Finset (Fin (4 * m))}
    {Op : Point F (4 * m) → F → Matrix RB RB ℂ} (hOp : ∀ u u', Op (mixOn T u u') = Op u')
    (hpvm : ∀ u, IsPVM (Op u)) {H : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hH : H.DepOutside T) (Φ : RA × RB → ℂ) {S : Matrix RA RA ℂ} (hS : S.PosSemidef) :
    ∑ u, uniform (Point F (4 * m)) u * bornProb Φ S (Op u (H.eval u))
      ≤ 8 * m * d / Fintype.card F * bornProb Φ S 1 := by
  obtain ⟨t₀, ht₀T, ht₀, hcoef⟩ := LowIndDegPoly.exists_coef_ne_zero_of_depOutside hH
  have hW0 : 0 ≤ bornProb Φ S 1 := bornProb_nonneg Φ hS Matrix.PosSemidef.one
  have hη0 : (0 : ℝ) ≤ 4 * m * d / Fintype.card F := by positivity
  rw [sum_uniform_mixOn T]
  have hinner : ∀ u' : Point F (4 * m),
      ∑ u, uniform (Point F (4 * m)) u * bornProb Φ S (Op (mixOn T u u') (H.eval (mixOn T u u')))
        ≤ ((if (H.coef Tᶜ t₀).eval u' = 0 then (1 : ℝ) else 0) + 4 * m * d / Fintype.card F)
          * bornProb Φ S 1 := by
    intro u'
    simp only [hOp, eval_mixOn]
    split_ifs with h0
    · calc _ ≤ ∑ u, uniform (Point F (4 * m)) u * bornProb Φ S 1 :=
            Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (bornProb_mono_right Φ hS
              (proj_le_one ((hpvm u').isSelfAdjoint _) ((hpvm u').idem _))) (uniform_nonneg _ _)
        _ = 1 * bornProb Φ S 1 := by rw [← Finset.sum_mul, sum_uniform_eq_one]
        _ ≤ (1 + 4 * m * d / Fintype.card F) * bornProb Φ S 1 :=
            mul_le_mul_of_nonneg_right (by linarith) hW0
    · rw [zero_add]
      have hne : ∀ b : F, H.restrictOff T u' - LowIndDegPoly.const b ≠ 0 := fun b h => by
        have := congrArg (fun G : LowIndDegPoly (F := F) (m := 4 * m) (d := d) => G t₀) h
        simp only [Pi.sub_apply, Pi.zero_apply, LowIndDegPoly.const, if_neg ht₀, sub_zero,
          LowIndDegPoly.restrictOff_apply_of H T u' ht₀T] at this
        exact h0 this
      have hprob : ∀ b : F, ∑ u, uniform (Point F (4 * m)) u
          * (if (H.restrictOff T u').eval u = b then (1 : ℝ) else 0)
          ≤ 4 * m * d / Fintype.card F := fun b => by
        have h := sum_uniform_eval_eq_zero_le (hne b)
        simp only [LowIndDegPoly.eval_sub, LowIndDegPoly.eval_const, sub_eq_zero] at h
        exact h
      calc ∑ u, uniform (Point F (4 * m)) u * bornProb Φ S (Op u' ((H.restrictOff T u').eval u))
          = ∑ u, uniform (Point F (4 * m)) u * ∑ b, (if (H.restrictOff T u').eval u = b
              then (1 : ℝ) else 0) * bornProb Φ S (Op u' b) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            congr 1
            rw [Finset.sum_eq_single ((H.restrictOff T u').eval u)]
            · rw [if_pos rfl, one_mul]
            · intro b _ hb
              rw [if_neg (Ne.symm hb), zero_mul]
            · intro h
              exact absurd (mem_univ _) h
        _ = ∑ b, (∑ u, uniform (Point F (4 * m)) u
              * (if (H.restrictOff T u').eval u = b then (1 : ℝ) else 0))
                * bornProb Φ S (Op u' b) := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun u _ => ?_
            ring
        _ ≤ ∑ b, (4 * m * d / Fintype.card F) * bornProb Φ S (Op u' b) :=
            Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hprob b)
              (bornProb_nonneg Φ hS ((hpvm u').posSemidef b))
        _ = 4 * m * d / Fintype.card F * bornProb Φ S 1 := by
            rw [← Finset.mul_sum, ← bornProb_sum_right, (hpvm u').sum_eq_one]
  calc _ ≤ ∑ u', uniform (Point F (4 * m)) u'
        * (((if (H.coef Tᶜ t₀).eval u' = 0 then (1 : ℝ) else 0) + 4 * m * d / Fintype.card F)
          * bornProb Φ S 1) :=
        Finset.sum_le_sum fun u' _ => mul_le_mul_of_nonneg_left (hinner u') (uniform_nonneg _ _)
    _ = (∑ u', uniform (Point F (4 * m)) u' * (if (H.coef Tᶜ t₀).eval u' = 0 then (1 : ℝ) else 0))
          * bornProb Φ S 1
        + 4 * m * d / Fintype.card F * (∑ u', uniform (Point F (4 * m)) u') * bornProb Φ S 1 := by
        rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun u' _ => by ring
    _ ≤ 4 * m * d / Fintype.card F * bornProb Φ S 1
        + 4 * m * d / Fintype.card F * 1 * bornProb Φ S 1 := by
        rw [sum_uniform_eq_one]
        exact add_le_add (mul_le_mul_of_nonneg_right (sum_uniform_eval_eq_zero_le hcoef) hW0)
          le_rfl
    _ = 8 * m * d / Fintype.card F * bornProb Φ S 1 := by ring

variable {X Z : Point F m → F → Matrix RB RB ℂ}

/-- **A linear outcome whose `β` coefficient reads a coordinate outside the `z` block**, against
the order `X_a Z_b`: `E_u ‖(S ⊗ B_u(g(u))) Φ‖² ≤ (2 + 8md)/q · ⟨S ⊗ 1⟩`. -/
theorem sum_uniform_snorm_sq_ordComb_XZ_le_of_depB (hd : 1 ≤ d) (Φ : RA × RB → ℂ)
    {S : Matrix RA RA ℂ} (hsa : Sᴴ = S) (hidem : S * S = S) (hX : ∀ x, IsPVM (X x))
    (hZ : ∀ z, IsPVM (Z z)) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hlin : IsLinAB g) (hB : (gB hd g).DepOutside zSet) :
    ∑ u, uniform (Point F (4 * m)) u
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordXZ X Z u (g.eval u))) ^ 2
      ≤ (2 + 8 * m * d) / Fintype.card F * bornProb Φ S 1 := by
  have hS := posSemidef_of_proj hsa hidem
  rw [sum_uniform_setAB]
  have hinner : ∀ u₀ : Point F (4 * m),
      ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordXZ X Z (setAB u₀ ab.1 ab.2)
          (g.eval (setAB u₀ ab.1 ab.2)))) ^ 2
      ≤ 2 / Fintype.card F * bornProb Φ S 1
        + bornProb Φ S (Z (zBlk u₀) ((gB hd g).eval u₀)) := by
    intro u₀
    have hre : ∀ ab : F × F, ordComb ordXZ X Z (setAB u₀ ab.1 ab.2) (g.eval (setAB u₀ ab.1 ab.2))
        = ptComb (ordXZ (X (xBlk u₀)) (Z (zBlk u₀))) ab.1 ab.2
          (ab.1 * (gA hd g).eval u₀ + ab.2 * (gB hd g).eval u₀) := fun ab => by
      rw [ordComb, xBlk_setAB, zBlk_setAB, alph_setAB, bet_setAB, eval_setAB_of_isLinAB hd hlin]
    simp only [hre]
    exact (sum_ab_snorm_sq_ordComb_le_of_lin Φ hsa hidem (hX _) (hZ _) _ _).trans
      (add_le_add le_rfl (snorm_sq_ordXZ_le_bornProb Φ hsa hidem (hX _) (hZ _) _ _))
  calc _ ≤ ∑ u₀, uniform (Point F (4 * m)) u₀ * (2 / Fintype.card F * bornProb Φ S 1
        + bornProb Φ S (Z (zBlk u₀) ((gB hd g).eval u₀))) :=
        Finset.sum_le_sum fun u₀ _ => mul_le_mul_of_nonneg_left (hinner u₀) (uniform_nonneg _ _)
    _ = 2 / Fintype.card F * (∑ u₀, uniform (Point F (4 * m)) u₀) * bornProb Φ S 1
        + ∑ u₀, uniform (Point F (4 * m)) u₀ * bornProb Φ S (Z (zBlk u₀) ((gB hd g).eval u₀)) := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun u₀ _ => by ring
    _ ≤ 2 / Fintype.card F * 1 * bornProb Φ S 1 + 8 * m * d / Fintype.card F * bornProb Φ S 1 := by
        rw [sum_uniform_eq_one]
        exact add_le_add le_rfl (sum_uniform_bornProb_readOn_le (Op := fun u => Z (zBlk u))
          (fun u u' => by rw [zBlk_mixOn_zSet]) (fun u => hZ _) hB Φ hS)
    _ = (2 + 8 * m * d) / Fintype.card F * bornProb Φ S 1 := by ring

/-- **A linear outcome whose `α` coefficient reads a coordinate outside the `x` block**, against
the order `Z_b X_a`: the mirror image, with the roles of `(X, a, α)` and `(Z, b, β)` exchanged. -/
theorem sum_uniform_snorm_sq_ordComb_ZX_le_of_depA (hd : 1 ≤ d) (Φ : RA × RB → ℂ)
    {S : Matrix RA RA ℂ} (hsa : Sᴴ = S) (hidem : S * S = S) (hX : ∀ x, IsPVM (X x))
    (hZ : ∀ z, IsPVM (Z z)) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hlin : IsLinAB g) (hA : (gA hd g).DepOutside xSet) :
    ∑ u, uniform (Point F (4 * m)) u
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordZX X Z u (g.eval u))) ^ 2
      ≤ (2 + 8 * m * d) / Fintype.card F * bornProb Φ S 1 := by
  have hS := posSemidef_of_proj hsa hidem
  rw [sum_uniform_setAB]
  have hinner : ∀ u₀ : Point F (4 * m),
      ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordZX X Z (setAB u₀ ab.1 ab.2)
          (g.eval (setAB u₀ ab.1 ab.2)))) ^ 2
      ≤ 2 / Fintype.card F * bornProb Φ S 1
        + bornProb Φ S (X (xBlk u₀) ((gA hd g).eval u₀)) := by
    intro u₀
    have hre : ∀ ab : F × F, ordComb ordZX X Z (setAB u₀ ab.1 ab.2) (g.eval (setAB u₀ ab.1 ab.2))
        = ptComb (ordXZ (Z (zBlk u₀)) (X (xBlk u₀))) ab.2 ab.1
          (ab.2 * (gB hd g).eval u₀ + ab.1 * (gA hd g).eval u₀) := fun ab => by
      rw [ordComb, xBlk_setAB, zBlk_setAB, alph_setAB, bet_setAB, eval_setAB_of_isLinAB hd hlin,
        ptComb_ordZX_eq, add_comm]
    simp only [hre]
    calc _ = ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
          * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ)
            * bOp (ptComb (ordXZ (Z (zBlk u₀)) (X (xBlk u₀))) ab.1 ab.2
              (ab.1 * (gB hd g).eval u₀ + ab.2 * (gA hd g).eval u₀))) ^ 2 :=
          Equiv.sum_comp (Equiv.prodComm F F) (fun ab : F × F =>
            ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
              * snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ)
                * bOp (ptComb (ordXZ (Z (zBlk u₀)) (X (xBlk u₀))) ab.1 ab.2
                  (ab.1 * (gB hd g).eval u₀ + ab.2 * (gA hd g).eval u₀))) ^ 2)
      _ ≤ 2 / Fintype.card F * bornProb Φ S 1 + snorm Φ ((aOp S : Matrix (RA × RB) _ ℂ)
            * bOp (Z (zBlk u₀) ((gB hd g).eval u₀) * X (xBlk u₀) ((gA hd g).eval u₀))) ^ 2 :=
          sum_ab_snorm_sq_ordComb_le_of_lin Φ hsa hidem (hZ _) (hX _) _ _
      _ ≤ _ := add_le_add le_rfl (snorm_sq_ordXZ_le_bornProb Φ hsa hidem (hZ _) (hX _) _ _)
  calc _ ≤ ∑ u₀, uniform (Point F (4 * m)) u₀ * (2 / Fintype.card F * bornProb Φ S 1
        + bornProb Φ S (X (xBlk u₀) ((gA hd g).eval u₀))) :=
        Finset.sum_le_sum fun u₀ _ => mul_le_mul_of_nonneg_left (hinner u₀) (uniform_nonneg _ _)
    _ = 2 / Fintype.card F * (∑ u₀, uniform (Point F (4 * m)) u₀) * bornProb Φ S 1
        + ∑ u₀, uniform (Point F (4 * m)) u₀ * bornProb Φ S (X (xBlk u₀) ((gA hd g).eval u₀)) := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun u₀ _ => by ring
    _ ≤ 2 / Fintype.card F * 1 * bornProb Φ S 1 + 8 * m * d / Fintype.card F * bornProb Φ S 1 := by
        rw [sum_uniform_eq_one]
        exact add_le_add le_rfl (sum_uniform_bornProb_readOn_le (Op := fun u => X (xBlk u))
          (fun u u' => by rw [xBlk_mixOn_xSet]) (fun u => hX _) hA Φ hS)
    _ = (2 + 8 * m * d) / Fintype.card F * bornProb Φ S 1 := by ring

omit [DecidableEq F] [NeZero m] in
/-- **The assembly, abstractly**: if every bad outcome has `E_u ‖(G_g ⊗ B_u(g(u))) Φ‖² ≤ η ⟨G_g⟩`
and the products estimate `∑_g E_u ‖(G_g ⊗ (1 - B_u(g(u)))) Φ‖² ≤ Δ` holds, then
`(1 - 2η) · (weight of the bad outcomes) ≤ 2Δ`. -/
theorem sum_bad_mass_le_of_avg (Φ : RA × RB → ℂ)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (B : Point F (4 * m) → F → Matrix RB RB ℂ)
    (bad : LowIndDegPoly (F := F) (m := 4 * m) (d := d) → Prop) [DecidablePred bad] {η Δ : ℝ}
    (havg : ∀ g, bad g → ∑ u, uniform (Point F (4 * m)) u
      * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (B u (g.eval u))) ^ 2
      ≤ η * bornProb Φ (G.M () g) 1)
    (hprod : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - B u (g.eval u))) ^ 2 ≤ Δ) :
    (1 - 2 * η) * ∑ g ∈ univ.filter bad, bornProb Φ (G.M () g) 1 ≤ 2 * Δ := by
  have hsa : ∀ g, (G.M () g)ᴴ = G.M () g := fun g => G.selfAdjoint () g
  have hidem : ∀ g, G.M () g * G.M () g = G.M () g := fun g => G.projective () g
  have hbad : ∀ g : LowIndDegPoly (F := F) (m := 4 * m) (d := d), bad g →
      (1 - 2 * η) * bornProb Φ (G.M () g) 1
        ≤ 2 * ∑ u, uniform (Point F (4 * m)) u * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (1 - B u (g.eval u))) ^ 2 := by
    intro g hg
    have hB := havg g hg
    have hterm : ∀ u : Point F (4 * m), bornProb Φ (G.M () g) 1
        ≤ 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (B u (g.eval u))) ^ 2
          + 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (1 - B u (g.eval u))) ^ 2 := by
      intro u
      have h := snorm_sq_add_le Φ
        ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (B u (g.eval u)))
        ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - B u (g.eval u)))
      rwa [← Matrix.mul_add, ← bOp_add,
        show B u (g.eval u) + (1 - B u (g.eval u)) = (1 : Matrix RB RB ℂ) by abel,
        snorm_sq_aOp_mul_bOp Φ (hsa g) (hidem g), Matrix.conjTranspose_one, Matrix.one_mul] at h
    have hw : bornProb Φ (G.M () g) 1
        = ∑ u, uniform (Point F (4 * m)) u * bornProb Φ (G.M () g) 1 := by
      rw [← Finset.sum_mul, sum_uniform_eq_one, one_mul]
    have h1 : bornProb Φ (G.M () g) 1 ≤ ∑ u, uniform (Point F (4 * m)) u
        * (2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (B u (g.eval u))) ^ 2
          + 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (1 - B u (g.eval u))) ^ 2) := by
      rw [hw]
      exact Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hterm u) (uniform_nonneg _ _)
    have h2 : ∑ u, uniform (Point F (4 * m)) u
        * (2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (B u (g.eval u))) ^ 2
          + 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (1 - B u (g.eval u))) ^ 2)
        = 2 * ∑ u, uniform (Point F (4 * m)) u
            * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (B u (g.eval u))) ^ 2
          + 2 * ∑ u, uniform (Point F (4 * m)) u * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (1 - B u (g.eval u))) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    linarith [h1, h2, hB]
  calc (1 - 2 * η) * ∑ g ∈ univ.filter bad, bornProb Φ (G.M () g) 1
      = ∑ g ∈ univ.filter bad, (1 - 2 * η) * bornProb Φ (G.M () g) 1 := Finset.mul_sum _ _ _
    _ ≤ ∑ g ∈ univ.filter bad, 2 * ∑ u, uniform (Point F (4 * m)) u
          * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - B u (g.eval u))) ^ 2 :=
        Finset.sum_le_sum fun g hg => hbad g (mem_filter.mp hg).2
    _ ≤ ∑ g, 2 * ∑ u, uniform (Point F (4 * m)) u
          * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - B u (g.eval u))) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun g _ _ =>
          mul_nonneg (by norm_num) (Finset.sum_nonneg fun u _ =>
            mul_nonneg (uniform_nonneg _ _) (sq_nonneg _))
    _ = 2 * ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
          ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - B u (g.eval u))) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * Δ := by linarith [hprod]

/-- **`lem:qld-global-separate`, abstract form.** With `η = (2 + 2d + 8md)/q`, if the two
ordered-product estimates hold with bounds `Δ₁` (order `X_a Z_b`) and `Δ₂` (order `Z_b X_a`),
then `(1 - 2η) · (weight of the outcomes that are not good) ≤ 2Δ₁ + 2Δ₂`. -/
theorem sum_not_isGood_mass_le (hd : 1 ≤ d) (Φ : RA × RB → ℂ)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z)) {Δ₁ Δ₂ : ℝ}
    (hXZ : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2
      ≤ Δ₁)
    (hZX : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - ordComb ordZX X Z u (g.eval u))) ^ 2
      ≤ Δ₂) :
    (1 - 2 * ((2 + 2 * d + 8 * m * d) / Fintype.card F))
        * ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1
      ≤ 2 * Δ₁ + 2 * Δ₂ := by
  have hsa : ∀ g, (G.M () g)ᴴ = G.M () g := fun g => G.selfAdjoint () g
  have hidem : ∀ g, G.M () g * G.M () g = G.M () g := fun g => G.projective () g
  have hw0 : ∀ g, 0 ≤ bornProb Φ (G.M () g) 1 := fun g =>
    bornProb_nonneg Φ (posSemidef_of_proj (hsa g) (hidem g)) Matrix.PosSemidef.one
  have hq0 : (0 : ℝ) ≤ (Fintype.card F : ℝ)⁻¹ := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmd0 : (0 : ℝ) ≤ m * d := mul_nonneg hm0 hd0
  have hη₁ : (1 + 2 * d + 4 * m * d) / (Fintype.card F : ℝ)
      ≤ (2 + 2 * d + 8 * m * d) / Fintype.card F := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ hq0
    linarith
  have hη₂ : (2 + 8 * m * d) / (Fintype.card F : ℝ)
      ≤ (2 + 2 * d + 8 * m * d) / Fintype.card F := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ hq0
    linarith
  -- the two applications of the assembly
  have h₁ := sum_bad_mass_le_of_avg Φ G (ordComb ordXZ X Z)
    (fun g => ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet))
    (η := (2 + 2 * d + 8 * m * d) / Fintype.card F) (fun g hg => by
      rcases hg with hg | ⟨hlin, hB⟩
      · exact (sum_uniform_snorm_sq_ordComb_le_of_not_isLinAB hd Φ (hsa g) (hidem g) hX hZ
          hg).trans (mul_le_mul_of_nonneg_right hη₁ (hw0 g))
      · exact (sum_uniform_snorm_sq_ordComb_XZ_le_of_depB hd Φ (hsa g) (hidem g) hX hZ hlin
          hB).trans (mul_le_mul_of_nonneg_right hη₂ (hw0 g))) hXZ
  have h₂ := sum_bad_mass_le_of_avg Φ G (ordComb ordZX X Z)
    (fun g => IsLinAB g ∧ (gA hd g).DepOutside xSet)
    (η := (2 + 2 * d + 8 * m * d) / Fintype.card F) (fun g hg =>
      (sum_uniform_snorm_sq_ordComb_ZX_le_of_depA hd Φ (hsa g) (hidem g) hX hZ hg.1
        hg.2).trans (mul_le_mul_of_nonneg_right hη₂ (hw0 g))) hZX
  -- the union bound
  have hsub : univ.filter (fun g : LowIndDegPoly (F := F) (m := 4 * m) (d := d) => ¬ IsGood g)
      ⊆ univ.filter (fun g => ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet))
        ∪ univ.filter (fun g => IsLinAB g ∧ (gA hd g).DepOutside xSet) := by
    intro g hg
    rw [mem_filter] at hg
    rw [Finset.mem_union, mem_filter, mem_filter]
    rcases not_isGood_cases hd hg.2 with h | h | h
    · exact Or.inl ⟨mem_univ _, Or.inl h⟩
    · exact Or.inl ⟨mem_univ _, Or.inr h⟩
    · exact Or.inr ⟨mem_univ _, h⟩
  have hunion := Finset.sum_union_inter
    (s₁ := univ.filter (fun g : LowIndDegPoly (F := F) (m := 4 * m) (d := d) =>
      ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet)))
    (s₂ := univ.filter (fun g => IsLinAB g ∧ (gA hd g).DepOutside xSet))
    (f := fun g => bornProb Φ (G.M () g) 1)
  have hinter := Finset.sum_nonneg (s := univ.filter (fun g : LowIndDegPoly (F := F) (m := 4 * m)
    (d := d) => ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet))
      ∩ univ.filter (fun g => IsLinAB g ∧ (gA hd g).DepOutside xSet))
    fun g _ => hw0 g
  have hcover := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun g => bornProb Φ (G.M () g) 1) fun g _ _ => hw0 g
  have hΔ₁ : 0 ≤ Δ₁ := le_trans (Finset.sum_nonneg fun u _ => mul_nonneg (uniform_nonneg _ _)
    (Finset.sum_nonneg fun g _ => sq_nonneg _)) hXZ
  have hΔ₂ : 0 ≤ Δ₂ := le_trans (Finset.sum_nonneg fun u _ => mul_nonneg (uniform_nonneg _ _)
    (Finset.sum_nonneg fun g _ => sq_nonneg _)) hZX
  by_cases hc : 0 ≤ 1 - 2 * ((2 + 2 * d + 8 * m * d) / (Fintype.card F : ℝ))
  · have hW : ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1
        ≤ ∑ g ∈ univ.filter (fun g => ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet)),
            bornProb Φ (G.M () g) 1
          + ∑ g ∈ univ.filter (fun g => IsLinAB g ∧ (gA hd g).DepOutside xSet),
            bornProb Φ (G.M () g) 1 := by linarith
    calc _ ≤ (1 - 2 * ((2 + 2 * d + 8 * m * d) / Fintype.card F))
          * (∑ g ∈ univ.filter (fun g => ¬ IsLinAB g ∨ (IsLinAB g ∧ (gB hd g).DepOutside zSet)),
              bornProb Φ (G.M () g) 1
            + ∑ g ∈ univ.filter (fun g => IsLinAB g ∧ (gA hd g).DepOutside xSet),
              bornProb Φ (G.M () g) 1) := mul_le_mul_of_nonneg_left hW hc
      _ ≤ 2 * Δ₁ + 2 * Δ₂ := by rw [mul_add]; exact add_le_add h₁ h₂
  · push Not at hc
    have hsum : 0 ≤ ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1 :=
      Finset.sum_nonneg fun g _ => hw0 g
    have hprod0 := mul_nonneg (neg_nonneg.mpr hc.le) hsum
    linarith

end Blocks

end MIPRE.QLD

end
