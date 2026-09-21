/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.PaddedStrategy
import MIPRE.Foundations.LowDegree.SchwartzZippel
import MIPRE.Foundations.StrategyDilation

/-!
# Removing the dummy coordinates (`lem:qld-global-dummy`)

The global polynomial measurements of `lem:qld-global-pvm` have outcomes in
`LowIndDegPoly F (4m) d`, polynomials in the `4m` coordinates of the padded point, while the
padded point measurements read only the `2m + 2` coordinates `xBlk`, `zBlk`, `alph`, `bet`
(`padPt_mats`). The remaining `2m - 2` coordinates are the paper's dummy coordinates `w`. This file
proves that an outcome which reads a dummy coordinate carries little state weight: if the
evaluated global measurement is `δ`-consistent, on average over a uniform point, with a point
measurement that does not read the dummy coordinates, then the total weight of such outcomes is at
most `2δ / (1 - 8md/q)`, hence `4δ` once `16 m d ≤ q`.

## The argument

Resample the dummy coordinates: for two independent uniform points `u`, `u'`, let `mix u u'` be
`u` with its dummy coordinates replaced by those of `u'`. The point measurement is the same at `u`
and at `mix u u'`, and `(u, u') ↦ (mix u u', mix u' u)` is an involution of the pairs, so the
consistency estimate holds at both points simultaneously. Adding the two, the operator
`P_u(g(u)) + P_u(g(mix u u'))` is at most `2 · 1` when the two values agree and at most `1` when
they differ (two distinct elements of a POVM sum to at most the identity; no projectivity is
used), which gives `∑_g ⟨G_g⟩ · Pr[g(u) = g(mix u u')] ≥ 1 - 2δ` (`sum_mass_mixAgree_ge`). For an
outcome that reads a dummy coordinate, `g(u) - g(mix u u')` is a nonzero polynomial in the `8m`
coordinates of the pair, of individual degree at most `d`, so Schwartz--Zippel bounds the
probability by `8md/q` (`card_mixAgree_le`); for one that does not, the probability is `1`
(`eval_mix_of_wIndep`). The two bounds give `sum_bad_mass_le`.

## The bridge to `MvPolynomial`

`LowIndDegPoly F n d` is a coefficient vector indexed by exponent vectors with entries at most
`d`; `LowIndDegPoly.toMv` is the polynomial it denotes, with the evaluation, coefficient and
individual-degree facts, and `degreeOf_rename_le` carries degree bounds along an injective
renaming to every target variable. Schwartz--Zippel is stated in `Foundations` for `Fin n`
variables; `prob_agreeOn_le_individualDegree` is the same statement for any finite variable type,
which is what the pair `Fin (4m) ⊕ Fin (4m)` needs.
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

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## Born-rule and POVM facts -/

section Born

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem bornProb_add_right (ψ : dA × dB → ℂ) (X : Matrix dA dA ℂ) (Y Z : Matrix dB dB ℂ) :
    bornProb ψ X (Y + Z) = bornProb ψ X Y + bornProb ψ X Z := by
  have h := bornProb_sub_right ψ X (Y + Z) Z
  rw [add_sub_cancel_right] at h
  linarith

/-- The Born probability is monotone in Bob's operator when Alice's is positive. -/
theorem bornProb_mono_right (ψ : dA × dB → ℂ) {X : Matrix dA dA ℂ} (hX : X.PosSemidef)
    {Y Y' : Matrix dB dB ℂ} (h : Y ≤ Y') : bornProb ψ X Y ≤ bornProb ψ X Y' := by
  have h0 := bornProb_nonneg ψ hX (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h))
  rw [bornProb_sub_right] at h0
  linarith

/-- Two distinct elements of a POVM sum to at most the identity. -/
theorem POVM.add_le_one {A : Type*} [Fintype A] [DecidableEq A] (M : POVM A dB) {b b' : A}
    (h : b ≠ b') : ((M.mats b).val) + ((M.mats b').val) ≤ (1 : Matrix dB dB ℂ) := by
  have hpair : ((M.mats b).val) + ((M.mats b').val)
      = ∑ x ∈ ({b, b'} : Finset A), ((M.mats x).val) :=
    (Finset.sum_pair (f := fun x => ((M.mats x).val)) h).symm
  rw [← POVM.sum_val M, hpair]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun a _ _ => Matrix.nonneg_iff_posSemidef.mpr (M.posSemidef a)

/-- Exchanging the two parties exchanges the two families. -/
theorem inconsistency_swapVec {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A] (μ : X → ℝ)
    (ψ : dA × dB → ℂ) (M : X → POVM A dA) (N : X → POVM A dB) :
    inconsistency μ (swapVec ψ) N M = inconsistency μ ψ M N := by
  unfold inconsistency
  simp only [bornProb_def, bornProb_swapVec]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact if_congr eq_comm rfl rfl

theorem sum_uniform_eq_one (X : Type*) [Fintype X] [Nonempty X] : ∑ x, uniform X x = 1 := by
  simp only [uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem sum_ite_eq_zero_sub {α β : Type*} [Fintype α] [DecidableEq α] [AddCommGroup β] (a : α)
    (x : α → β) : (∑ b, if a = b then 0 else x b) = (∑ b, x b) - x a := by
  have h : ((∑ b, if a = b then 0 else x b) + ∑ b, if a = b then x b else 0) = ∑ b, x b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_ite_eq univ a x, if_pos (mem_univ a)] at h
  exact eq_sub_of_add_eq h

/-- The elements of a projective measurement are positive. -/
theorem ProjectiveMeasurement.posSemidef_M {X A : Type*} [Fintype A]
    (G : ProjectiveMeasurement X A (Matrix dA dA ℂ)) (x : X) (a : A) : (G.M x a).PosSemidef := by
  have : G.M x a = (G.M x a)ᴴ * G.M x a := by
    rw [← Matrix.star_eq_conjTranspose, G.selfAdjoint, G.projective]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end Born

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MvPolynomial
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## The inconsistency of an evaluated global measurement, unfolded -/

section Mass

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ} {RA RB : Type*} [Fintype RA]
  [DecidableEq RA] [Fintype RB] [DecidableEq RB]

/-- **The inconsistency of an evaluated global measurement with a point measurement** is one minus
the average weight the global outcome's value at the point receives from the point measurement:
`1 - ∑_u μ_u ∑_g ⟨G_g ⊗ P_u(g(u))⟩`. -/
theorem inconsistency_evalPOVM_eq (μ : Point F n → ℝ) (hμ : ∑ u, μ u = 1) {Φ : RA × RB → ℂ}
    (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := n) (d := d)) (Matrix RA RA ℂ))
    (P : Point F n → POVM F RB) :
    inconsistency μ Φ (evalPOVM G) P
      = 1 - ∑ u, μ u * ∑ g, bornProb Φ (G.M () g) (((P u).mats (g.eval u)).val) := by
  have hfib : ∀ u, (∑ a : F, ∑ b : F, if a = b then 0 else
      bornProb Φ (((evalPOVM G u).mats a).val) (((P u).mats b).val))
      = ∑ g, ∑ b : F, if g.eval u = b then 0 else
          bornProb Φ (G.M () g) (((P u).mats b).val) := by
    intro u
    have h1 : ∀ a b : F, (if a = b then (0 : ℝ) else
        bornProb Φ (((evalPOVM G u).mats a).val) (((P u).mats b).val))
        = ∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := n) (d := d) => g.eval u = a,
            if a = b then 0 else bornProb Φ (G.M () g) (((P u).mats b).val) := by
      intro a b
      rw [evalPOVM, POVM.map_mats, bornProb_sum_left]
      split_ifs
      · simp
      · rfl
    simp_rw [h1]
    rw [← Finset.sum_fiberwise univ fun g : LowIndDegPoly (F := F) (m := n) (d := d) => g.eval u]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [(mem_filter.mp hg).2]
  have hsum : ∀ u, (∑ g, ∑ b : F, if g.eval u = b then 0 else
      bornProb Φ (G.M () g) (((P u).mats b).val))
      = 1 - ∑ g, bornProb Φ (G.M () g) (((P u).mats (g.eval u)).val) := by
    intro u
    simp_rw [sum_ite_eq_zero_sub, ← bornProb_sum_right, POVM.sum_val]
    rw [Finset.sum_sub_distrib, ← bornProb_sum_left, G.normalized, bornProb_one_one hΦ]
  unfold inconsistency
  simp only [bornProb_def, hfib, hsum, mul_sub, mul_one, Finset.sum_sub_distrib, hμ]

/-- The total weight of a projective measurement's outcomes is one. -/
theorem sum_bornProb_M_one {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1) {A : Type*} [Fintype A]
    (G : ProjectiveMeasurement Unit A (Matrix RA RA ℂ)) :
    ∑ g, bornProb Φ (G.M () g) (1 : Matrix RB RB ℂ) = 1 := by
  rw [← bornProb_sum_left, G.normalized, bornProb_one_one hΦ]

end Mass

/-! ## The dummy coordinates -/

section Dummy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- A coordinate of the padded point that no padded point measurement reads: everything past
`xBlk`, `zBlk`, `alph`, `bet`. -/
def IsDummy (i : Fin (4 * m)) : Prop := 2 * m + 2 ≤ (i : ℕ)

instance : DecidablePred (IsDummy (m := m)) := fun i =>
  inferInstanceAs (Decidable (2 * m + 2 ≤ (i : ℕ)))

theorem not_isDummy_xIdx (i : Fin m) : ¬ IsDummy (xIdx m i) := by
  simp only [IsDummy, xIdx_val, not_le]
  have := i.isLt
  omega

theorem not_isDummy_zIdx (i : Fin m) : ¬ IsDummy (zIdx m i) := by
  simp only [IsDummy, zIdx_val, not_le]
  have := i.isLt
  omega

theorem not_isDummy_aIdx : ¬ IsDummy (aIdx m) := by
  simp only [IsDummy, aIdx_val, not_le]
  omega

theorem not_isDummy_bIdx : ¬ IsDummy (bIdx m) := by
  simp only [IsDummy, bIdx_val, not_le]
  omega

omit [NeZero m] in
/-- For `m = 1` there are no dummy coordinates. -/
theorem not_isDummy_of_eq_one (hm : m = 1) (i : Fin (4 * m)) : ¬ IsDummy i := by
  simp only [IsDummy, not_le]
  have := i.isLt
  omega

/-- **Resampling the dummy coordinates**: `u` with its dummy coordinates replaced by those of
`u'`. -/
def mix (u u' : Point F (4 * m)) : Point F (4 * m) := fun i => if IsDummy i then u' i else u i

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem mix_apply_of_not (u u' : Point F (4 * m)) {i : Fin (4 * m)} (h : ¬ IsDummy i) :
    mix u u' i = u i := if_neg h

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem mix_apply_of (u u' : Point F (4 * m)) {i : Fin (4 * m)} (h : IsDummy i) :
    mix u u' i = u' i := if_pos h

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
@[simp] theorem xBlk_mix (u u' : Point F (4 * m)) : xBlk (mix u u') = xBlk u :=
  funext fun i => mix_apply_of_not u u' (not_isDummy_xIdx i)

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
@[simp] theorem zBlk_mix (u u' : Point F (4 * m)) : zBlk (mix u u') = zBlk u :=
  funext fun i => mix_apply_of_not u u' (not_isDummy_zIdx i)

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
@[simp] theorem alph_mix (u u' : Point F (4 * m)) : alph (mix u u') = alph u :=
  mix_apply_of_not u u' not_isDummy_aIdx

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
@[simp] theorem bet_mix (u u' : Point F (4 * m)) : bet (mix u u') = bet u :=
  mix_apply_of_not u u' not_isDummy_bIdx

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem mix_mix (u u' : Point F (4 * m)) : mix (mix u u') (mix u' u) = u := by
  funext i
  unfold mix
  split_ifs <;> rfl

/-- The involution of pairs of points that exchanges their dummy coordinates. -/
def mixSwap : Point F (4 * m) × Point F (4 * m) ≃ Point F (4 * m) × Point F (4 * m) where
  toFun p := (mix p.1 p.2, mix p.2 p.1)
  invFun p := (mix p.1 p.2, mix p.2 p.1)
  left_inv p := Prod.ext (mix_mix p.1 p.2) (mix_mix p.2 p.1)
  right_inv p := Prod.ext (mix_mix p.1 p.2) (mix_mix p.2 p.1)

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
@[simp] theorem mixSwap_apply_fst (p : Point F (4 * m) × Point F (4 * m)) :
    (mixSwap p).1 = mix p.1 p.2 := rfl

/-- **The padded point measurement does not read the dummy coordinates.** -/
theorem padPt_mix {dA : Type} [Fintype dA] [DecidableEq dA]
    {M : Question F m → POVM (Answer F m d) dA} (hM : ∀ q, IsPVM fun a => (((M q).mats a).val))
    (u u' : Point F (4 * m)) : padPt hM (mix u u') = padPt hM u :=
  POVM.ext' fun a => by rw [padPt_mats, padPt_mats, xBlk_mix, zBlk_mix, alph_mix, bet_mix]

/-- **`w`-independence**: a coefficient vector with no monomial involving a dummy coordinate. -/
def WIndep (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) : Prop :=
  ∀ e : Fin (4 * m) → Fin (d + 1), (∃ i, IsDummy i ∧ e i ≠ 0) → g e = 0

instance : DecidablePred (WIndep (F := F) (m := m) (d := d)) := fun g =>
  inferInstanceAs (Decidable (∀ e : Fin (4 * m) → Fin (d + 1),
    (∃ i, IsDummy i ∧ e i ≠ 0) → g e = 0))

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem wIndep_of_eq_one (hm : m = 1) (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) :
    WIndep g := fun _ ⟨i, hi, _⟩ => absurd hi (not_isDummy_of_eq_one hm i)

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- A `w`-independent outcome takes the same value after resampling the dummy coordinates. -/
theorem eval_mix_of_wIndep {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : WIndep g)
    (u u' : Point F (4 * m)) : g.eval (mix u u') = g.eval u := by
  unfold LowIndDegPoly.eval
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : ∃ i, IsDummy i ∧ e i ≠ 0
  · rw [hg e he, zero_mul, zero_mul]
  · push Not at he
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : IsDummy i
    · rw [he i hi]
      simp
    · rw [mix_apply_of_not u u' hi]

/-! ### Schwartz--Zippel on the pair -/

/-- The substitution that reads the dummy coordinates from the second point of a pair. -/
def dumSub (i : Fin (4 * m)) : Fin (4 * m) ⊕ Fin (4 * m) :=
  if IsDummy i then Sum.inr i else Sum.inl i

omit [NeZero m] in
theorem dumSub_injective : Function.Injective (dumSub (m := m)) := by
  intro i j h
  unfold dumSub at h
  split_ifs at h <;> simp_all

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem comp_dumSub (x : Fin (4 * m) ⊕ Fin (4 * m) → F) :
    x ∘ dumSub = mix (x ∘ Sum.inl) (x ∘ Sum.inr) := by
  funext i
  simp only [Function.comp_apply, dumSub, mix]
  split_ifs <;> rfl

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- An outcome that reads a dummy coordinate is a different polynomial of the pair before and
after the resampling. -/
theorem rename_toMv_ne {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : ¬ WIndep g) :
    rename Sum.inl g.toMv ≠ rename dumSub g.toMv := by
  intro heq
  unfold WIndep at hg
  push Not at hg
  obtain ⟨e, ⟨i, hi, hei⟩, hge⟩ := hg
  set inl : Fin (4 * m) → Fin (4 * m) ⊕ Fin (4 * m) := Sum.inl with hinl
  have hinj : Function.Injective inl := Sum.inl_injective
  have h1 : (rename inl g.toMv).coeff (Finsupp.mapDomain inl (expFinsupp e)) = g e := by
    rw [coeff_rename_mapDomain _ hinj, LowIndDegPoly.coeff_toMv]
  have h2 : (rename dumSub g.toMv).coeff (Finsupp.mapDomain inl (expFinsupp e)) = 0 := by
    refine coeff_rename_eq_zero _ _ _ fun v hv => ?_
    exfalso
    have hval := congrArg (fun w : Fin (4 * m) ⊕ Fin (4 * m) →₀ ℕ => w (inl i)) hv
    have hnot : inl i ∉ Set.range (dumSub (m := m)) := by
      rintro ⟨j, hj⟩
      unfold dumSub at hj
      by_cases hD : IsDummy j
      · rw [if_pos hD, hinl] at hj
        exact absurd hj (by simp)
      · rw [if_neg hD, hinl, Sum.inl.injEq] at hj
        subst hj
        exact hD hi
    rw [Finsupp.mapDomain_of_notMem_range _ _ hnot, Finsupp.mapDomain_apply hinj,
      expFinsupp_apply] at hval
    exact hei (Fin.ext (by simpa using hval.symm))
  rw [heq, h2] at h1
  exact hge h1.symm

/-- The pairs of points at which an outcome takes the same value before and after resampling
the dummy coordinates. -/
def mixAgree (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) :
    Finset (Point F (4 * m) × Point F (4 * m)) :=
  univ.filter fun p => g.eval p.1 = g.eval (mix p.1 p.2)

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem mixAgree_eq_univ_of_wIndep {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hg : WIndep g) : mixAgree g = univ :=
  Finset.filter_true_of_mem fun p _ => (eval_mix_of_wIndep hg p.1 p.2).symm

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **Schwartz--Zippel for the dummy coordinates**: an outcome that reads a dummy coordinate
takes the same value before and after the resampling with probability at most `8md/q`. -/
theorem card_mixAgree_le {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : ¬ WIndep g) :
    ((mixAgree g).card : ℝ) / (Fintype.card F : ℝ) ^ (4 * m + 4 * m)
      ≤ ((4 * m + 4 * m : ℕ) : ℝ) * d / Fintype.card F := by
  have h := LowDegree.prob_agreeOn_le_individualDegree (rename_toMv_ne hg)
    (degreeOf_rename_le Sum.inl_injective (LowIndDegPoly.degreeOf_toMv_le g))
    (degreeOf_rename_le dumSub_injective (LowIndDegPoly.degreeOf_toMv_le g))
  have hcard : (LowDegree.agreeOn (rename Sum.inl g.toMv) (rename dumSub g.toMv)).card
      = (mixAgree g).card := by
    refine Finset.card_equiv (Equiv.sumArrowEquivProdArrow _ _ _) fun x => ?_
    rw [LowDegree.mem_agreeOn, mixAgree, mem_filter, eval_rename, eval_rename,
      LowIndDegPoly.eval_toMv, LowIndDegPoly.eval_toMv, comp_dumSub]
    exact ⟨fun h => ⟨mem_univ _, h⟩, fun h => h.2⟩
  rw [hcard, Fintype.card_sum, Fintype.card_fin] at h
  exact h

/-! ### The weight of the outcomes that read a dummy coordinate -/

section Weight

variable {RA RB : Type*} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **The resampling estimate.** If the evaluated global measurement is `δ`-consistent, on average
over a uniform point, with a point measurement that does not read the dummy coordinates, then
`∑_g ⟨G_g⟩ · Pr[g(u) = g(mix u u')] ≥ 1 - 2δ`: the consistency holds at `u` and at `mix u u'`
simultaneously, and two distinct elements of a POVM sum to at most the identity. -/
theorem sum_mass_mixAgree_ge {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (P : Point F (4 * m) → POVM F RB) (hP : ∀ u u', P (mix u u') = P u) {δ : ℝ}
    (hcons : inconsistency (uniform (Point F (4 * m))) Φ (evalPOVM G) P ≤ δ) :
    1 - 2 * δ ≤ ∑ g, bornProb Φ (G.M () g) 1
      * (((mixAgree g).card : ℝ) / (Fintype.card F : ℝ) ^ (4 * m + 4 * m)) := by
  set μ := uniform (Point F (4 * m)) with hμdef
  have hμ1 : ∑ u, μ u = 1 := sum_uniform_eq_one _
  set c : ℝ := (Fintype.card (Point F (4 * m)) : ℝ)⁻¹ with hc
  have hcard_c : (Fintype.card (Point F (4 * m)) : ℝ) * c = 1 :=
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  set S : Point F (4 * m) → ℝ :=
    fun u => ∑ g, bornProb Φ (G.M () g) (((P u).mats (g.eval u)).val) with hS
  have h1 : 1 - δ ≤ ∑ u, c * S u := by
    rw [inconsistency_evalPOVM_eq μ hμ1 hΦ G P] at hcons
    have : ∑ u, μ u * ∑ g, bornProb Φ (G.M () g) (((P u).mats (g.eval u)).val)
        = ∑ u, c * S u := rfl
    linarith
  have hpair : ∑ p : Point F (4 * m) × Point F (4 * m), c * c * S p.1 = ∑ u, c * S u := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    calc (Fintype.card (Point F (4 * m)) : ℝ) * (c * c * S u)
        = ((Fintype.card (Point F (4 * m)) : ℝ) * c) * (c * S u) := by ring
      _ = c * S u := by rw [hcard_c, one_mul]
  have hswap : ∑ p : Point F (4 * m) × Point F (4 * m), c * c * S (mix p.1 p.2)
      = ∑ p : Point F (4 * m) × Point F (4 * m), c * c * S p.1 := by
    have := Equiv.sum_comp mixSwap (fun p : Point F (4 * m) × Point F (4 * m) => c * c * S p.1)
    simpa only [mixSwap_apply_fst] using this
  have h2 : 2 * (1 - δ)
      ≤ ∑ p : Point F (4 * m) × Point F (4 * m), c * c * (S p.1 + S (mix p.1 p.2)) := by
    have e1 : 1 - δ ≤ ∑ p : Point F (4 * m) × Point F (4 * m), c * c * S p.1 := by
      rw [hpair]; exact h1
    have e2 : 1 - δ ≤ ∑ p : Point F (4 * m) × Point F (4 * m), c * c * S (mix p.1 p.2) := by
      rw [hswap]; exact e1
    simp only [mul_add, Finset.sum_add_distrib]
    linarith
  have hpt : ∀ (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) (u u' : Point F (4 * m)),
      bornProb Φ (G.M () g) (((P u).mats (g.eval u)).val)
        + bornProb Φ (G.M () g) (((P (mix u u')).mats (g.eval (mix u u'))).val)
        ≤ (1 + if g.eval u = g.eval (mix u u') then 1 else 0) * bornProb Φ (G.M () g) 1 := by
    intro g u u'
    have hG := G.posSemidef_M () g
    rw [hP, ← bornProb_add_right]
    split_ifs with heq
    · rw [heq]
      calc bornProb Φ (G.M () g)
            (((P u).mats (g.eval (mix u u'))).val + ((P u).mats (g.eval (mix u u'))).val)
          ≤ bornProb Φ (G.M () g) (1 + 1) :=
            bornProb_mono_right Φ hG (add_le_add (POVM.le_one _ _) (POVM.le_one _ _))
        _ = (1 + 1) * bornProb Φ (G.M () g) 1 := by rw [bornProb_add_right]; ring
    · calc bornProb Φ (G.M () g)
            (((P u).mats (g.eval u)).val + ((P u).mats (g.eval (mix u u'))).val)
          ≤ bornProb Φ (G.M () g) 1 := bornProb_mono_right Φ hG (POVM.add_le_one (P u) heq)
        _ = (1 + 0) * bornProb Φ (G.M () g) 1 := by ring
  have hc2 : ∑ _p : Point F (4 * m) × Point F (4 * m), c * c = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
    push_cast
    calc ((Fintype.card (Point F (4 * m)) : ℝ) * Fintype.card (Point F (4 * m))) * (c * c)
        = ((Fintype.card (Point F (4 * m)) : ℝ) * c) * (Fintype.card (Point F (4 * m)) * c) := by
          ring
      _ = 1 := by rw [hcard_c, one_mul]
  have hsum : ∑ p : Point F (4 * m) × Point F (4 * m), c * c * (S p.1 + S (mix p.1 p.2))
      ≤ ∑ g, bornProb Φ (G.M () g) 1 * (1 + ((mixAgree g).card : ℝ) * (c * c)) := by
    calc ∑ p : Point F (4 * m) × Point F (4 * m), c * c * (S p.1 + S (mix p.1 p.2))
        = ∑ p : Point F (4 * m) × Point F (4 * m), ∑ g, c * c
            * (bornProb Φ (G.M () g) (((P p.1).mats (g.eval p.1)).val)
              + bornProb Φ (G.M () g) (((P (mix p.1 p.2)).mats (g.eval (mix p.1 p.2))).val)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          show c * c * (∑ g, bornProb Φ (G.M () g) (((P p.1).mats (g.eval p.1)).val)
            + ∑ g, bornProb Φ (G.M () g) (((P (mix p.1 p.2)).mats (g.eval (mix p.1 p.2))).val))
            = _
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ p : Point F (4 * m) × Point F (4 * m), ∑ g, c * c
            * ((1 + if g.eval p.1 = g.eval (mix p.1 p.2) then 1 else 0)
              * bornProb Φ (G.M () g) 1) := by
          refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun g _ => ?_
          exact mul_le_mul_of_nonneg_left (hpt g p.1 p.2) (by positivity)
      _ = ∑ g, bornProb Φ (G.M () g) 1 * (1 + ((mixAgree g).card : ℝ) * (c * c)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun g _ => ?_
          have hind : ∑ p : Point F (4 * m) × Point F (4 * m),
              c * c * (if g.eval p.1 = g.eval (mix p.1 p.2) then (1 : ℝ) else 0)
              = c * c * (mixAgree g).card := by
            rw [← Finset.mul_sum, Finset.sum_boole, mixAgree]
          calc ∑ p : Point F (4 * m) × Point F (4 * m), c * c
                * ((1 + if g.eval p.1 = g.eval (mix p.1 p.2) then (1 : ℝ) else 0)
                  * bornProb Φ (G.M () g) 1)
              = bornProb Φ (G.M () g) 1 * ((∑ _p : Point F (4 * m) × Point F (4 * m), c * c)
                + ∑ p : Point F (4 * m) × Point F (4 * m),
                    c * c * (if g.eval p.1 = g.eval (mix p.1 p.2) then (1 : ℝ) else 0)) := by
                rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun p _ => ?_
                ring
            _ = bornProb Φ (G.M () g) 1 * (1 + ((mixAgree g).card : ℝ) * (c * c)) := by
                rw [hc2, hind]
                ring
  have hmass : ∑ g, bornProb Φ (G.M () g) 1 = 1 := sum_bornProb_M_one hΦ G
  have hcc : c * c = ((Fintype.card F : ℝ) ^ (4 * m + 4 * m))⁻¹ := by
    rw [hc, Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [← mul_inv, ← pow_add]
  have hfin : ∑ g, bornProb Φ (G.M () g) 1 * (1 + ((mixAgree g).card : ℝ) * (c * c))
      = 1 + ∑ g, bornProb Φ (G.M () g) 1
          * (((mixAgree g).card : ℝ) / (Fintype.card F : ℝ) ^ (4 * m + 4 * m)) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hmass, hcc, div_eq_mul_inv]
  linarith

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **`lem:qld-global-dummy`.** If the evaluated global measurement is `δ`-consistent with a point
measurement that does not read the dummy coordinates, the total weight of the outcomes that read
one satisfies `(1 - 8md/q) · weight ≤ 2δ`. -/
theorem sum_bad_mass_le {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (P : Point F (4 * m) → POVM F RB) (hP : ∀ u u', P (mix u u') = P u) {δ : ℝ}
    (hcons : inconsistency (uniform (Point F (4 * m))) Φ (evalPOVM G) P ≤ δ) :
    (1 - ((4 * m + 4 * m : ℕ) : ℝ) * d / Fintype.card F)
      * ∑ g ∈ univ.filter (fun g => ¬ WIndep g), bornProb Φ (G.M () g) 1 ≤ 2 * δ := by
  have h := sum_mass_mixAgree_ge hΦ G P hP hcons
  have hmass := sum_bornProb_M_one (RB := RB) hΦ G
  set η : ℝ := ((4 * m + 4 * m : ℕ) : ℝ) * d / Fintype.card F with hη
  set Q : ℝ := (Fintype.card F : ℝ) ^ (4 * m + 4 * m) with hQ
  have hQpos : 0 < Q := pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
  have hPQ : (Fintype.card (Point F (4 * m) × Point F (4 * m)) : ℝ) = Q := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [hQ, pow_add]
  rw [← Finset.sum_filter_add_sum_filter_not univ fun g => WIndep g] at h hmass
  have hgood : ∑ g ∈ univ.filter (fun g => WIndep g),
      bornProb Φ (G.M () g) 1 * (((mixAgree g).card : ℝ) / Q)
      = ∑ g ∈ univ.filter (fun g => WIndep g), bornProb Φ (G.M () g) 1 := by
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [mixAgree_eq_univ_of_wIndep (mem_filter.mp hg).2, Finset.card_univ, hPQ,
      div_self hQpos.ne', mul_one]
  have hbad : ∑ g ∈ univ.filter (fun g => ¬ WIndep g),
      bornProb Φ (G.M () g) 1 * (((mixAgree g).card : ℝ) / Q)
      ≤ η * ∑ g ∈ univ.filter (fun g => ¬ WIndep g), bornProb Φ (G.M () g) 1 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun g hg => ?_
    rw [mul_comm η]
    exact mul_le_mul_of_nonneg_left (card_mixAgree_le (mem_filter.mp hg).2)
      (bornProb_nonneg _ (G.posSemidef_M () g) Matrix.PosSemidef.one)
  rw [hgood] at h
  rw [sub_mul, one_mul]
  linarith

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- `lem:qld-global-dummy` with the standing assumption `16 m d ≤ q`: the weight of the outcomes
that read a dummy coordinate is at most `4δ`. -/
theorem sum_bad_mass_le_of_le {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (P : Point F (4 * m) → POVM F RB) (hP : ∀ u u', P (mix u u') = P u) {δ : ℝ}
    (hcons : inconsistency (uniform (Point F (4 * m))) Φ (evalPOVM G) P ≤ δ)
    (hq : 16 * m * d ≤ Fintype.card F) :
    ∑ g ∈ univ.filter (fun g => ¬ WIndep g), bornProb Φ (G.M () g) 1 ≤ 4 * δ := by
  have h := sum_bad_mass_le hΦ G P hP hcons
  have hB : 0 ≤ ∑ g ∈ univ.filter (fun g => ¬ WIndep g), bornProb Φ (G.M () g) 1 :=
    Finset.sum_nonneg fun g _ => bornProb_nonneg _ (G.posSemidef_M () g) Matrix.PosSemidef.one
  have hη : ((4 * m + 4 * m : ℕ) : ℝ) * d / Fintype.card F ≤ 1 / 2 := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)]
    have : ((16 * m * d : ℕ) : ℝ) ≤ Fintype.card F := Nat.cast_le.mpr hq
    push_cast at this ⊢
    linarith
  nlinarith

end Weight

end Dummy

end MIPRE.QLD

end
