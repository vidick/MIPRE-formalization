/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Helper
import MIPRE.Background.QLD.PauliBasis
import MIPRE.Background.QLD.NonMultilinear

/-!
# The mass at non-multilinear outcomes (`lem:qld-exact-paulis`, the approximate half)

The Pauli construction of `MIPRE/Background/QLD/ExactPauli.lean` reads an outcome `g` of the
simultaneous measurement through the *multilinear interpolant* of its values on the boolean cube,
`Coded(g) · ind_m(u)`, rather than through `g(u)` itself. The two agree exactly when `g` is
multilinear and not otherwise, so the construction is consistent with the strategy's point
measurement up to the mass the simultaneous measurement puts on non-multilinear outcomes.

That mass is what the paper's `lem:qld-construct-the-paulis` bounds, in an argument it repaired
twice. The repair is to compare the outcome not with the point measurement --- whose label depends
on the sampled point --- but with a projective family indexed by **cube data**, which does not.
Then the point is independent of the operators, and Schwartz--Zippel applies in the direction it
is true in: two distinct polynomials of total degree `md` *agree* on at most an `md/q` fraction.

This file is the aggregation step, stated so that its two inputs are visible: a lower bound on the
agreement with the cube-data family, and a uniform bound on the probability that a bad outcome
agrees with any one of its labels.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

section Mass

variable {RA RB G K X : Type*} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
  [Fintype G] [DecidableEq G] [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]

/-- **The aggregation step.** `S` is a projective measurement on one party and `N` one on the
other, `val` and `ev` two labellings by a field element at each question, and the agreement of `S`
with `N` under matching labels is at least `1 - η`. If off a set `ML` every outcome of `S` matches
every label of `N` with probability at most `c`, the mass of `S` off `ML` is at most `η + c`. -/
theorem sum_mass_off_le {F : Type*} [DecidableEq F] {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ : ∑ x, μ x = 1) {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1) {S : G → Matrix RA RA ℂ}
    (hS : IsPVM S) {N : K → Matrix RB RB ℂ} (hN : IsPVM N) (val : K → X → F) (ev : G → X → F)
    {ML : Finset G} {η c : ℝ} (hc : 0 ≤ c)
    (hlow : 1 - η ≤ ∑ g, ∑ x, μ x
      * ∑ k ∈ univ.filter fun k => val k x = ev g x, bornProb Φ (S g) (N k))
    (hagree : ∀ g ∉ ML, ∀ k, ∑ x, μ x * (if val k x = ev g x then (1 : ℝ) else 0) ≤ c) :
    ∑ g ∈ univ \ ML, bornProb Φ (S g) 1 ≤ η + c := by
  classical
  set Sw : G → ℝ := fun g => bornProb Φ (S g) 1 with hSw
  set Tw : G → ℝ := fun g => ∑ x, μ x
    * ∑ k ∈ univ.filter fun k => val k x = ev g x, bornProb Φ (S g) (N k) with hTw
  have hpos : ∀ (g : G) (k : K), 0 ≤ bornProb Φ (S g) (N k) := fun g k =>
    bornProb_nonneg Φ (hS.posSemidef g) (hN.posSemidef k)
  have hfull : ∀ g, ∑ k, bornProb Φ (S g) (N k) = Sw g := fun g => by
    rw [hSw, ← bornProb_sum_right, hN.sum_eq_one]
  have hS0 : ∀ g, 0 ≤ Sw g := fun g => by
    rw [← hfull g]
    exact Finset.sum_nonneg fun k _ => hpos g k
  -- the total mass is one
  have hsum : ∑ g, Sw g = 1 := by
    rw [hSw]
    simp only []
    rw [← bornProb_sum_left, hS.sum_eq_one, bornProb_one_one hΦ]
  -- `T` is dominated by `S`
  have hdom : ∀ g, Tw g ≤ Sw g := fun g => by
    have hx : ∀ x : X, (∑ k ∈ univ.filter fun k => val k x = ev g x, bornProb Φ (S g) (N k))
        ≤ Sw g := fun x => by
      rw [← hfull g]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun k _ _ => hpos g k
    calc Tw g ≤ ∑ x, μ x * Sw g :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hx x) (hμ0 x)
      _ = Sw g := by rw [← Finset.sum_mul, hμ, one_mul]
  -- off `ML` it is dominated by `c` times `S`
  have hoff : ∀ g ∉ ML, Tw g ≤ c * Sw g := fun g hg => by
    have hswap : Tw g = ∑ k, (∑ x, μ x * (if val k x = ev g x then (1 : ℝ) else 0))
        * bornProb Φ (S g) (N k) := by
      rw [hTw]
      simp only [Finset.sum_filter, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> ring
    rw [hswap, ← hfull g, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_right (hagree g hg k) (hpos g k)
  exact MIPRE.QLD.nonMultilinear_mass_le hS0 hsum hdom hoff hc hlow

omit [Fintype G] [DecidableEq G] [Fintype K] [DecidableEq K] in
/-- **The averaged substitution estimate.** Against a projective family at each question, an
agreement with any family on the other party is bounded by the root of that family's average
weight: Cauchy--Schwarz at each question, then Jensen for the average. -/
theorem abs_sum_weighted_bornProb_le {C : Type*} [Fintype C] {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ : ∑ x, μ x = 1) {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1) {T : X → C → Matrix RA RA ℂ}
    (hT : ∀ x, IsPVM (T x)) (D : X → C → Matrix RB RB ℂ) :
    |∑ x, μ x * ∑ c, bornProb Φ (T x c) (D x c)|
      ≤ Real.sqrt (∑ x, μ x * ∑ c, ‖stateVecB Φ (D x c)‖ ^ 2) := by
  have hx : ∀ x, |∑ c, bornProb Φ (T x c) (D x c)|
      ≤ Real.sqrt (∑ c, ‖stateVecB Φ (D x c)‖ ^ 2) := fun x =>
    QLD.abs_sum_bornProb_le Φ hΦ (hT x) (D x)
  have h1 : |∑ x, μ x * ∑ c, bornProb Φ (T x c) (D x c)|
      ≤ ∑ x, μ x * Real.sqrt (∑ c, ‖stateVecB Φ (D x c)‖ ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [abs_mul, abs_of_nonneg (hμ0 x)]
    exact mul_le_mul_of_nonneg_left (hx x) (hμ0 x)
  exact h1.trans (sum_weighted_sqrt_le μ _ hμ0 hμ
    fun x => Finset.sum_nonneg fun c _ => sq_nonneg _)

end Mass

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl MvPolynomial
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## Multilinear outcomes, and Schwartz--Zippel against every cube datum at once -/

section ML

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- **A multilinear outcome**: every monomial has each exponent at most one, so the outcome is its
own multilinear interpolant. -/
def IsML (g : LowIndDegPoly (F := F) (m := m) (d := d)) : Prop :=
  ∀ e : Fin m → Fin (d + 1), g e ≠ 0 → ∀ i, (e i : ℕ) ≤ 1

instance : DecidablePred (IsML (F := F) (m := m) (d := d)) := fun g =>
  inferInstanceAs (Decidable (∀ e : Fin m → Fin (d + 1), g e ≠ 0 → ∀ i, (e i : ℕ) ≤ 1))

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- A non-multilinear outcome has an individual degree above one, so it is distinct from the
interpolant of every cube datum. -/
theorem not_degreeOf_le_one_of_not_isML {g : LowIndDegPoly (F := F) (m := m) (d := d)}
    (hg : ¬ IsML g) : ¬ ∀ i, g.toMv.degreeOf i ≤ 1 := by
  unfold IsML at hg
  push Not at hg
  obtain ⟨e, he, i, hi⟩ := hg
  intro hall
  have hmem : expFinsupp e ∈ g.toMv.support := by
    rw [MvPolynomial.mem_support_iff, LowIndDegPoly.coeff_toMv]
    exact he
  have hlt : g.toMv.degreeOf i < 2 := lt_of_le_of_lt (hall i) (by norm_num)
  rw [MvPolynomial.degreeOf_lt_iff (by norm_num)] at hlt
  have := hlt _ hmem
  rw [expFinsupp_apply] at this
  omega

/-- **Schwartz--Zippel, in the direction the repair needs**: a non-multilinear outcome agrees with
the interpolant of a cube datum at a uniform point with probability at most `md/q`, and the bound
does not depend on the datum. -/
theorem sum_uniform_agree_ldEnc_le (hd : 1 ≤ d)
    {g : LowIndDegPoly (F := F) (m := m) (d := d)} (hg : ¬ IsML g) (k : Anc F m) :
    ∑ u, uniform (Point F m) u
        * (if dotF k (indVec u) = g.eval u then (1 : ℝ) else 0)
      ≤ (m : ℝ) * d / Fintype.card F := by
  have hsz := prob_agree_ldEnc_le_of_not_multilinear (g := g.toMv)
    (LowIndDegPoly.degreeOf_toMv_le g) hd (not_degreeOf_le_one_of_not_isML hg) k
  have hset : (univ.filter fun u : Point F m => dotF k (indVec u) = g.eval u)
      = agree g.toMv (ldEnc k) := by
    ext u
    rw [mem_filter, mem_agree, dotF_indVec, LowIndDegPoly.eval_toMv]
    simp only [mem_univ, true_and]
    exact eq_comm
  simp only [uniform]
  rw [← Finset.mul_sum, Finset.sum_boole, hset, Fintype.card_fun, Fintype.card_fin]
  push_cast at hsz ⊢
  rw [inv_mul_eq_div]
  exact hsz

end ML

end MIPRE.QLD

end
