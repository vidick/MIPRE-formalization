/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Helper
public import MIPRE.Background.QLD.PauliBasis
public import MIPRE.Background.QLD.NonMultilinear

@[expose] public section

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

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The pair measurement is a
`SimulPair M S K ι δ` of a projective strategy `S` of a bipartite model `M`: its marginals are POVMs
in `K`'s first algebra, and the second player's expanded measurements --- the hatted point
measurement and the hatted Pauli basis measurement `hatPauli`, POVMs of the register model
`M.reg (Anc F m)` --- are read in `K` through the embedding `ι`. The aggregation and substitution
steps are stated in any bipartite model; the squared distance they meet is carried from the
register model to `K` exactly (`SimulPair.normSq_stateVecB_aOp`). The projectivity of the
strategy, a hypothesis of the matrix statements, is a field of `S`.
-/

noncomputable section

namespace MIPRE

open Finset

section Mass

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]
variable {G K X : Type*} [Fintype G] [DecidableEq G] [Fintype K] [DecidableEq K] [Fintype X]
  [DecidableEq X]

omit [DecidableEq K] [DecidableEq X] in
/-- **The aggregation step.** `S` is a projective measurement of one player and `N` one of the
other, `val` and `ev` two labellings by a field element at each question, and the agreement of `S`
with `N` under matching labels is at least `1 - η`. If off a set `ML` every outcome of `S` matches
every label of `N` with probability at most `c`, the mass of `S` off `ML` is at most `η + c`. -/
theorem sum_mass_off_le {F : Type*} [DecidableEq F] {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ : ∑ x, μ x = 1) {M : BipartiteModel 𝒞 𝒜 ℬ} (hM : ‖M.ψ‖ = 1) {S : G → 𝒜}
    (hS : IsPVMIn S) {N : K → ℬ} (hN : IsPVMIn N) (val : K → X → F) (ev : G → X → F)
    {ML : Finset G} {η c : ℝ} (hc : 0 ≤ c)
    (hlow : 1 - η ≤ ∑ g, ∑ x, μ x
      * ∑ k ∈ univ.filter fun k => val k x = ev g x, M.bornProb (S g) (N k))
    (hagree : ∀ g ∉ ML, ∀ k, ∑ x, μ x * (if val k x = ev g x then (1 : ℝ) else 0) ≤ c) :
    ∑ g ∈ univ \ ML, M.bornProb (S g) 1 ≤ η + c := by
  classical
  set Sw : G → ℝ := fun g => M.bornProb (S g) 1 with hSw
  set Tw : G → ℝ := fun g => ∑ x, μ x
    * ∑ k ∈ univ.filter fun k => val k x = ev g x, M.bornProb (S g) (N k) with hTw
  have hpos : ∀ (g : G) (k : K), 0 ≤ M.bornProb (S g) (N k) := fun g k =>
    M.bornProb_nonneg (hS.nonneg g) (hN.nonneg k)
  have hfull : ∀ g, ∑ k, M.bornProb (S g) (N k) = Sw g := fun g => by
    rw [hSw, ← M.bornProb_sum_right, hN.sum_eq_one]
  have hS0 : ∀ g, 0 ≤ Sw g := fun g => by
    rw [← hfull g]
    exact Finset.sum_nonneg fun k _ => hpos g k
  -- the total mass is one
  have hsum : ∑ g, Sw g = 1 := by
    rw [hSw]
    simp only []
    rw [← M.bornProb_sum_left, hS.sum_eq_one, M.bornProb_one_one hM]
  -- `T` is dominated by `S`
  have hdom : ∀ g, Tw g ≤ Sw g := fun g => by
    have hx : ∀ x : X, (∑ k ∈ univ.filter fun k => val k x = ev g x, M.bornProb (S g) (N k))
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
        * M.bornProb (S g) (N k) := by
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

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] [Fintype G]
  [DecidableEq G] [Fintype K] [DecidableEq K] [DecidableEq X] in
/-- **The averaged substitution estimate.** Against a projective family at each question, an
agreement with any family of the other player is bounded by the root of that family's average
weight: Cauchy--Schwarz at each question, then Jensen for the average. -/
theorem abs_sum_weighted_bornProb_le {C : Type*} [Fintype C] {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ : ∑ x, μ x = 1) {M : BipartiteModel 𝒞 𝒜 ℬ} (hM : ‖M.ψ‖ = 1) {T : X → C → 𝒜}
    (hT : ∀ x, IsPVMIn (T x)) (D : X → C → ℬ) :
    |∑ x, μ x * ∑ c, M.bornProb (T x c) (D x c)|
      ≤ Real.sqrt (∑ x, μ x * ∑ c, M.swap.stateSqNorm (D x c)) := by
  have hx : ∀ x, |∑ c, M.bornProb (T x c) (D x c)|
      ≤ Real.sqrt (∑ c, M.swap.stateSqNorm (D x c)) := fun x =>
    QLD.abs_sum_bornProb_le hM (hT x) (D x)
  have h1 : |∑ x, μ x * ∑ c, M.bornProb (T x c) (D x c)|
      ≤ ∑ x, μ x * Real.sqrt (∑ c, M.swap.stateSqNorm (D x c)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [abs_mul, abs_of_nonneg (hμ0 x)]
    exact mul_le_mul_of_nonneg_left (hx x) (hμ0 x)
  exact h1.trans (sum_weighted_sqrt_le μ _ hμ0 hμ
    fun x => Finset.sum_nonneg fun c _ => M.swap.stateSqNorm_nonneg _)

omit [Fintype X] [DecidableEq X] [DecidableEq G] [DecidableEq K] in
/-- **Grouping an agreement by the common label.** Summing the Born probabilities of all outcome
pairs whose labels match is the same as summing the two coarse-grained measurements against each
other at each label. This is what lets the helper's agreement, which is stated at an outcome in
`F_q`, be read as an agreement between the polynomial-indexed marginal and a point-independent
family of the other player. -/
theorem sum_filter_bornProb_eq {C : Type*} [Fintype C] [DecidableEq C]
    (M : BipartiteModel 𝒞 𝒜 ℬ) (S : POVMIn G 𝒜) (N : POVMIn K ℬ) (ev : G → C) (val : K → C) :
    ∑ g, ∑ k ∈ univ.filter fun k => val k = ev g, M.bornProb (S.op g) (N.op k)
      = ∑ c, M.bornProb ((S.map ev).op c) ((N.map val).op c) := by
  classical
  have hc : ∀ c : C, M.bornProb ((S.map ev).op c) ((N.map val).op c)
      = ∑ g ∈ univ.filter fun g => ev g = c, ∑ k ∈ univ.filter fun k => val k = c,
          M.bornProb (S.op g) (N.op k) := by
    intro c
    rw [POVMIn.map_op, POVMIn.map_op, M.bornProb_sum_left]
    exact Finset.sum_congr rfl fun g _ => M.bornProb_sum_right _ _ _
  rw [← Finset.sum_fiberwise (univ : Finset G) ev
      (fun g => ∑ k ∈ univ.filter fun k => val k = ev g, M.bornProb (S.op g) (N.op k)),
    Finset.sum_congr rfl fun c (_ : c ∈ univ) => hc c]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun g hg => by
    rw [(Finset.mem_filter.mp hg).2]

omit [Fintype X] [DecidableEq X] [DecidableEq G] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [Fintype K] [DecidableEq K] in
/-- **Reading a coarse-grained measurement against a family indexed by the labels** is reading the
original measurement against the family at its own label. -/
theorem sum_bornProb_map_eq {C : Type*} [Fintype C] [DecidableEq C] (M : BipartiteModel 𝒞 𝒜 ℬ)
    (S : POVMIn G 𝒜) (ev : G → C) (N : C → ℬ) :
    ∑ c, M.bornProb ((S.map ev).op c) (N c) = ∑ g, M.bornProb (S.op g) (N (ev g)) := by
  classical
  have hc : ∀ c : C, M.bornProb ((S.map ev).op c) (N c)
      = ∑ g ∈ univ.filter fun g => ev g = c, M.bornProb (S.op g) (N c) := fun c => by
    rw [POVMIn.map_op, M.bornProb_sum_left]
  have h2 : ∑ c, ∑ g ∈ univ.filter fun g => ev g = c, M.bornProb (S.op g) (N c)
      = ∑ g, M.bornProb (S.op g) (N (ev g)) := by
    rw [← Finset.sum_fiberwise (univ : Finset G) ev
      fun g => M.bornProb (S.op g) (N (ev g))]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun g hg => by
      rw [(Finset.mem_filter.mp hg).2]
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => hc c, h2]

omit [DecidableEq X] in
/-- **Averaging a pointwise bound on a difference.** -/
theorem abs_sum_weighted_sub_le {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ : ∑ x, μ x = 1)
    (f g : X → ℝ) {B : ℝ} (h : ∀ x, |f x - g x| ≤ B) :
    |∑ x, μ x * f x - ∑ x, μ x * g x| ≤ B := by
  have hrw : (∑ x, μ x * f x) - ∑ x, μ x * g x = ∑ x, μ x * (f x - g x) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hrw]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ x : X, |μ x * (f x - g x)| ≤ μ x * B := fun x => by
    rw [abs_mul, abs_of_nonneg (hμ0 x)]
    exact mul_le_mul_of_nonneg_left (h x) (hμ0 x)
  refine (Finset.sum_le_sum fun x _ => h1 x).trans ?_
  rw [← Finset.sum_mul, hμ, one_mul]

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

/-! ## Outcomes the Pauli construction reads correctly

`mTilde` labels the outcome `g` not by `g(u)` but by `\coded(g) . ind_m(u)`, the value at `u` of
the low-degree encoding of `g`'s values on the boolean cube. The two agree exactly on the outcomes
that *are* their own encoding, and the appendix's repair is to bound the mass off that set. `IsML`
is the syntactic version of the set; `IsInterp` is the semantic one, and it is the one the
construction needs, because it is also what makes Schwartz--Zippel apply off it. -/

/-- **The cube data of an outcome**: its values on `{0,1}^m`, the paper's `\coded(g)`. -/
def cubeData (g : LowIndDegPoly (F := F) (m := m) (d := d)) : Anc F m :=
  fun y => g.eval (pt y)

/-- **An outcome that is the low-degree encoding of its own cube data.** -/
def IsInterp (g : LowIndDegPoly (F := F) (m := m) (d := d)) : Prop :=
  g.toMv = ldEnc (cubeData g)

instance : DecidablePred (IsInterp (F := F) (m := m) (d := d)) := fun g =>
  inferInstanceAs (Decidable (g.toMv = ldEnc (cubeData g)))

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The cube data of an encoding is the data it encodes. -/
theorem cubeData_eq_of_eq_ldEnc {g : LowIndDegPoly (F := F) (m := m) (d := d)} {k : Anc F m}
    (h : g.toMv = ldEnc k) : cubeData g = k :=
  funext fun y => by rw [cubeData, ← LowIndDegPoly.eval_toMv, h, eval_ldEnc]

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- So being *some* encoding is being one's own. -/
theorem isInterp_of_exists {g : LowIndDegPoly (F := F) (m := m) (d := d)}
    (h : ∃ k : Anc F m, g.toMv = ldEnc k) : IsInterp g := by
  obtain ⟨k, hk⟩ := h
  rw [IsInterp, cubeData_eq_of_eq_ldEnc hk]
  exact hk

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- An outcome that is not an interpolant is distinct from the encoding of *every* cube datum,
which is what makes the Schwartz--Zippel bound below uniform in the datum. -/
theorem ne_ldEnc_of_not_isInterp {g : LowIndDegPoly (F := F) (m := m) (d := d)}
    (hg : ¬ IsInterp g) (k : Anc F m) : g.toMv ≠ ldEnc k :=
  fun h => hg (isInterp_of_exists ⟨k, h⟩)

/-- **On an interpolant the construction's label is the outcome's own value**, which is exactly
why the substitution is free there. -/
theorem dotF_cubeData_indVec {g : LowIndDegPoly (F := F) (m := m) (d := d)} (hg : IsInterp g)
    (u : Point F m) : dotF (cubeData g) (indVec u) = g.eval u := by
  rw [dotF_indVec, ← hg, LowIndDegPoly.eval_toMv]

/-- **Schwartz--Zippel off the interpolants**, uniformly in the cube datum. -/
theorem sum_uniform_agree_ldEnc_le_of_not_isInterp (hd : 1 ≤ d)
    {g : LowIndDegPoly (F := F) (m := m) (d := d)} (hg : ¬ IsInterp g) (k : Anc F m) :
    ∑ u, uniform (Point F m) u
        * (if dotF k (indVec u) = g.eval u then (1 : ℝ) else 0)
      ≤ (m : ℝ) * d / Fintype.card F := by
  have hsz := prob_agree_le_individualDegree (ne_ldEnc_of_not_isInterp hg k)
    (LowIndDegPoly.degreeOf_toMv_le g) fun i => (degreeOf_ldEnc_le k i).trans hd
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


/-! ## The marginal indexed by polynomials

`evalMarg` reads the pair measurement's `W` component through its value at the sampled point, so
the family it names depends on the point. The repaired argument needs a family that does not: the
Schwartz--Zippel bound is applied to a *fixed* outcome operator against a point drawn afterwards.
`polyMarg` is that family, and `evalMarg` is its coarse-graining at each point. -/

section PolyMarg

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- **The `W` marginal of a pair measurement, indexed by polynomials.** -/
def polyMarg (S : POVMIn (PolyPair F m d) R) (W : Bas) :
    POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) R :=
  S.map (PolyPair.proj W)

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- The evaluated marginal is the polynomial marginal read at the point. -/
theorem evalMarg_eq_map_polyMarg (S : POVMIn (PolyPair F m d) R) (W : Bas) (u : Point F m) :
    evalMarg S W u = (polyMarg S W).map fun g => g.eval u :=
  (POVMIn.map_map S (PolyPair.proj W) fun g => g.eval u).symm

omit [Field F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The polynomial marginal of a projective pair measurement is projective. -/
theorem isPVM_polyMarg {S : POVMIn (PolyPair F m d) R} (hS : IsPVMIn S.op) (W : Bas) :
    IsPVMIn (polyMarg S W).op :=
  POVMIn.isPVMIn_map hS _

end PolyMarg

/-! ## The mass the simultaneous measurement puts on non-multilinear outcomes -/

section Bad

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- **The hatted Pauli family is projective**: a product of two projective measurements, coarse
grained along the sum of their outcomes. -/
theorem isPVM_hatPauli {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    [PartialOrder R] [StarOrderedRing R] [StarProper R]
    {P : Question F m → POVMIn (Answer F m d) R} (hP : ∀ q, IsPVMIn (P q).op) (W : Bas) :
    IsPVMIn (hatPauli P W).op :=
  POVMIn.isPVMIn_map (isPVMIn_kronIn (POVMIn.isPVMIn_map (hP _) _) _ _) _

/-- An element of a coarse-graining of a pushed-forward POVM is the image of the element of the
coarse-graining. -/
private theorem map_pushforward_op {R R' Y Z : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
    [PartialOrder R] [StarOrderedRing R] [Ring R'] [StarRing R'] [Algebra ℂ R'] [PartialOrder R']
    [StarOrderedRing R'] [Fintype Y] [Fintype Z] [DecidableEq Z] (P : POVMIn Y R)
    (f : R →⋆ₙₐ[ℂ] R') (hf : f 1 = 1) (g : Y → Z) (z : Z) :
    ((P.pushforward f hf).map g).op z = f ((P.map g).op z) := by
  rw [POVMIn.map_op, POVMIn.map_op, map_sum]
  rfl

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ']

namespace SimulPair

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {K : BipartiteModel 𝒞' 𝒜' ℬ'}
  {ι : (M.reg (Anc F m)).Embedding K} {δ : ℝ}

variable (P : SimulPair M S K ι δ)

/-- **The substitution.** Replacing Bob's expanded point measurement by the point-independent
hatted Pauli family inside the helper's agreement costs `sqrt (688 eps)`: one Cauchy--Schwarz at
each point against Alice's projective marginal, then Jensen for the average over points. -/
theorem sum_bornProb_hatPauli_ge {ε : ℝ} (hfail : 1 - S.value ≤ ε) (W : Bas) :
    1 - δ - Real.sqrt (688 * ε) ≤ ∑ u, uniform (Point F m) u * ∑ a : F,
      K.bornProb ((evalMarg P.SA W u).op a)
        (ι.ΦB (((hatPauli S.PB W).map fun k => dotF k (indVec u)).op a)) := by
  classical
  have hT : ∀ u : Point F m, IsPVMIn (evalMarg P.SA W u).op := fun u =>
    isPVM_evalMarg P.SA_proj W u
  -- the hatted Pauli family, read at the point, is the convolution the closeness bound names
  have hC : ∀ (u : Point F m) (a : F),
      ((hatPauli S.PB W).map fun k => dotF k (indVec u)).op a
        = ((kronIn ((S.PB (.pauli W)).map (rdPauli u)) (synPOVM W u) (isPVM_synPOVM W u)).map
            fun p => p.1 + p.2).op a := fun u a => by rw [hatPauli_map]
  set D : Point F m → F → Matrix (Anc F m) (Anc F m) ℬ := fun u a =>
    hatMats S.PB W u a - ((hatPauli S.PB W).map fun k => dotF k (indVec u)).op a with hD
  -- the two agreements differ by the Born probabilities of the difference
  have hsplit : ∀ (u : Point F m) (a : F),
      K.bornProb ((evalMarg P.SA W u).op a) (ι.ΦB (hatMats S.PB W u a))
        = K.bornProb ((evalMarg P.SA W u).op a)
            (ι.ΦB (((hatPauli S.PB W).map fun k => dotF k (indVec u)).op a))
          + K.bornProb ((evalMarg P.SA W u).op a) (ι.ΦB (D u a)) := by
    intro u a
    rw [hD, map_sub, K.bornProb_sub_right]
    ring
  -- Cauchy--Schwarz, averaged
  have hcs : |∑ u, uniform (Point F m) u * ∑ a : F,
      K.bornProb ((evalMarg P.SA W u).op a) (ι.ΦB (D u a))|
      ≤ Real.sqrt (∑ u, uniform (Point F m) u * ∑ a : F, K.swap.stateSqNorm (ι.ΦB (D u a))) :=
    MIPRE.abs_sum_weighted_bornProb_le (uniform_nonneg (Point F m))
      (sum_uniform_eq_one (Point F m)) P.ψ_unit hT _
  -- the squared distance is the one on the expanded state, and it is at most `688 eps`
  have hnorm : ∀ (u : Point F m) (a : F),
      K.swap.stateSqNorm (ι.ΦB (D u a)) = (M.reg (Anc F m)).swap.stateSqNorm (D u a) :=
    fun u a => P.normSq_stateVecB_aOp _
  have h688 : ∑ u, uniform (Point F m) u * ∑ a : F,
      (M.reg (Anc F m)).swap.stateSqNorm (D u a) ≤ 688 * ε := by
    have h := sum_normSq_hat_point_sub_pauli_le (PB := S.PB) (hm := hm) S.ψ_unit hfail W
    rw [sum_content_pt W fun u => ∑ a : F, (M.reg (Anc F m)).swap.stateSqNorm
      ((hatPtPOVM S.PB W u).op a
        - ((kronIn ((S.PB (.pauli W)).map (rdPauli u)) (synPOVM W u) (isPVM_synPOVM W u)).map
            fun p => p.1 + p.2).op a)] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
    simp only [hD, hC u a, hatMats]
  -- assemble
  have hlow := P.sum_bornProb_evalMarg_ge W
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hsplit u a, Finset.sum_add_distrib,
      mul_add]] at hlow
  rw [Finset.sum_add_distrib] at hlow
  have habs := abs_le.mp (hcs.trans (Real.sqrt_le_sqrt
    (le_trans (le_of_eq (Finset.sum_congr rfl fun u _ =>
      congrArg _ (Finset.sum_congr rfl fun a _ => hnorm u a))) h688)))
  linarith [habs.1, habs.2]

/-- **The mass off a set of outcomes**, the critical step of `lem:qld-construct-the-paulis`.
Alice's polynomial-indexed marginal agrees, at a point sampled *after* the operators are fixed,
with the point-independent hatted Pauli family; if off `ML` an outcome can agree with any one cube
datum with probability at most `c`, the mass the marginal puts off `ML` is at most the sum of the
two errors. -/
theorem sum_bornProb_off_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (W : Bas)
    {ML : Finset (LowIndDegPoly (F := F) (m := m) (d := d))} {c : ℝ} (hc : 0 ≤ c)
    (hagree : ∀ g ∉ ML, ∀ k : Anc F m, ∑ u, uniform (Point F m) u
      * (if dotF k (indVec u) = g.eval u then (1 : ℝ) else 0) ≤ c) :
    ∑ g ∈ univ \ ML, K.bornProb ((polyMarg P.SA W).op g) 1
      ≤ (δ + Real.sqrt (688 * ε)) + c := by
  classical
  -- the agreement at a point, regrouped as a sum over matching outcome pairs
  have hreg : ∀ u : Point F m,
      (∑ g, ∑ k ∈ univ.filter fun k => dotF k (indVec u) = g.eval u,
          K.bornProb ((polyMarg P.SA W).op g) (ι.ΦB ((hatPauli S.PB W).op k)))
        = ∑ a : F, K.bornProb ((evalMarg P.SA W u).op a)
            (ι.ΦB (((hatPauli S.PB W).map fun k => dotF k (indVec u)).op a)) := by
    intro u
    have h := MIPRE.sum_filter_bornProb_eq K (polyMarg P.SA W)
      ((hatPauli S.PB W).pushforward ι.ΦB ι.ΦB_one) (fun g => g.eval u)
      fun k => dotF k (indVec u)
    simp only [POVMIn.pushforward_op, map_pushforward_op] at h
    rw [h, ← evalMarg_eq_map_polyMarg]
  -- the helper's agreement, after the substitution, in the shape the aggregation consumes
  have hlow : 1 - (δ + Real.sqrt (688 * ε))
      ≤ ∑ g, ∑ u, uniform (Point F m) u
          * ∑ k ∈ univ.filter fun k => dotF k (indVec u) = g.eval u,
            K.bornProb ((polyMarg P.SA W).op g) (ι.ΦB ((hatPauli S.PB W).op k)) := by
    have h := P.sum_bornProb_hatPauli_ge hfail W
    rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [← hreg u]] at h
    simp only [Finset.mul_sum] at h
    rw [Finset.sum_comm] at h
    simp only [← Finset.mul_sum] at h
    linarith
  exact MIPRE.sum_mass_off_le (uniform_nonneg (Point F m)) (sum_uniform_eq_one (Point F m))
    P.ψ_unit (isPVM_polyMarg P.SA_proj W) ((isPVM_hatPauli S.projB W).pushforward ι.ΦB_one)
    (fun k u => dotF k (indVec u)) (fun g u => g.eval u) hc hlow hagree

/-- **The mass at non-multilinear outcomes.** -/
theorem sum_bornProb_not_isML_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d) (W : Bas) :
    ∑ g ∈ univ \ univ.filter (IsML (F := F) (m := m) (d := d)),
        K.bornProb ((polyMarg P.SA W).op g) 1
      ≤ (δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / Fintype.card F :=
  P.sum_bornProb_off_le hfail W (by positivity)
    fun g hg k => sum_uniform_agree_ldEnc_le hd (by simpa using hg) k

/-- **The mass at outcomes that are not the encoding of their own cube data** --- the form the
Pauli construction consumes, since it is exactly off this set that its label differs from the
outcome's own value. -/
theorem sum_bornProb_not_isInterp_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d)
    (W : Bas) :
    ∑ g ∈ univ \ univ.filter (IsInterp (F := F) (m := m) (d := d)),
        K.bornProb ((polyMarg P.SA W).op g) 1
      ≤ (δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / Fintype.card F :=
  P.sum_bornProb_off_le hfail W (by positivity)
    fun g hg k => sum_uniform_agree_ldEnc_le_of_not_isInterp hd (by simpa using hg) k

/-- The helper's agreement, regrouped by the outcome polynomial rather than by its value. -/
theorem sum_bornProb_polyMarg_ge (W : Bas) :
    1 - δ ≤ ∑ u, uniform (Point F m) u * ∑ g,
      K.bornProb ((polyMarg P.SA W).op g) (ι.ΦB (hatMats S.PB W u (g.eval u))) := by
  have h := P.sum_bornProb_evalMarg_ge W
  have hu : ∀ u : Point F m,
      (∑ a : F, K.bornProb ((evalMarg P.SA W u).op a) (ι.ΦB (hatMats S.PB W u a)))
        = ∑ g, K.bornProb ((polyMarg P.SA W).op g) (ι.ΦB (hatMats S.PB W u (g.eval u))) := by
    intro u
    rw [evalMarg_eq_map_polyMarg]
    exact MIPRE.sum_bornProb_map_eq K (polyMarg P.SA W) (fun g => g.eval u)
      fun a => ι.ΦB (hatMats S.PB W u a)
  rwa [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [hu u]] at h

/-- **`lem:qld-exact-paulis`, item 1, as the agreement the appendix's chain establishes.**

`mTilde` reads the outcome `g` through the value at `u` of the encoding of its cube data,
`\coded(g) . ind_m(u)`, and not through `g(u)`; expanding its definition and contracting the
generalized Pauli on the opposite party's ancilla against the strategy's point measurement turns
the agreement of `mTilde` with `M^{(Point,W),u}` into the left-hand side below. It differs from
the helper's agreement only at outcomes that are not their own encoding, where the two labels can
differ, and each term is at most the outcome's own weight; so twice the mass off the interpolants
pays for the substitution. -/
theorem sum_bornProb_cubeData_ge {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d) (W : Bas) :
    1 - (δ + 2 * ((δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / Fintype.card F))
      ≤ ∑ u, uniform (Point F m) u * ∑ g,
          K.bornProb ((polyMarg P.SA W).op g)
            (ι.ΦB (hatMats S.PB W u (dotF (cubeData g) (indVec u)))) := by
  classical
  -- each term is at most the outcome's own weight
  have habs : ∀ (g : LowIndDegPoly (F := F) (m := m) (d := d)) (u : Point F m) (a : F),
      |K.bornProb ((polyMarg P.SA W).op g) (ι.ΦB (hatMats S.PB W u a))|
        ≤ K.bornProb ((polyMarg P.SA W).op g) 1 := by
    intro g u a
    have h0 : 0 ≤ K.bornProb ((polyMarg P.SA W).op g) (ι.ΦB (hatMats S.PB W u a)) :=
      K.bornProb_nonneg ((polyMarg P.SA W).op_nonneg g)
        (((hatPtPOVM S.PB W u).pushforward ι.ΦB ι.ΦB_one).op_nonneg a)
    rw [abs_of_nonneg h0]
    exact bornProb_mono_right K ((polyMarg P.SA W).op_nonneg g)
      (((hatPtPOVM S.PB W u).pushforward ι.ΦB ι.ΦB_one).op_le_one a)
  -- and the two labels agree on the interpolants
  have hbd : ∀ u : Point F m,
      |(∑ g, K.bornProb ((polyMarg P.SA W).op g)
            (ι.ΦB (hatMats S.PB W u (dotF (cubeData g) (indVec u)))))
          - ∑ g, K.bornProb ((polyMarg P.SA W).op g) (ι.ΦB (hatMats S.PB W u (g.eval u)))|
        ≤ 2 * ∑ g ∈ univ \ univ.filter (IsInterp (F := F) (m := m) (d := d)),
            K.bornProb ((polyMarg P.SA W).op g) 1 := fun u =>
    sum_sub_le_of_eq_on
      (fun g hg => by rw [dotF_cubeData_indVec (Finset.mem_filter.mp hg).2 u])
      (fun g => habs g u _) fun g => habs g u _
  have havg := MIPRE.abs_sum_weighted_sub_le (uniform_nonneg (Point F m))
    (sum_uniform_eq_one (Point F m))
    (fun u => ∑ g, K.bornProb ((polyMarg P.SA W).op g)
      (ι.ΦB (hatMats S.PB W u (dotF (cubeData g) (indVec u)))))
    (fun u => ∑ g, K.bornProb ((polyMarg P.SA W).op g)
      (ι.ΦB (hatMats S.PB W u (g.eval u)))) hbd
  have h2 := abs_le.mp havg
  have hlow := P.sum_bornProb_polyMarg_ge W
  have hmass := P.sum_bornProb_not_isInterp_le hfail hd W
  linarith [h2.1, h2.2]

end SimulPair

end Bad

end MIPRE.QLD

end

end
