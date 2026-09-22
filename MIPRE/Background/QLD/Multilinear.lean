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

omit [Fintype X] [DecidableEq X] in
/-- **Grouping an agreement by the common label.** Summing the Born probabilities of all outcome
pairs whose labels match is the same as summing the two coarse-grained measurements against each
other at each label. This is what lets the helper's agreement, which is stated at an outcome in
`F_q`, be read as an agreement between the polynomial-indexed marginal and a point-independent
family on the other party. -/
theorem sum_filter_bornProb_eq {C : Type*} [Fintype C] [DecidableEq C] (Φ : RA × RB → ℂ)
    (S : POVM G RA) (N : POVM K RB) (ev : G → C) (val : K → C) :
    ∑ g, ∑ k ∈ univ.filter fun k => val k = ev g,
        bornProb Φ ((S.mats g).val) ((N.mats k).val)
      = ∑ c, bornProb Φ (((S.map ev).mats c).val) (((N.map val).mats c).val) := by
  classical
  have hc : ∀ c : C, bornProb Φ (((S.map ev).mats c).val) (((N.map val).mats c).val)
      = ∑ g ∈ univ.filter fun g => ev g = c, ∑ k ∈ univ.filter fun k => val k = c,
          bornProb Φ ((S.mats g).val) ((N.mats k).val) := by
    intro c
    rw [POVM.map_mats, POVM.map_mats, bornProb_sum_left]
    exact Finset.sum_congr rfl fun g _ => bornProb_sum_right _ _ _ _
  rw [← Finset.sum_fiberwise (univ : Finset G) ev
      (fun g => ∑ k ∈ univ.filter fun k => val k = ev g,
        bornProb Φ ((S.mats g).val) ((N.mats k).val)),
    Finset.sum_congr rfl fun c (_ : c ∈ univ) => hc c]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun g hg => by
    rw [(Finset.mem_filter.mp hg).2]

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

/-! ## The marginal indexed by polynomials

`evalMarg` reads the pair measurement's `W` component through its value at the sampled point, so
the family it names depends on the point. The repaired argument needs a family that does not: the
Schwartz--Zippel bound is applied to a *fixed* outcome operator against a point drawn afterwards.
`polyMarg` is that family, and `evalMarg` is its coarse-graining at each point. -/

section PolyMarg

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {R : Type*} [Fintype R] [DecidableEq R]

/-- **The `W` marginal of a pair measurement, indexed by polynomials.** -/
def polyMarg (S : POVM (PolyPair F m d) R) (W : Bas) :
    POVM (LowIndDegPoly (F := F) (m := m) (d := d)) R :=
  S.map (PolyPair.proj W)

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- The evaluated marginal is the polynomial marginal read at the point. -/
theorem evalMarg_eq_map_polyMarg (S : POVM (PolyPair F m d) R) (W : Bas) (u : Point F m) :
    evalMarg S W u = (polyMarg S W).map fun g => g.eval u :=
  (POVM.map_map S (PolyPair.proj W) fun g => g.eval u).symm

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- The polynomial marginal of a projective pair measurement is projective. -/
theorem isPVM_polyMarg {S : POVM (PolyPair F m d) R} (hS : IsPVM fun p => ((S.mats p).val))
    (W : Bas) : IsPVM fun g => (((polyMarg S W).mats g).val) :=
  isPVM_povm_map S hS _

end PolyMarg

/-! ## The mass the simultaneous measurement puts on non-multilinear outcomes -/

section Bad

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/-- **The hatted Pauli family is projective**: a product of two projective measurements, coarse
grained along the sum of their outcomes. -/
theorem isPVM_hatPauli (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) :
    IsPVM fun k => (((hatPauli MB W).mats k).val) :=
  isPVM_povm_map _ (isPVM_povm_kron _ _ (isPVM_povm_map _ (hprojB _) _)
    (isPVM_synOfPOVM W id)) _

namespace SimulPair

variable (P : SimulPair ψ MA MB δ)

/-- **The substitution.** Replacing Bob's expanded point measurement by the point-independent
hatted Pauli family inside the helper's agreement costs `sqrt (688 eps)`: one Cauchy--Schwarz at
each point against Alice's projective marginal, then Jensen for the average over points. -/
theorem sum_bornProb_hatPauli_ge {hm : m ∣ Fintype.card F} {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    1 - δ - Real.sqrt (688 * ε) ≤ ∑ u, uniform (Point F m) u * ∑ a : F,
      bornProb P.Φ (((evalMarg P.SA W u).mats a).val)
        (aOp ((((hatPauli MB W).map fun k => dotF k (indVec u)).mats a).val)) := by
  classical
  have hT : ∀ u : Point F m, IsPVM fun a : F => (((evalMarg P.SA W u).mats a).val) := fun u =>
    isPVM_evalMarg P.SA_proj W u
  -- the hatted Pauli family, read at the point, is the convolution the closeness bound names
  have hC : ∀ (u : Point F m) (a : F),
      ((((hatPauli MB W).map fun k => dotF k (indVec u)).mats a).val)
        = ((((((MB (.pauli W)).map (rdPauli u)).kron (synPOVM W u)).map
            fun p => p.1 + p.2).mats a).val) := fun u a => by rw [hatPauli_map]
  set D : Point F m → F → Matrix (dB × Anc F m) (dB × Anc F m) ℂ := fun u a =>
    hatMats MB W u a - ((((hatPauli MB W).map fun k => dotF k (indVec u)).mats a).val) with hD
  -- the two agreements differ by the Born probabilities of the difference
  have hsplit : ∀ (u : Point F m) (a : F),
      bornProb P.Φ (((evalMarg P.SA W u).mats a).val) (aOp (hatMats MB W u a))
        = bornProb P.Φ (((evalMarg P.SA W u).mats a).val)
            (aOp ((((hatPauli MB W).map fun k => dotF k (indVec u)).mats a).val))
          + bornProb P.Φ (((evalMarg P.SA W u).mats a).val) (aOp (D u a)) := by
    intro u a
    rw [hD, aOp_sub, bornProb_sub_right]
    ring
  -- Cauchy--Schwarz, averaged
  have hcs : |∑ u, uniform (Point F m) u * ∑ a : F,
      bornProb P.Φ (((evalMarg P.SA W u).mats a).val) (aOp (D u a))|
      ≤ Real.sqrt (∑ u, uniform (Point F m) u * ∑ a : F,
        ‖stateVecB P.Φ (aOp (D u a) : Matrix ((dB × Anc F m) × P.EB) _ ℂ)‖ ^ 2) :=
    MIPRE.abs_sum_weighted_bornProb_le (uniform_nonneg (Point F m))
      (sum_uniform_eq_one (Point F m)) P.Φ_unit hT _
  -- the squared distance is the one on the expanded state, and it is at most `688 eps`
  have hnorm : ∀ (u : Point F m) (a : F),
      ‖stateVecB P.Φ (aOp (D u a) : Matrix ((dB × Anc F m) × P.EB) _ ℂ)‖ ^ 2
        = ‖stateVecB (hatVec (F := F) (m := m) ψ) (D u a)‖ ^ 2 := fun u a =>
    P.normSq_stateVecB_aOp _
  have h688 : ∑ u, uniform (Point F m) u * ∑ a : F,
      ‖stateVecB (hatVec (F := F) (m := m) ψ) (D u a)‖ ^ 2 ≤ 688 * ε := by
    have h := sum_normSq_hat_point_sub_pauli_le (MB := MB) (hm := hm) hψ hfail W
    rw [sum_content_pt W fun u => ∑ a : F, ‖stateVecB (hatVec (F := F) (m := m) ψ)
      ((((hatPtPOVM MB W u).mats a).val)
        - ((((((MB (.pauli W)).map (rdPauli u)).kron (synPOVM W u)).map
            fun p => p.1 + p.2).mats a).val))‖ ^ 2] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
    simp only [hD, hC u a, hatMats]
  -- assemble
  have hlow := P.sum_bornProb_evalMarg_ge (MB := MB) W
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hsplit u a, Finset.sum_add_distrib,
      mul_add]] at hlow
  rw [Finset.sum_add_distrib] at hlow
  have habs := abs_le.mp (hcs.trans (Real.sqrt_le_sqrt
    (le_trans (le_of_eq (Finset.sum_congr rfl fun u _ =>
      congrArg _ (Finset.sum_congr rfl fun a _ => hnorm u a))) h688)))
  linarith [habs.1, habs.2]

/-- **The mass at non-multilinear outcomes**, the critical step of
`lem:qld-construct-the-paulis`. Alice's polynomial-indexed marginal agrees, at a point sampled
*after* the operators are fixed, with the point-independent hatted Pauli family; a
non-multilinear outcome can agree with any one cube datum on at most an `md/q` fraction of points
(Schwartz--Zippel in the agreement direction); so the mass the marginal puts on non-multilinear
outcomes is at most the sum of the two. -/
theorem sum_bornProb_not_isML_le {hm : m ∣ Fintype.card F} {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (W : Bas) :
    ∑ g ∈ univ \ univ.filter (IsML (F := F) (m := m) (d := d)),
        bornProb P.Φ (((polyMarg P.SA W).mats g).val) 1
      ≤ (δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / Fintype.card F := by
  classical
  -- the agreement at a point, regrouped as a sum over matching outcome pairs
  have hreg : ∀ u : Point F m,
      (∑ g, ∑ k ∈ univ.filter fun k => dotF k (indVec u) = g.eval u,
          bornProb P.Φ (((polyMarg P.SA W).mats g).val) (aOp (((hatPauli MB W).mats k).val)))
        = ∑ a : F, bornProb P.Φ (((evalMarg P.SA W u).mats a).val)
            (aOp ((((hatPauli MB W).map fun k => dotF k (indVec u)).mats a).val)) := by
    intro u
    have h := MIPRE.sum_filter_bornProb_eq P.Φ (polyMarg P.SA W)
      ((hatPauli MB W).aOp (E := P.EB)) (fun g => g.eval u) fun k => dotF k (indVec u)
    simp only [POVM.aOp_mats] at h
    rw [h, ← POVM.map_aOp, ← evalMarg_eq_map_polyMarg]
    simp only [POVM.aOp_mats]
  -- the helper's agreement, after the substitution, in the shape the aggregation consumes
  have hlow : 1 - (δ + Real.sqrt (688 * ε))
      ≤ ∑ g, ∑ u, uniform (Point F m) u
          * ∑ k ∈ univ.filter fun k => dotF k (indVec u) = g.eval u,
            bornProb P.Φ (((polyMarg P.SA W).mats g).val)
              (aOp (((hatPauli MB W).mats k).val)) := by
    have h := P.sum_bornProb_hatPauli_ge (hm := hm) hψ hfail W
    rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [← hreg u]] at h
    simp only [Finset.mul_sum] at h
    rw [Finset.sum_comm] at h
    simp only [← Finset.mul_sum] at h
    linarith
  refine MIPRE.sum_mass_off_le (uniform_nonneg (Point F m)) (sum_uniform_eq_one (Point F m))
    P.Φ_unit (isPVM_polyMarg P.SA_proj W) (isPVM_hatPauli hprojB W).aOp
    (fun k u => dotF k (indVec u)) (fun g u => g.eval u) (by positivity) hlow ?_
  intro g hg k
  exact sum_uniform_agree_ldEnc_le hd (by simpa using hg) k

end SimulPair

end Bad

end MIPRE.QLD

end
