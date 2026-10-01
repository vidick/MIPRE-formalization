/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Dummy
public import MIPRE.Foundations.ModelCalculus

@[expose] public section

/-!
# Ordered products with global outcome multipliers (`lem:qld-global-products`)

The global measurement of `lem:qld-global-pvm` is consistent, on average over a uniform padded
point `u = (x, z, α, β, w)`, with the *sandwich combination*
`P_u(c) = ∑_{αa + βb = c} Z_b X_a Z_b` of Bob's expanded point measurements. Stage 4b needs the
same statement for the two *ordered products* `∑_{αa + βb = c} Z_b X_a` and
`∑_{αa + βb = c} X_a Z_b`, in the state-distance form: with `v_g = (G_g ⊗ 1) Φ`,
`∑_g E_u ‖v_g - (1 ⊗ B_u(g(u))) v_g‖² ≤ 2δ + 2κ`, where `δ` is the consistency error and `κ` the
average commutator weight `E_{x,z} ∑_{a,b} ‖(1 ⊗ [X_a, Z_b]) Φ‖²` of Bob's two measurements.

## The argument

Two steps. `(1 ⊗ (1 - P)) v_g` is controlled by the consistency itself, because `0 ≤ P ≤ 1` gives
`(1 - P)² ≤ 1 - P` and so `∑_g E ‖(G_g ⊗ (1 - P_u(g(u)))) Φ‖² ≤ ∑_g E ⟨G_g ⊗ (1 - P_u(g(u)))⟩ ≤ δ`.
`(1 ⊗ (P - B)) v_g` is controlled by the commutators: grouping the outcomes by their value
`c = g(u)` and dropping the projector `∑_{g(u) = c} G_g ≤ 1` leaves
`∑_c ‖(1 ⊗ (P_u(c) - B_u(c))) Φ‖²`,
a fibre-summed family of the deviations `sand - ord`; these sum to zero over `(a, b)`, so Parseval
over `F_q` (`BipartiteModel.sum_avg_stateSqNorm_fibre_eq`) turns the average over `(α, β)` of the
fibre sums into `(1 - 1/q) ∑_{a,b} ‖(1 ⊗ (sand - ord)(a, b)) Φ‖²` with no loss of a factor `q`, and
each deviation is a contraction of a commutator: `Z X Z - Z X = Z [X, Z]` and
`Z X Z - X Z = -(1 - Z) [X, Z]`.

Everything here is stated for abstract projective families `X x`, `Z z` of the second player,
with the consistency and the commutator weight as hypotheses; `lem:qld-global-pvm` and
`lem:qld-combined-points` supply them for the padded strategy.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The state is that of a
bipartite model `K` (the model in which the low individual degree test is applied, `padModel`,
or any other), the global measurement `G` is a projective POVM in the first player's algebra, and
the two families `X x`, `Z z` are projective measurements in the second player's. A Kronecker
product `G_g ⊗ D` is `K.πA (G.op g) * K.πB D`, its state norm is `K.snorm`, and the second
player's squared norm `‖(1 ⊗ D) Φ‖²` is `K.swap.stateSqNorm D`. The ordered products, the
commutator and the combinations are defined in any ring. The step `(1 - P)² ≤ 1 - P` is taken on
the represented operators, where the functional calculus lives (`mul_self_le_self_of_le_one`),
and Parseval is the model's (`BipartiteModel.sum_avg_stateSqNorm_fibre_eq` in `K.swap`).
-/

noncomputable section

namespace MIPRE

open Finset

section Generic

/-- An element of a projective measurement is at most one, in a star-ordered ring. -/
theorem IsPVMIn.le_one {R Λ : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    [Fintype Λ] {P : Λ → R} (h : IsPVMIn P) (a : Λ) : P a ≤ 1 := by
  rw [← h.sum_eq_one]
  exact Finset.single_le_sum (fun b _ => h.nonneg b) (Finset.mem_univ a)

/-- The complement of a projection is a contraction, in a star-ordered ring. -/
theorem one_sub_proj_conjTranspose_mul_self_le_one {R : Type*} [Ring R] [StarRing R]
    [PartialOrder R] [StarOrderedRing R] {P : R} (hsa : star P = P) (hidem : P * P = P) :
    star (1 - P) * (1 - P) ≤ 1 := by
  have hsa' : star (1 - P) = 1 - P := by rw [star_sub, star_one, hsa]
  have hidem' : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hidem]
    abel
  rw [hsa', hidem']
  exact sub_le_self 1 (posSemidef_of_proj hsa hidem)

/-- `‖T + T'‖² ≤ 2 ‖T‖² + 2 ‖T'‖²` in the state norm of a state model. -/
theorem snorm_sq_add_le {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (M : StateModel 𝒞)
    (T T' : 𝒞) : M.snorm (T + T') ^ 2 ≤ 2 * M.snorm T ^ 2 + 2 * M.snorm T' ^ 2 := by
  have h := M.snorm_add_le T T'
  have h0 := M.snorm_nonneg (T + T')
  nlinarith [sq_nonneg (M.snorm T - M.snorm T')]

end Generic

section Born

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **`Q² ≤ Q` for `0 ≤ Q ≤ 1`, read through a Born probability**: against a nonnegative element
of the first player, `⟨S ⊗ Q²⟩ ≤ ⟨S ⊗ Q⟩`. The inequality `Q² ≤ Q` is taken on the represented
operator (`Op.mul_self_le_self`), where the functional calculus lives; the second player's
algebra need not have one. -/
theorem mul_self_le_self_of_le_one (M : BipartiteModel 𝒞 𝒜 ℬ) {S : 𝒜} (hS : 0 ≤ S) {Q : ℬ}
    (h0 : 0 ≤ Q) (h1 : Q ≤ 1) : M.bornProb S (Q * Q) ≤ M.bornProb S Q := by
  have hD : 0 ≤ M.π (M.πB (Q - Q * Q)) := by
    simp only [map_sub, map_mul]
    exact sub_nonneg.2 (Op.mul_self_le_self (M.π_πB_nonneg h0) (M.swap.π_πA_le_one h1))
  have h : 0 ≤ M.bornProb S (Q - Q * Q) := by
    refine M.qform_nonneg ?_
    rw [map_mul]
    exact ((M.commute S (Q - Q * Q)).map M.π).mul_nonneg (M.π_πA_nonneg hS) hD
  rw [M.bornProb_sub_right] at h
  linarith

/-- The Born probability is monotone in the first player's operator when the second player's is
nonnegative. -/
theorem bornProb_mono_left (M : BipartiteModel 𝒞 𝒜 ℬ) {X X' : 𝒜} (h : X ≤ X') {Y : ℬ}
    (hY : 0 ≤ Y) : M.bornProb X Y ≤ M.bornProb X' Y := by
  rw [← M.bornProb_swap X Y, ← M.bornProb_swap X' Y]
  exact bornProb_mono_right M.swap hY h

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- `⟨ψ| 1 ⊗ D⋆ D |ψ⟩ = ‖(1 ⊗ D) ψ‖²`: the second player's squared state norm. -/
theorem bornProb_one_eq_normSq_stateVecB (M : BipartiteModel 𝒞 𝒜 ℬ) (D : ℬ) :
    M.bornProb 1 (star D * D) = M.swap.stateSqNorm D := by
  rw [M.swap.stateSqNorm_eq_bornProb_one D, M.bornProb_swap]

/-- The deviation of a projective outcome family from a family of the second player, grouped by
a value map: the first player's projection `∑_{f g = c} G_g ≤ 1` is dropped. -/
theorem sum_snorm_sq_aOp_mul_bOp_le (M : BipartiteModel 𝒞 𝒜 ℬ) {Λ C : Type*} [Fintype Λ]
    [Fintype C] [DecidableEq C] {G : Λ → 𝒜} (hG : IsPVMIn G) (f : Λ → C) (D : C → ℬ) :
    ∑ g, M.snorm (M.πA (G g) * M.πB (D (f g))) ^ 2 ≤ ∑ c, M.swap.stateSqNorm (D c) := by
  classical
  have hterm : ∀ g, M.snorm (M.πA (G g) * M.πB (D (f g))) ^ 2
      = M.bornProb (G g) (star (D (f g)) * D (f g)) := fun g =>
    M.snorm_sq_πA_mul_πB (hG.isStarProjection g) _
  simp_rw [hterm]
  rw [← Finset.sum_fiberwise univ f]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Finset.sum_congr rfl fun g hg => by rw [(mem_filter.mp hg).2], ← M.bornProb_sum_left,
    ← bornProb_one_eq_normSq_stateVecB]
  refine bornProb_mono_left M ?_ (star_mul_self_nonneg _)
  rw [← hG.sum_eq_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun g _ _ => hG.nonneg g

end Born

end MIPRE

namespace MIPRE.QLD

open Finset MIPRE MIPRE.LIDT

/-! ## The two ordered products and the commutator -/

section Ord

variable {F : Type*} {R : Type*}

/-- The ordered product, `X` then `Z` (applied right to left: `Z_b X_a`). -/
def ordZX [Mul R] (X Z : F → R) (p : F × F) : R := Z p.2 * X p.1

/-- The ordered product, `Z` then `X`: `X_a Z_b`. -/
def ordXZ [Mul R] (X Z : F → R) (p : F × F) : R := X p.1 * Z p.2

/-- The commutator `X_a Z_b - Z_b X_a`. -/
def comm [Ring R] (X Z : F → R) (p : F × F) : R := X p.1 * Z p.2 - Z p.2 * X p.1

variable [Fintype F] [Ring R] [StarRing R] {X Z : F → R}

theorem sum_ordZX (hX : IsPVMIn X) (hZ : IsPVMIn Z) : ∑ p : F × F, ordZX X Z p = 1 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [ordZX, ← Finset.mul_sum, hX.sum_eq_one, mul_one]
  exact hZ.sum_eq_one

theorem sum_ordXZ (hX : IsPVMIn X) (hZ : IsPVMIn Z) : ∑ p : F × F, ordXZ X Z p = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [ordXZ, ← Finset.mul_sum, hZ.sum_eq_one, mul_one]
  exact hX.sum_eq_one

/-- `Z X Z - Z X = Z [X, Z]`. -/
theorem sand_sub_ordZX (hZ : IsPVMIn Z) (p : F × F) :
    sand X Z p - ordZX X Z p = Z p.2 * comm X Z p := by
  simp only [sand, ordZX, comm, mul_sub, ← mul_assoc, hZ.idem]

/-- `Z X Z - X Z = -(1 - Z) [X, Z]`. -/
theorem sand_sub_ordXZ (hZ : IsPVMIn Z) (p : F × F) :
    sand X Z p - ordXZ X Z p = -((1 - Z p.2) * comm X Z p) := by
  have h : (1 - Z p.2) * comm X Z p = X p.1 * Z p.2 - Z p.2 * X p.1 * Z p.2 := by
    simp only [comm, sub_mul, one_mul, mul_sub, ← mul_assoc, hZ.idem]
    abel
  rw [h, sand, ordXZ]
  abel

end Ord

section OrdNorm

variable {F : Type*} [Fintype F] {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜]
  [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] {X Z : F → ℬ}

/-- The deviation of the sandwich from the order `Z_b X_a` is at most the commutator, in the
second player's state norm. -/
theorem norm_stateVecB_sand_sub_ordZX_le (hZ : IsPVMIn Z) (K : BipartiteModel 𝒞 𝒜 ℬ)
    (p : F × F) :
    K.swap.stateNorm (sand X Z p - ordZX X Z p) ≤ K.swap.stateNorm (comm X Z p) := by
  rw [sand_sub_ordZX hZ]
  exact K.swap.stateNorm_mul_le (K.swap.bnd_πA_of_isStarProjection (hZ.isStarProjection _)) _

/-- The deviation of the sandwich from the order `X_a Z_b` is at most the commutator, in the
second player's state norm. -/
theorem norm_stateVecB_sand_sub_ordXZ_le [PartialOrder ℬ] [StarOrderedRing ℬ] (hZ : IsPVMIn Z)
    (K : BipartiteModel 𝒞 𝒜 ℬ) (p : F × F) :
    K.swap.stateNorm (sand X Z p - ordXZ X Z p) ≤ K.swap.stateNorm (comm X Z p) := by
  rw [sand_sub_ordXZ hZ, ← neg_one_smul ℂ ((1 - Z p.2) * comm X Z p), K.swap.stateNorm_smul,
    norm_neg, norm_one, one_mul]
  exact K.swap.stateNorm_mul_le (K.swap.bnd_πA_of_star_mul_self_le
    (one_sub_proj_conjTranspose_mul_self_le_one (hZ.star_eq _) (hZ.idem _))) _

end OrdNorm

/-! ## The averaged fibre bound -/

section Fibre

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] {X Z : F → ℬ}

/-- **The fibre sums of `sand - ord` are controlled by the commutators**, on average over the
combining coefficients and without a factor `q`, for either order. -/
theorem sum_avg_fibre_sand_sub_ord_le (hX : IsPVMIn X) (hZ : IsPVMIn Z)
    (K : BipartiteModel 𝒞 𝒜 ℬ) {ord : (F → ℬ) → (F → ℬ) → F × F → ℬ}
    (hord1 : ∑ p : F × F, ord X Z p = 1)
    (hordle : ∀ p, K.swap.stateNorm (sand X Z p - ord X Z p) ≤ K.swap.stateNorm (comm X Z p)) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ c : F, K.swap.stateSqNorm (ptComb (fun p => sand X Z p - ord X Z p) ab.1 ab.2 c)
      ≤ ∑ p : F × F, K.swap.stateSqNorm (comm X Z p) := by
  rw [show (∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ c : F, K.swap.stateSqNorm (ptComb (fun p => sand X Z p - ord X Z p) ab.1 ab.2 c))
      = (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, K.swap.stateSqNorm (sand X Z p - ord X Z p)
      from K.swap.sum_avg_stateSqNorm_fibre_eq (E := fun p => sand X Z p - ord X Z p)
        (by rw [Finset.sum_sub_distrib, hX.sum_sand hZ, hord1, sub_self])]
  calc (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, K.swap.stateSqNorm (sand X Z p - ord X Z p)
      ≤ 1 * ∑ p : F × F, K.swap.stateSqNorm (comm X Z p) := by
        refine mul_le_mul
          (by linarith [inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ _)])
          (Finset.sum_le_sum fun p _ =>
            pow_le_pow_left₀ (K.swap.stateNorm_nonneg _) (hordle p) 2)
          (Finset.sum_nonneg fun p _ => K.swap.stateSqNorm_nonneg _) (by norm_num)
    _ = _ := one_mul _

end Fibre

/-! ## The uniform padded point as its blocks and combining coefficients -/

section Pad

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]

/-- Setting the two combining coordinates of a padded point. -/
def setAB (u : Point F (4 * m)) (α β : F) : Point F (4 * m) :=
  Function.update (Function.update u (aIdx m) α) (bIdx m) β

omit [Field F] [Fintype F] [DecidableEq F] in
theorem xBlk_setAB (u : Point F (4 * m)) (α β : F) : xBlk (setAB u α β) = xBlk u :=
  funext fun i => by
    simp only [xBlk_apply, setAB]
    rw [Function.update_of_ne (xIdx_ne_bIdx i), Function.update_of_ne (xIdx_ne_aIdx i)]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem zBlk_setAB (u : Point F (4 * m)) (α β : F) : zBlk (setAB u α β) = zBlk u :=
  funext fun i => by
    simp only [zBlk_apply, setAB]
    rw [Function.update_of_ne (zIdx_ne_bIdx i), Function.update_of_ne (zIdx_ne_aIdx i)]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem alph_setAB (u : Point F (4 * m)) (α β : F) : alph (setAB u α β) = α := by
  simp only [alph, setAB]
  rw [Function.update_of_ne aIdx_ne_bIdx, Function.update_self]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem bet_setAB (u : Point F (4 * m)) (α β : F) : bet (setAB u α β) = β := by
  simp only [bet, setAB]
  rw [Function.update_self]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem setAB_setAB (u : Point F (4 * m)) (α β : F) : setAB (setAB u α β) (alph u) (bet u) = u := by
  funext i
  by_cases hb : i = bIdx m
  · subst hb
    simp only [setAB, bet, Function.update_self]
  · by_cases ha : i = aIdx m
    · subst ha
      simp only [setAB, alph]
      rw [Function.update_of_ne aIdx_ne_bIdx, Function.update_self]
    · simp only [setAB]
      rw [Function.update_of_ne hb, Function.update_of_ne ha, Function.update_of_ne hb,
        Function.update_of_ne ha]

/-- The involution of `(point, α, β)` exchanging the combining coordinates with `(α, β)`. -/
def abSwap : Point F (4 * m) × F × F ≃ Point F (4 * m) × F × F where
  toFun p := (setAB p.1 p.2.1 p.2.2, alph p.1, bet p.1)
  invFun p := (setAB p.1 p.2.1 p.2.2, alph p.1, bet p.1)
  left_inv _ := Prod.ext (setAB_setAB _ _ _) (Prod.ext (alph_setAB _ _ _) (bet_setAB _ _ _))
  right_inv _ := Prod.ext (setAB_setAB _ _ _) (Prod.ext (alph_setAB _ _ _) (bet_setAB _ _ _))

omit [Field F] [DecidableEq F] in
/-- Reading a padded point's blocks and combining coordinates is reading its blocks and a fresh
uniform pair. -/
theorem sum_pad_ab (f : Point F m → Point F m → F → F → ℝ) :
    ∑ p : Point F (4 * m) × F × F, f (xBlk p.1) (zBlk p.1) p.2.1 p.2.2
      = ((Fintype.card F : ℝ) * Fintype.card F)
          * ∑ u : Point F (4 * m), f (xBlk u) (zBlk u) (alph u) (bet u) := by
  have h := Equiv.sum_comp abSwap
    (fun p : Point F (4 * m) × F × F => f (xBlk p.1) (zBlk p.1) (alph p.1) (bet p.1))
  simp only [abSwap, Equiv.coe_fn_mk, xBlk_setAB, zBlk_setAB, alph_setAB, bet_setAB] at h
  rw [h, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul]
  rw [Finset.mul_sum]

/-- **The uniform padded point, read through its blocks and combining coordinates**: the average
over `u ∈ F^{4m}` of a function of `(xBlk u, zBlk u, alph u, bet u)` is the average over
independent uniform `x, z ∈ F^m` and `(α, β) ∈ F²`. -/
theorem sum_uniform_pad4 (f : Point F m → Point F m → F → F → ℝ) :
    ∑ u, uniform (Point F (4 * m)) u * f (xBlk u) (zBlk u) (alph u) (bet u)
      = ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
          * ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) * f x z ab.1 ab.2 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hpad : ∑ u : Point F (4 * m), f (xBlk u) (zBlk u) (alph u) (bet u)
      = ((Fintype.card F : ℝ) * Fintype.card F)⁻¹
          * ∑ ab : F × F, (Fintype.card F : ℝ) ^ (2 * m) * ∑ x, ∑ z, f x z ab.1 ab.2 := by
    rw [eq_inv_mul_iff_mul_eq₀ (mul_ne_zero hq hq), ← sum_pad_ab f, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [sum_point_pad (fun x z => f x z ab.1 ab.2), nsmul_eq_mul, Fintype.card_fun,
      Fintype.card_fin]
    push_cast
    rfl
  have hswap : ∑ ab : F × F, ∑ x, ∑ z, f x z ab.1 ab.2
      = ∑ x, ∑ z, ∑ ab : F × F, f x z ab.1 ab.2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  simp only [uniform, Fintype.card_fun, Fintype.card_fin, ← Finset.mul_sum]
  rw [hpad, ← Finset.mul_sum, hswap]
  push_cast
  field_simp
  ring

end Pad

/-! ## The lemma -/

section Products

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- The sandwich combination at a padded point, `P_u(c) = ∑_{αa + βb = c} Z_b X_a Z_b`, for
abstract point measurements `X x`, `Z z` in a ring. -/
def sandComb {R : Type*} [Ring R] (X Z : Point F m → F → R) (u : Point F (4 * m)) (c : F) : R :=
  ptComb (sand (X (xBlk u)) (Z (zBlk u))) (alph u) (bet u) c

/-- An ordered-product combination at a padded point, `∑_{αa + βb = c} ord(a, b)`. -/
def ordComb {R : Type*} [Ring R] (ord : (F → R) → (F → R) → F × F → R)
    (X Z : Point F m → F → R) (u : Point F (4 * m)) (c : F) : R :=
  ptComb (ord (X (xBlk u)) (Z (zBlk u))) (alph u) (bet u) c

section Ring

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem ptComb_posSemidef {Q : F × F → R} (hQ : ∀ p, 0 ≤ Q p) (a b c : F) :
    0 ≤ ptComb Q a b c :=
  Finset.sum_nonneg fun p _ => hQ p

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem ptComb_le_one {Q : F × F → R} (hQ : ∀ p, 0 ≤ Q p) (hsum : ∑ p, Q p = 1) (a b c : F) :
    ptComb Q a b c ≤ 1 := by
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => hQ p

omit [PartialOrder R] [StarOrderedRing R] [Algebra (ZMod 2) F] [NeZero m] in
theorem ptComb_conjTranspose {Q : F × F → R} (hQ : ∀ p, star (Q p) = Q p) (a b c : F) :
    star (ptComb Q a b c) = ptComb Q a b c := by
  rw [ptComb, star_sum]
  exact Finset.sum_congr rfl fun p _ => hQ p

variable {X Z : Point F m → F → R}

omit [Algebra (ZMod 2) F] in
theorem sandComb_posSemidef (hX : ∀ x, IsPVMIn (X x)) (hZ : ∀ z, IsPVMIn (Z z))
    (u : Point F (4 * m)) (c : F) : 0 ≤ sandComb X Z u c :=
  ptComb_posSemidef (fun p => by
    rw [(hX _).sand_eq_gram (hZ _)]
    exact star_mul_self_nonneg _) _ _ _

omit [Algebra (ZMod 2) F] in
theorem sandComb_le_one (hX : ∀ x, IsPVMIn (X x)) (hZ : ∀ z, IsPVMIn (Z z))
    (u : Point F (4 * m)) (c : F) : sandComb X Z u c ≤ 1 :=
  ptComb_le_one (fun p => by
    rw [(hX _).sand_eq_gram (hZ _)]
    exact star_mul_self_nonneg _) ((hX _).sum_sand (hZ _)) _ _ _

omit [PartialOrder R] [StarOrderedRing R] [Algebra (ZMod 2) F] in
theorem sandComb_conjTranspose (hX : ∀ x, IsPVMIn (X x)) (hZ : ∀ z, IsPVMIn (Z z))
    (u : Point F (4 * m)) (c : F) : star (sandComb X Z u c) = sandComb X Z u c :=
  ptComb_conjTranspose (fun p => (hX _).star_sand (hZ _) p) _ _ _

omit [StarRing R] [PartialOrder R] [StarOrderedRing R] [Algebra (ZMod 2) F] in
theorem sandComb_sub_ordComb (ord : (F → R) → (F → R) → F × F → R) (u : Point F (4 * m))
    (c : F) :
    sandComb X Z u c - ordComb ord X Z u c
      = ptComb (fun p => sand (X (xBlk u)) (Z (zBlk u)) p - ord (X (xBlk u)) (Z (zBlk u)) p)
          (alph u) (bet u) c := by
  simp only [sandComb, ordComb, ptComb, Finset.sum_sub_distrib]

end Ring

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {X Z : Point F m → F → ℬ}

/-- **`lem:qld-global-products`, for an abstract ordered product.** Let `G` be a projective
measurement of the first player with outcomes polynomials on `F^{4m}`, consistent with error `δ`,
on average over a uniform padded point, with the sandwich combination of two projective families
`X x`, `Z z` of the second player whose average commutator weight is `κ`; and let `ord` be an
ordered product of the two families summing to one and deviating from the sandwich by a
contraction of the commutator. Then `∑_g E_u ‖(G_g ⊗ (1 - ∑_{αa + βb = g(u)} ord(a, b))) Φ‖² ≤
2δ + 2κ`. -/
theorem sum_snorm_sq_ordComb_le {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1)
    (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) 𝒜) (hG : IsPVMIn G.op)
    (hX : ∀ x, IsPVMIn (X x)) (hZ : ∀ z, IsPVMIn (Z z))
    {ord : (F → ℬ) → (F → ℬ) → F × F → ℬ}
    (hord1 : ∀ x z, ∑ p : F × F, ord (X x) (Z z) p = 1)
    (hordle : ∀ x z p, K.swap.stateNorm (sand (X x) (Z z) p - ord (X x) (Z z) p)
      ≤ K.swap.stateNorm (comm (X x) (Z z) p))
    {δ κ : ℝ}
    (hcons : 1 - δ ≤ ∑ u, uniform (Point F (4 * m)) u
      * ∑ g, K.bornProb (G.op g) (sandComb X Z u (g.eval u)))
    (hcomm : ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
      * ∑ p : F × F, K.swap.stateSqNorm (comm (X x) (Z z) p) ≤ κ) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm (K.πA (G.op g)
        * K.πB (1 - ordComb ord X Z u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * κ := by
  have hμ0 : ∀ u, 0 ≤ uniform (Point F (4 * m)) u := fun u => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hμ1 : ∑ u, uniform (Point F (4 * m)) u = 1 := sum_uniform_eq_one _
  -- the pointwise split along `1 - B = (1 - P) + (P - B)`
  have hsplit : ∀ u g, K.snorm (K.πA (G.op g) * K.πB (1 - ordComb ord X Z u (g.eval u))) ^ 2
      ≤ 2 * K.snorm (K.πA (G.op g) * K.πB (1 - sandComb X Z u (g.eval u))) ^ 2
        + 2 * K.snorm (K.πA (G.op g)
          * K.πB (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2 := by
    intro u g
    have h : (1 : ℬ) - ordComb ord X Z u (g.eval u)
        = (1 - sandComb X Z u (g.eval u))
          + (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u)) := by abel
    rw [h, map_add, mul_add]
    exact snorm_sq_add_le K.toStateModel _ _
  -- the first term: the consistency itself
  have hfirst : ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
      (K.πA (G.op g) * K.πB (1 - sandComb X Z u (g.eval u))) ^ 2 ≤ δ := by
    have hpt : ∀ u g, K.snorm (K.πA (G.op g) * K.πB (1 - sandComb X Z u (g.eval u))) ^ 2
        ≤ K.bornProb (G.op g) 1 - K.bornProb (G.op g) (sandComb X Z u (g.eval u)) := by
      intro u g
      rw [K.snorm_sq_πA_mul_πB (hG.isStarProjection g), ← K.bornProb_sub_right]
      have hsa : star ((1 : ℬ) - sandComb X Z u (g.eval u)) = 1 - sandComb X Z u (g.eval u) := by
        rw [star_sub, star_one, sandComb_conjTranspose hX hZ]
      rw [hsa]
      exact mul_self_le_self_of_le_one K (hG.nonneg g)
        (sub_nonneg.mpr (sandComb_le_one hX hZ u _))
        (sub_le_self _ (sandComb_posSemidef hX hZ u _))
    calc ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
          (K.πA (G.op g) * K.πB (1 - sandComb X Z u (g.eval u))) ^ 2
        ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, (K.bornProb (G.op g) 1
            - K.bornProb (G.op g) (sandComb X Z u (g.eval u))) :=
          Finset.sum_le_sum fun u _ =>
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => hpt u g) (hμ0 u)
      _ = 1 - ∑ u, uniform (Point F (4 * m)) u
            * ∑ g, K.bornProb (G.op g) (sandComb X Z u (g.eval u)) := by
          simp only [Finset.sum_sub_distrib, sum_bornProb_M_one hK G, mul_sub, mul_one, hμ1]
      _ ≤ δ := by linarith
  -- the second term: the commutators, through Parseval
  have hsecond : ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
      (K.πA (G.op g) * K.πB (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2
      ≤ κ := by
    have hu : ∀ u, ∑ g, K.snorm (K.πA (G.op g)
          * K.πB (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2
        ≤ ∑ c, K.swap.stateSqNorm (ptComb (fun p => sand (X (xBlk u)) (Z (zBlk u)) p
            - ord (X (xBlk u)) (Z (zBlk u)) p) (alph u) (bet u) c) := by
      intro u
      have h := sum_snorm_sq_aOp_mul_bOp_le K hG (fun g => g.eval u)
        (fun c => sandComb X Z u c - ordComb ord X Z u c)
      simpa only [sandComb_sub_ordComb] using h
    calc ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
          (K.πA (G.op g) * K.πB (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2
        ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ c, K.swap.stateSqNorm (ptComb
            (fun p => sand (X (xBlk u)) (Z (zBlk u)) p - ord (X (xBlk u)) (Z (zBlk u)) p)
            (alph u) (bet u) c) :=
          Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hu u) (hμ0 u)
      _ = ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
            * ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
              * ∑ c, K.swap.stateSqNorm (ptComb (fun p => sand (X x) (Z z) p - ord (X x) (Z z) p)
                  ab.1 ab.2 c) :=
          sum_uniform_pad4 fun x z a b => ∑ c, K.swap.stateSqNorm (ptComb
            (fun p => sand (X x) (Z z) p - ord (X x) (Z z) p) a b c)
      _ ≤ ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
            * ∑ p : F × F, K.swap.stateSqNorm (comm (X x) (Z z) p) := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (inv_nonneg.mpr (Nat.cast_nonneg _)))
          exact sum_avg_fibre_sand_sub_ord_le (hX x) (hZ z) K (hord1 x z) (hordle x z)
      _ ≤ κ := hcomm
  have hsum : ∑ u, uniform (Point F (4 * m)) u * ∑ g, (2 * K.snorm
        (K.πA (G.op g) * K.πB (1 - sandComb X Z u (g.eval u))) ^ 2
        + 2 * K.snorm (K.πA (G.op g)
          * K.πB (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2)
      = 2 * (∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
          (K.πA (G.op g) * K.πB (1 - sandComb X Z u (g.eval u))) ^ 2)
        + 2 * (∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
          (K.πA (G.op g) * K.πB (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2) := by
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1 <;> exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun g _ => by ring
  calc ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm (K.πA (G.op g)
          * K.πB (1 - ordComb ord X Z u (g.eval u))) ^ 2
      ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, (2 * K.snorm
          (K.πA (G.op g) * K.πB (1 - sandComb X Z u (g.eval u))) ^ 2
          + 2 * K.snorm (K.πA (G.op g)
            * K.πB (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2) :=
        Finset.sum_le_sum fun u _ =>
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => hsplit u g) (hμ0 u)
    _ = _ := hsum
    _ ≤ 2 * δ + 2 * κ := by linarith [hfirst, hsecond]

/-- `lem:qld-global-products` for the order `Z_b X_a`. -/
theorem sum_snorm_sq_ordZX_le {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1)
    (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) 𝒜) (hG : IsPVMIn G.op)
    (hX : ∀ x, IsPVMIn (X x)) (hZ : ∀ z, IsPVMIn (Z z)) {δ κ : ℝ}
    (hcons : 1 - δ ≤ ∑ u, uniform (Point F (4 * m)) u
      * ∑ g, K.bornProb (G.op g) (sandComb X Z u (g.eval u)))
    (hcomm : ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
      * ∑ p : F × F, K.swap.stateSqNorm (comm (X x) (Z z) p) ≤ κ) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm (K.πA (G.op g)
        * K.πB (1 - ordComb ordZX X Z u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * κ :=
  sum_snorm_sq_ordComb_le hK G hG hX hZ (fun x z => sum_ordZX (hX x) (hZ z))
    (fun _ z p => norm_stateVecB_sand_sub_ordZX_le (hZ z) K p) hcons hcomm

/-- `lem:qld-global-products` for the order `X_a Z_b`. -/
theorem sum_snorm_sq_ordXZ_le {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1)
    (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) 𝒜) (hG : IsPVMIn G.op)
    (hX : ∀ x, IsPVMIn (X x)) (hZ : ∀ z, IsPVMIn (Z z)) {δ κ : ℝ}
    (hcons : 1 - δ ≤ ∑ u, uniform (Point F (4 * m)) u
      * ∑ g, K.bornProb (G.op g) (sandComb X Z u (g.eval u)))
    (hcomm : ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
      * ∑ p : F × F, K.swap.stateSqNorm (comm (X x) (Z z) p) ≤ κ) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm (K.πA (G.op g)
        * K.πB (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * κ :=
  sum_snorm_sq_ordComb_le hK G hG hX hZ (fun x z => sum_ordXZ (hX x) (hZ z))
    (fun _ z p => norm_stateVecB_sand_sub_ordXZ_le (hZ z) K p) hcons hcomm

end Products

end MIPRE.QLD

end

end
