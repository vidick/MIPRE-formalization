/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Dummy
import MIPRE.Foundations.Parseval

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
over `F_q` (`sum_avg_norm_fibre_sq`) turns the average over `(α, β)` of the fibre sums into
`(1 - 1/q) ∑_{a,b} ‖(1 ⊗ (sand - ord)(a, b)) Φ‖²` with no loss of a factor `q`, and each deviation
is a contraction of a commutator: `Z X Z - Z X = Z [X, Z]` and `Z X Z - X Z = -(1 - Z) [X, Z]`.

Everything here is stated for abstract projective families `X x`, `Z z` on Bob's register, with
the consistency and the commutator weight as hypotheses; `lem:qld-global-pvm` and
`lem:qld-combined-points` supply them for the padded state.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

section Generic

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- `Q² ≤ Q` for `0 ≤ Q ≤ 1`. -/
theorem mul_self_le_self_of_le_one {Q : Matrix N N ℂ} (h0 : (0 : Matrix N N ℂ) ≤ Q)
    (h1 : Q ≤ 1) : Q * Q ≤ Q := by
  have hc : Commute Q (1 - Q) := by
    show Q * (1 - Q) = (1 - Q) * Q
    noncomm_ring
  have h := hc.mul_nonneg h0 (sub_nonneg.mpr h1)
  have heq : Q * (1 - Q) = Q - Q * Q := by noncomm_ring
  rw [heq] at h
  exact sub_nonneg.mp h

/-- The complement of a projector is a contraction. -/
theorem one_sub_proj_conjTranspose_mul_self_le_one {P : Matrix N N ℂ} (hsa : Pᴴ = P)
    (hidem : P * P = P) : ((1 : Matrix N N ℂ) - P)ᴴ * (1 - P) ≤ 1 := by
  have hsa' : ((1 : Matrix N N ℂ) - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hsa]
  have hidem' : ((1 : Matrix N N ℂ) - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hidem]
    abel
  rw [hsa', hidem']
  exact proj_le_one hsa' hidem'

omit [DecidableEq N] in
theorem snorm_sq_add_le (v : N → ℂ) (M M' : Matrix N N ℂ) :
    snorm v (M + M') ^ 2 ≤ 2 * snorm v M ^ 2 + 2 * snorm v M' ^ 2 := by
  have h := snorm_add_le v M M'
  have h0 := snorm_nonneg v (M + M')
  nlinarith [sq_nonneg (snorm v M - snorm v M')]

end Generic

section Born

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- The Born probability is monotone in Alice's operator when Bob's is positive. -/
theorem bornProb_mono_left (ψ : dA × dB → ℂ) {X X' : Matrix dA dA ℂ} (h : X ≤ X')
    {Y : Matrix dB dB ℂ} (hY : Y.PosSemidef) : bornProb ψ X Y ≤ bornProb ψ X' Y := by
  rw [← bornProb_swapVec ψ X Y, ← bornProb_swapVec ψ X' Y]
  exact bornProb_mono_right _ hY h

/-- The squared norm of `(S ⊗ D) ψ` for a projector `S`, as a Born probability. -/
theorem snorm_sq_aOp_mul_bOp (ψ : dA × dB → ℂ) {S : Matrix dA dA ℂ} (hsa : Sᴴ = S)
    (hidem : S * S = S) (D : Matrix dB dB ℂ) :
    snorm ψ ((aOp S : Matrix (dA × dB) _ ℂ) * bOp D) ^ 2 = bornProb ψ S (Dᴴ * D) := by
  rw [snorm_sq_eq_qform, aOp_bOp_conjTranspose, aOp_bOp_mul_aOp_bOp, hsa, hidem,
    ← bornProb_eq_qform]

/-- `⟨ψ| 1 ⊗ Dᴴ D |ψ⟩ = ‖(1 ⊗ D) ψ‖²`. -/
theorem bornProb_one_eq_normSq_stateVecB (ψ : dA × dB → ℂ) (D : Matrix dB dB ℂ) :
    bornProb ψ (1 : Matrix dA dA ℂ) (Dᴴ * D) = ‖stateVecB ψ D‖ ^ 2 := by
  rw [normSq_stateVecB_eq_qform, bornProb_eq_qform, aOp_one, Matrix.one_mul]

/-- The deviation of a projective outcome family from a Bob-side operator family, grouped by a
value map: the Alice projector `∑_{f g = c} G_g ≤ 1` is dropped. -/
theorem sum_snorm_sq_aOp_mul_bOp_le {Λ C : Type*} [Fintype Λ] [Fintype C] [DecidableEq C]
    (ψ : dA × dB → ℂ) {G : Λ → Matrix dA dA ℂ} (hG : IsPVM G) (f : Λ → C)
    (D : C → Matrix dB dB ℂ) :
    ∑ g, snorm ψ ((aOp (G g) : Matrix (dA × dB) _ ℂ) * bOp (D (f g))) ^ 2
      ≤ ∑ c, ‖stateVecB ψ (D c)‖ ^ 2 := by
  classical
  have hterm : ∀ g, snorm ψ ((aOp (G g) : Matrix (dA × dB) _ ℂ) * bOp (D (f g))) ^ 2
      = bornProb ψ (G g) ((D (f g))ᴴ * D (f g)) := fun g =>
    snorm_sq_aOp_mul_bOp ψ (hG.isSelfAdjoint g) (hG.idem g) _
  simp_rw [hterm]
  rw [← Finset.sum_fiberwise univ f]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Finset.sum_congr rfl fun g hg => by rw [(mem_filter.mp hg).2], ← bornProb_sum_left,
    ← bornProb_one_eq_normSq_stateVecB]
  refine bornProb_mono_left ψ ?_ (Matrix.posSemidef_conjTranspose_mul_self _)
  rw [← hG.sum_eq_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun g _ _ => Matrix.nonneg_iff_posSemidef.mpr (hG.posSemidef g)

end Born

section Ext

variable {dA dB Anc Bnc : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]

/-- Alice's squared state norm of an operator extended by the identity, on the twice-extended
state, is its squared state norm on the state. -/
theorem stateSqNorm_extVec2_aOp (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc) (M : Matrix dA dA ℂ) :
    stateSqNorm (extVec2 ψ a₀ b₀) (aOp M : Matrix (dA × Anc) _ ℂ) = stateSqNorm ψ M := by
  rw [stateSqNorm_eq_qform (dB := dB × Bnc), aOp_conjTranspose, ← aOp_mul, qform_aOp_extVec2,
    compress_aOp, ← stateSqNorm_eq_qform]

end Ext

/-! ## Parseval for a Bob-side family -/

section Parseval

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **Parseval over `F_q` for the fibre sums of a Bob-side family summing to zero**: the average
over the combining coefficients of the squared norms of the fibre sums is `(1 - 1/q)` times the
sum of the squared norms of the members. -/
theorem sum_avg_normSq_stateVecB_fibre_eq (ψ : dA × dB → ℂ) {E : F × F → Matrix dB dB ℂ}
    (hE : ∑ p, E p = 0) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ c : F, ‖stateVecB ψ (QLD.ptComb E ab.1 ab.2 c)‖ ^ 2
      = (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, ‖stateVecB ψ (E p)‖ ^ 2 := by
  have hU : ∑ p : F × F, (bOp (E p) : Matrix (dA × dB) _ ℂ) *ᵥ ψ = 0 := by
    rw [← Matrix.sum_mulVec, ← bOp_sum, hE, bOp_zero, Matrix.zero_mulVec]
  have h := sum_avg_norm_fibre_sq (F := F) (fun p => (bOp (E p) : Matrix (dA × dB) _ ℂ) *ᵥ ψ) hU
  have hfib : ∀ (ab : F × F) (c : F), stateVecB ψ (QLD.ptComb E ab.1 ab.2 c)
      = evec (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = c,
          (bOp (E p) : Matrix (dA × dB) _ ℂ) *ᵥ ψ) := by
    intro ab c
    rw [← Matrix.sum_mulVec, ← bOp_sum]
    rfl
  simp_rw [hfib]
  rw [h]
  rfl

end Parseval

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## The two ordered products and the commutator -/

section Ord

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {RB : Type*} [Fintype RB]
  [DecidableEq RB]

/-- Bob's ordered product, `X` then `Z` (applied right to left: `Z_b X_a`). -/
def ordZX (X Z : F → Matrix RB RB ℂ) (p : F × F) : Matrix RB RB ℂ := Z p.2 * X p.1

/-- Bob's ordered product, `Z` then `X`: `X_a Z_b`. -/
def ordXZ (X Z : F → Matrix RB RB ℂ) (p : F × F) : Matrix RB RB ℂ := X p.1 * Z p.2

/-- The commutator `X_a Z_b - Z_b X_a`. -/
def comm (X Z : F → Matrix RB RB ℂ) (p : F × F) : Matrix RB RB ℂ := X p.1 * Z p.2 - Z p.2 * X p.1

variable {X Z : F → Matrix RB RB ℂ}

omit [Field F] [DecidableEq F] in
theorem sum_ordZX (hX : IsPVM X) (hZ : IsPVM Z) : ∑ p : F × F, ordZX X Z p = 1 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [ordZX, ← Matrix.mul_sum, hX.sum_eq_one, Matrix.mul_one]
  exact hZ.sum_eq_one

omit [Field F] [DecidableEq F] in
theorem sum_ordXZ (hX : IsPVM X) (hZ : IsPVM Z) : ∑ p : F × F, ordXZ X Z p = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [ordXZ, ← Matrix.mul_sum, hZ.sum_eq_one, Matrix.mul_one]
  exact hX.sum_eq_one

omit [Field F] [DecidableEq F] in
/-- `Z X Z - Z X = Z [X, Z]`. -/
theorem sand_sub_ordZX (hZ : IsPVM Z) (p : F × F) :
    sand X Z p - ordZX X Z p = Z p.2 * comm X Z p := by
  simp only [sand, ordZX, comm, Matrix.mul_sub, ← Matrix.mul_assoc, hZ.idem]

omit [Field F] [DecidableEq F] in
/-- `Z X Z - X Z = -(1 - Z) [X, Z]`. -/
theorem sand_sub_ordXZ (hZ : IsPVM Z) (p : F × F) :
    sand X Z p - ordXZ X Z p = -(((1 : Matrix RB RB ℂ) - Z p.2) * comm X Z p) := by
  have h : ((1 : Matrix RB RB ℂ) - Z p.2) * comm X Z p
      = X p.1 * Z p.2 - Z p.2 * X p.1 * Z p.2 := by
    simp only [comm, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, ← Matrix.mul_assoc, hZ.idem]
    abel
  rw [h, sand, ordXZ]
  abel

variable {dA : Type*} [Fintype dA] [DecidableEq dA]

omit [Field F] in
theorem norm_stateVecB_sand_sub_ordZX_le (hZ : IsPVM Z) (ψ : dA × RB → ℂ) (p : F × F) :
    ‖stateVecB ψ (sand X Z p - ordZX X Z p)‖ ≤ ‖stateVecB ψ (comm X Z p)‖ := by
  rw [sand_sub_ordZX hZ]
  exact norm_stateVecB_mul_le ψ (hZ.conjTranspose_mul_self_le_one _) _

omit [Field F] [DecidableEq F] in
theorem norm_stateVecB_sand_sub_ordXZ_le (hZ : IsPVM Z) (ψ : dA × RB → ℂ) (p : F × F) :
    ‖stateVecB ψ (sand X Z p - ordXZ X Z p)‖ ≤ ‖stateVecB ψ (comm X Z p)‖ := by
  rw [sand_sub_ordXZ hZ, ← neg_one_smul ℂ, stateVecB_smul, norm_smul, norm_neg, norm_one,
    one_mul]
  exact norm_stateVecB_mul_le ψ
    (one_sub_proj_conjTranspose_mul_self_le_one (hZ.isSelfAdjoint _) (hZ.idem _)) _

end Ord

/-! ## The averaged fibre bound -/

section Fibre

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {dA RB : Type*} [Fintype dA] [DecidableEq dA] [Fintype RB] [DecidableEq RB]
  {X Z : F → Matrix RB RB ℂ}

/-- **The fibre sums of `sand - ord` are controlled by the commutators**, on average over the
combining coefficients and without a factor `q`, for either order. -/
theorem sum_avg_fibre_sand_sub_ord_le (hX : IsPVM X) (hZ : IsPVM Z) (ψ : dA × RB → ℂ)
    {ord : (F → Matrix RB RB ℂ) → (F → Matrix RB RB ℂ) → F × F → Matrix RB RB ℂ}
    (hord1 : ∑ p : F × F, ord X Z p = 1)
    (hordle : ∀ p, ‖stateVecB ψ (sand X Z p - ord X Z p)‖ ≤ ‖stateVecB ψ (comm X Z p)‖) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ c : F, ‖stateVecB ψ (ptComb (fun p => sand X Z p - ord X Z p) ab.1 ab.2 c)‖ ^ 2
      ≤ ∑ p : F × F, ‖stateVecB ψ (comm X Z p)‖ ^ 2 := by
  rw [sum_avg_normSq_stateVecB_fibre_eq ψ (E := fun p => sand X Z p - ord X Z p)
    (by rw [Finset.sum_sub_distrib, sum_sand hX hZ, hord1, sub_self])]
  have hq : (0 : ℝ) ≤ 1 - (Fintype.card F : ℝ)⁻¹ := by
    rw [sub_nonneg]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos)
  calc (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, ‖stateVecB ψ (sand X Z p - ord X Z p)‖ ^ 2
      ≤ 1 * ∑ p : F × F, ‖stateVecB ψ (comm X Z p)‖ ^ 2 := by
        refine mul_le_mul
          (by linarith [inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ _)])
          (Finset.sum_le_sum fun p _ => pow_le_pow_left₀ (norm_nonneg _) (hordle p) 2)
          (Finset.sum_nonneg fun p _ => sq_nonneg _) (by norm_num)
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

/-! ## The verifier's content, read through its two points -/

section ContentBlocks

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ} [NeZero m]

/-- The uniform content, read through `(uX, uZ)`, is a pair of independent uniform points. -/
theorem sum_content_blocks (g : Point F m → Point F m → ℝ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * g c.uX c.uZ
      = ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z) * g x z := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard : (Fintype.card (Content F m) : ℝ)
      = (Fintype.card F : ℝ) ^ m * (Fintype.card F : ℝ) ^ m * Fintype.card F
        * (Fintype.card F : ℝ) ^ m * (Fintype.card F * Fintype.card F) := by
    rw [Fintype.card_congr contentEquiv]
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  have hsplit : ∑ c : Content F m, g c.uX c.uZ
      = (Fintype.card F : ℝ) * (Fintype.card F : ℝ) ^ m * (Fintype.card F * Fintype.card F)
        * ∑ x, ∑ z, g x z := by
    rw [sum_content_split (fun c => g c.uX c.uZ)]
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  simp only [uniform, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ← Finset.mul_sum]
  rw [hsplit, hcard]
  field_simp

end ContentBlocks

/-! ## The lemma -/

section Products

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {RA RB : Type*} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]

/-- The sandwich combination at a padded point, `P_u(c) = ∑_{αa + βb = c} Z_b X_a Z_b`, for
abstract point measurements `X x`, `Z z` on Bob's register. -/
def sandComb (X Z : Point F m → F → Matrix RB RB ℂ) (u : Point F (4 * m)) (c : F) :
    Matrix RB RB ℂ :=
  ptComb (sand (X (xBlk u)) (Z (zBlk u))) (alph u) (bet u) c

/-- An ordered-product combination at a padded point, `∑_{αa + βb = c} ord(a, b)`. -/
def ordComb (ord : (F → Matrix RB RB ℂ) → (F → Matrix RB RB ℂ) → F × F → Matrix RB RB ℂ)
    (X Z : Point F m → F → Matrix RB RB ℂ) (u : Point F (4 * m)) (c : F) : Matrix RB RB ℂ :=
  ptComb (ord (X (xBlk u)) (Z (zBlk u))) (alph u) (bet u) c

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem ptComb_posSemidef {Q : F × F → Matrix RB RB ℂ} (hQ : ∀ p, (Q p).PosSemidef)
    (a b c : F) : (ptComb Q a b c).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun p _ => Matrix.nonneg_iff_posSemidef.mpr (hQ p))

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem ptComb_le_one {Q : F × F → Matrix RB RB ℂ} (hQ : ∀ p, (Q p).PosSemidef)
    (hsum : ∑ p, Q p = 1) (a b c : F) : ptComb Q a b c ≤ 1 := by
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun p _ _ => Matrix.nonneg_iff_posSemidef.mpr (hQ p)

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem ptComb_conjTranspose {Q : F × F → Matrix RB RB ℂ} (hQ : ∀ p, (Q p)ᴴ = Q p) (a b c : F) :
    (ptComb Q a b c)ᴴ = ptComb Q a b c := by
  rw [ptComb, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun p _ => hQ p

variable {X Z : Point F m → F → Matrix RB RB ℂ}

omit [Algebra (ZMod 2) F] in
theorem sandComb_posSemidef (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z))
    (u : Point F (4 * m)) (c : F) : (sandComb X Z u c).PosSemidef :=
  ptComb_posSemidef (fun p => sand_posSemidef (hX _) (hZ _) p) _ _ _

omit [Algebra (ZMod 2) F] in
theorem sandComb_le_one (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z)) (u : Point F (4 * m))
    (c : F) : sandComb X Z u c ≤ 1 :=
  ptComb_le_one (fun p => sand_posSemidef (hX _) (hZ _) p) (sum_sand (hX _) (hZ _)) _ _ _

omit [Algebra (ZMod 2) F] in
theorem sandComb_conjTranspose (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z))
    (u : Point F (4 * m)) (c : F) : (sandComb X Z u c)ᴴ = sandComb X Z u c :=
  ptComb_conjTranspose (fun p => sand_conjTranspose (hX _) (hZ _) p) _ _ _

omit [Algebra (ZMod 2) F] in
theorem sandComb_sub_ordComb (ord : (F → Matrix RB RB ℂ) → (F → Matrix RB RB ℂ) → F × F →
    Matrix RB RB ℂ) (u : Point F (4 * m)) (c : F) :
    sandComb X Z u c - ordComb ord X Z u c
      = ptComb (fun p => sand (X (xBlk u)) (Z (zBlk u)) p - ord (X (xBlk u)) (Z (zBlk u)) p)
          (alph u) (bet u) c := by
  simp only [sandComb, ordComb, ptComb, Finset.sum_sub_distrib]

/-- **`lem:qld-global-products`, for an abstract ordered product.** Let `G` be a projective
measurement with outcomes polynomials on `F^{4m}`, consistent with error `δ`, on average over a
uniform padded point, with the sandwich combination of two projective families `X x`, `Z z` on
Bob's register whose average commutator weight is `κ`; and let `ord` be an ordered product of the
two families summing to one and deviating from the sandwich by a contraction of the commutator.
Then `∑_g E_u ‖(G_g ⊗ (1 - ∑_{αa + βb = g(u)} ord(a, b))) Φ‖² ≤ 2δ + 2κ`. -/
theorem sum_snorm_sq_ordComb_le {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z))
    {ord : (F → Matrix RB RB ℂ) → (F → Matrix RB RB ℂ) → F × F → Matrix RB RB ℂ}
    (hord1 : ∀ x z, ∑ p : F × F, ord (X x) (Z z) p = 1)
    (hordle : ∀ x z p, ‖stateVecB Φ (sand (X x) (Z z) p - ord (X x) (Z z) p)‖
      ≤ ‖stateVecB Φ (comm (X x) (Z z) p)‖)
    {δ κ : ℝ}
    (hcons : 1 - δ ≤ ∑ u, uniform (Point F (4 * m)) u
      * ∑ g, bornProb Φ (G.M () g) (sandComb X Z u (g.eval u)))
    (hcomm : ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
      * ∑ p : F × F, ‖stateVecB Φ (comm (X x) (Z z) p)‖ ^ 2 ≤ κ) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
        * bOp (1 - ordComb ord X Z u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * κ := by
  have hμ0 : ∀ u, 0 ≤ uniform (Point F (4 * m)) u := fun u => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hμ1 : ∑ u, uniform (Point F (4 * m)) u = 1 := sum_uniform_eq_one _
  have hGpvm : IsPVM (G.M ()) :=
    ⟨fun g => G.selfAdjoint () g, fun g => G.projective () g, G.normalized ()⟩
  -- the pointwise split along `1 - B = (1 - P) + (P - B)`
  have hsplit : ∀ u g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
        * bOp (1 - ordComb ord X Z u (g.eval u))) ^ 2
      ≤ 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (1 - sandComb X Z u (g.eval u))) ^ 2
        + 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2 := by
    intro u g
    have h : (1 : Matrix RB RB ℂ) - ordComb ord X Z u (g.eval u)
        = (1 - sandComb X Z u (g.eval u))
          + (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u)) := by abel
    rw [h, bOp_add, Matrix.mul_add]
    exact snorm_sq_add_le _ _ _
  -- the first term: the consistency itself
  have hfirst : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - sandComb X Z u (g.eval u))) ^ 2 ≤ δ := by
    have hpt : ∀ u g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (1 - sandComb X Z u (g.eval u))) ^ 2
        ≤ bornProb Φ (G.M () g) 1 - bornProb Φ (G.M () g) (sandComb X Z u (g.eval u)) := by
      intro u g
      rw [snorm_sq_aOp_mul_bOp Φ (G.selfAdjoint () g) (G.projective () g), ← bornProb_sub_right]
      have hsa : ((1 : Matrix RB RB ℂ) - sandComb X Z u (g.eval u))ᴴ
          = 1 - sandComb X Z u (g.eval u) := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sandComb_conjTranspose hX hZ]
      rw [hsa]
      refine bornProb_mono_right Φ (G.posSemidef_M () g) (mul_self_le_self_of_le_one ?_ ?_)
      · exact sub_nonneg.mpr (sandComb_le_one hX hZ u _)
      · exact sub_le_self _ (Matrix.nonneg_iff_posSemidef.mpr (sandComb_posSemidef hX hZ u _))
    calc ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
          ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - sandComb X Z u (g.eval u))) ^ 2
        ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, (bornProb Φ (G.M () g) 1
            - bornProb Φ (G.M () g) (sandComb X Z u (g.eval u))) :=
          Finset.sum_le_sum fun u _ =>
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => hpt u g) (hμ0 u)
      _ = 1 - ∑ u, uniform (Point F (4 * m)) u
            * ∑ g, bornProb Φ (G.M () g) (sandComb X Z u (g.eval u)) := by
          simp only [Finset.sum_sub_distrib, sum_bornProb_M_one hΦ G, mul_sub, mul_one, hμ1]
      _ ≤ δ := by linarith
  -- the second term: the commutators, through Parseval
  have hsecond : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
        * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2 ≤ κ := by
    have hu : ∀ u, ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2
        ≤ ∑ c, ‖stateVecB Φ (ptComb (fun p => sand (X (xBlk u)) (Z (zBlk u)) p
            - ord (X (xBlk u)) (Z (zBlk u)) p) (alph u) (bet u) c)‖ ^ 2 := by
      intro u
      have h := sum_snorm_sq_aOp_mul_bOp_le Φ hGpvm (fun g => g.eval u)
        (fun c => sandComb X Z u c - ordComb ord X Z u c)
      simpa only [sandComb_sub_ordComb] using h
    calc ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
          ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2
        ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ c, ‖stateVecB Φ (ptComb
            (fun p => sand (X (xBlk u)) (Z (zBlk u)) p - ord (X (xBlk u)) (Z (zBlk u)) p)
            (alph u) (bet u) c)‖ ^ 2 :=
          Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hu u) (hμ0 u)
      _ = ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
            * ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
              * ∑ c, ‖stateVecB Φ (ptComb (fun p => sand (X x) (Z z) p - ord (X x) (Z z) p)
                  ab.1 ab.2 c)‖ ^ 2 :=
          sum_uniform_pad4 fun x z a b => ∑ c, ‖stateVecB Φ (ptComb
            (fun p => sand (X x) (Z z) p - ord (X x) (Z z) p) a b c)‖ ^ 2
      _ ≤ ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
            * ∑ p : F × F, ‖stateVecB Φ (comm (X x) (Z z) p)‖ ^ 2 := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (inv_nonneg.mpr (Nat.cast_nonneg _)))
          exact sum_avg_fibre_sand_sub_ord_le (hX x) (hZ z) Φ (hord1 x z) (hordle x z)
      _ ≤ κ := hcomm
  have hsum : ∑ u, uniform (Point F (4 * m)) u * ∑ g, (2 * snorm Φ
        ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - sandComb X Z u (g.eval u))) ^ 2
        + 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2)
      = 2 * (∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
          ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - sandComb X Z u (g.eval u))) ^ 2)
        + 2 * (∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
          ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2) := by
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1 <;> exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun g _ => by ring
  calc ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (1 - ordComb ord X Z u (g.eval u))) ^ 2
      ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, (2 * snorm Φ
          ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - sandComb X Z u (g.eval u))) ^ 2
          + 2 * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
            * bOp (sandComb X Z u (g.eval u) - ordComb ord X Z u (g.eval u))) ^ 2) :=
        Finset.sum_le_sum fun u _ =>
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => hsplit u g) (hμ0 u)
    _ = _ := hsum
    _ ≤ 2 * δ + 2 * κ := by linarith [hfirst, hsecond]

/-- `lem:qld-global-products` for the order `Z_b X_a`. -/
theorem sum_snorm_sq_ordZX_le {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z)) {δ κ : ℝ}
    (hcons : 1 - δ ≤ ∑ u, uniform (Point F (4 * m)) u
      * ∑ g, bornProb Φ (G.M () g) (sandComb X Z u (g.eval u)))
    (hcomm : ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
      * ∑ p : F × F, ‖stateVecB Φ (comm (X x) (Z z) p)‖ ^ 2 ≤ κ) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
        * bOp (1 - ordComb ordZX X Z u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * κ :=
  sum_snorm_sq_ordComb_le hΦ G hX hZ (fun x z => sum_ordZX (hX x) (hZ z))
    (fun _ z p => norm_stateVecB_sand_sub_ordZX_le (hZ z) Φ p) hcons hcomm

/-- `lem:qld-global-products` for the order `X_a Z_b`. -/
theorem sum_snorm_sq_ordXZ_le {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z)) {δ κ : ℝ}
    (hcons : 1 - δ ≤ ∑ u, uniform (Point F (4 * m)) u
      * ∑ g, bornProb Φ (G.M () g) (sandComb X Z u (g.eval u)))
    (hcomm : ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z)
      * ∑ p : F × F, ‖stateVecB Φ (comm (X x) (Z z) p)‖ ^ 2 ≤ κ) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
        * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * κ :=
  sum_snorm_sq_ordComb_le hΦ G hX hZ (fun x z => sum_ordXZ (hX x) (hZ z))
    (fun _ z p => norm_stateVecB_sand_sub_ordXZ_le (hZ z) Φ p) hcons hcomm

end Products

end MIPRE.QLD

end
