/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Separate
public import MIPRE.Background.QLD.Simul
public import MIPRE.Background.LIDT.BlockPoly

@[expose] public section

/-!
# Completing the pair measurement and its evaluated marginals (`lem:qld-global-complete`,
`lem:qld-global-sandwich`)

Stage 4 ends with the interface `SimulPair` (`lem:qld-simultaneous`): a projective measurement
with outcomes pairs `(g_X, g_Z)` of polynomials in `m` variables, whose evaluated marginals are
consistent with the opposite party's expanded point measurements. This file builds it from a
global measurement `G` with outcomes in `LowIndDegPoly F (4m) d` (the polynomials on the padded
point) and the estimates of stage 4b, abstractly: for a projective `G` of the first player and
two projective families `X x`, `Z z` of the second.

## The completion

A good outcome `g = α g_X(x) + β g_Z(z)` (`IsGood`) is relabelled by the pair `(g_X, g_Z)`, read
off its two coefficient polynomials through `LowIndDegPoly.blockPoly` (a polynomial reading only
the `x` block, as a polynomial in `m` variables); every other outcome is sent to the fixed pair
`(0, 0)`. This is a coarse-graining of `G`, so it is a complete projective measurement
(`pairMeas`, `isPVM_pairMeas`): the paper's completion by the orthogonal complement `R`, whose
weight is the weight of the non-good outcomes, bounded by `lem:qld-global-separate`.

## The marginals

From the products estimate `∑_g E_u ‖(G_g ⊗ (1 - B_u(g(u)))) Φ‖² ≤ Δ`, the triangle inequality
and Cauchy--Schwarz give `∑_g E_u ‖(G_g ⊗ B_u(g(u))) Φ‖² ≥ 1 - 2√Δ`
(`one_sub_two_sqrt_le_sum_snorm_sq`). For a good `g` and the order `X_a Z_b`, the fibre analysis
of `lem:qld-global-separate` bounds `E_u ‖(G_g ⊗ B_u(g(u))) Φ‖²` by `2/q · ⟨G_g⟩` plus the
diagonal weight `E_z ⟨G_g ⊗ Z_{g_Z(z)}(z)⟩`, and the non-good outcomes carry weight at most
`δ_G`; hence the `Z` marginal `E_z ∑_g ⟨G_g ⊗ Z_{g_Z(z)}(z)⟩ ≥ 1 - 2√Δ - 2/q - δ_G`
(`marg_Z_ge`), and the order `Z_b X_a` gives the `X` marginal. The consistency form
(`inconsistency_evalMarg_Z_le`, `_X_le`) is the same statement read through `inconsistency`.
The instance of `SimulPair` is in `PaddedLIDT.lean`.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The state is that of a
bipartite model `K` (the model in which the global measurements live), the global measurement is
a POVM `G` in the first player's algebra with `IsPVMIn G.op`, the families `X x`, `Z z` are
projective families of the second player's algebra, a Born probability is `K.bornProb`, and a
squared norm `K.snorm (K.πA (G.op g) * K.πB B) ^ 2`. The completed pair measurement is the
coarse-graining `G.map (pairOf hd)` in the same algebra, so it needs no transport to the shape of
`SimulPair`: the matrix associativity reindexing of the doubly extended registers
(`isPVM_reindex`, `isPVM_reindex_povm`, `reindex_aOp_aOp`, `POVM.aOp_aOp_reindex`) and the
matrix projective-measurement packaging (`ProjectiveMeasurement.isPVM_M`) are gone.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## The pair of a good outcome -/

section Pairs

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

omit [Fintype F] [DecidableEq F] in
theorem isLinAB_of_isGood {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : IsGood g) :
    IsLinAB g := by
  intro e hpat
  by_contra hne
  rcases hg e hne with ⟨h1, h0, _⟩ | ⟨h0, h1, _⟩
  · exact hpat (Or.inl ⟨h1, h0⟩)
  · exact hpat (Or.inr ⟨h0, h1⟩)

omit [Fintype F] [DecidableEq F] in
theorem notMem_xSet_iff {k : Fin (4 * m)} : k ∉ xSet ↔ ∀ j, xIdx m j ≠ k := by
  rw [xSet, Finset.mem_image]
  push Not
  exact ⟨fun h j => h j (mem_univ j), fun h j _ => h j⟩

omit [Fintype F] [DecidableEq F] in
theorem notMem_zSet_iff {k : Fin (4 * m)} : k ∉ zSet ↔ ∀ j, zIdx m j ≠ k := by
  rw [zSet, Finset.mem_image]
  push Not
  exact ⟨fun h j => h j (mem_univ j), fun h j _ => h j⟩

omit [Fintype F] [DecidableEq F] in
/-- The `α` coefficient of a good outcome reads only the `x` block. -/
theorem not_depOutside_gA_of_isGood (hd : 1 ≤ d)
    {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : IsGood g) :
    ¬ (gA hd g).DepOutside xSet := by
  rintro ⟨e, he, k, hk, hek⟩
  rw [gA, LowIndDegPoly.coef] at he
  split_ifs at he with hcond
  · rcases hg _ he with ⟨_, _, hrest⟩ | ⟨h0, _, _⟩
    · by_cases hka : k = aIdx m
      · exact hek (by rw [hka]; exact hcond.1 _ (mem_abSet.mpr (Or.inl rfl)))
      · by_cases hkb : k = bIdx m
        · exact hek (by rw [hkb]; exact hcond.1 _ (mem_abSet.mpr (Or.inr rfl)))
        · have := hrest k hk hka
          rw [patch, ite_eq_right (fun h => (mem_abSet.mp h).elim hka hkb)] at this
          exact hek this
    · rw [patch_abSet_aIdx, patAB_aIdx] at h0
      exact absurd h0 (by simp [oneD])
  · exact he rfl

omit [Fintype F] [DecidableEq F] in
/-- The `β` coefficient of a good outcome reads only the `z` block. -/
theorem not_depOutside_gB_of_isGood (hd : 1 ≤ d)
    {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : IsGood g) :
    ¬ (gB hd g).DepOutside zSet := by
  rintro ⟨e, he, k, hk, hek⟩
  rw [gB, LowIndDegPoly.coef] at he
  split_ifs at he with hcond
  · rcases hg _ he with ⟨_, h1, _⟩ | ⟨_, _, hrest⟩
    · rw [patch_abSet_bIdx, patAB_bIdx] at h1
      exact absurd h1 (by simp [oneD])
    · by_cases hka : k = aIdx m
      · exact hek (by rw [hka]; exact hcond.1 _ (mem_abSet.mpr (Or.inl rfl)))
      · by_cases hkb : k = bIdx m
        · exact hek (by rw [hkb]; exact hcond.1 _ (mem_abSet.mpr (Or.inr rfl)))
        · have := hrest k hk hkb
          rw [patch, ite_eq_right (fun h => (mem_abSet.mp h).elim hka hkb)] at this
          exact hek this
  · exact he rfl

/-- The `X` polynomial of an outcome: its `α` coefficient read on the `x` block. -/
def gX (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) :
    LowIndDegPoly (F := F) (m := m) (d := d) :=
  (gA hd g).blockPoly (xIdx m)

/-- The `Z` polynomial of an outcome: its `β` coefficient read on the `z` block. -/
def gZ (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) :
    LowIndDegPoly (F := F) (m := m) (d := d) :=
  (gB hd g).blockPoly (zIdx m)

omit [Fintype F] [DecidableEq F] in
theorem eval_gX (hd : 1 ≤ d) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : IsGood g)
    (u : Point F (4 * m)) : (gX hd g).eval (xBlk u) = (gA hd g).eval u := by
  refine LowIndDegPoly.eval_blockPoly xIdx_injective (fun e he k hk => ?_) u
  by_contra hne
  exact not_depOutside_gA_of_isGood hd hg ⟨e, he, k, notMem_xSet_iff.mpr hk, hne⟩

omit [Fintype F] [DecidableEq F] in
theorem eval_gZ (hd : 1 ≤ d) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)} (hg : IsGood g)
    (u : Point F (4 * m)) : (gZ hd g).eval (zBlk u) = (gB hd g).eval u := by
  refine LowIndDegPoly.eval_blockPoly zIdx_injective (fun e he k hk => ?_) u
  by_contra hne
  exact not_depOutside_gB_of_isGood hd hg ⟨e, he, k, notMem_zSet_iff.mpr hk, hne⟩

/-- **The relabelling**: a good outcome becomes its pair `(g_X, g_Z)`, every other outcome the
fixed pair `(0, 0)`. -/
def pairOf (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)) : PolyPair F m d :=
  if IsGood g then (gX hd g, gZ hd g) else (0, 0)

omit [Fintype F] in
theorem pairOf_of_isGood (hd : 1 ≤ d) {g : LowIndDegPoly (F := F) (m := 4 * m) (d := d)}
    (hg : IsGood g) : pairOf hd g = (gX hd g, gZ hd g) := ite_eq_left hg

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- **The completed pair measurement**: the global measurement coarse-grained by the relabelling.
The non-good outcomes are absorbed into the pair `(0, 0)`: the paper's complement `R`, added to a
fixed legal outcome. -/
def pairMeas (hd : 1 ≤ d) (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) R) :
    POVMIn (PolyPair F m d) R :=
  G.map (pairOf hd)

theorem pairMeas_mats (hd : 1 ≤ d) (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) R)
    (p : PolyPair F m d) :
    (pairMeas hd G).op p = ∑ g ∈ univ.filter fun g => pairOf hd g = p, G.op g :=
  POVMIn.map_op _ _ _

/-- **The completed pair measurement is projective.** -/
theorem isPVM_pairMeas (hd : 1 ≤ d)
    {G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) R} (hG : IsPVMIn G.op) :
    IsPVMIn (pairMeas hd G).op :=
  POVMIn.isPVMIn_map hG _

/-- The evaluated marginal of the completed measurement is the global measurement coarse-grained
by the evaluated component of the pair. -/
theorem evalMarg_pairMeas (hd : 1 ≤ d)
    (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) R) (W : Bas) (u : Point F m) :
    evalMarg (pairMeas hd G) W u = G.map fun g => (PolyPair.proj W (pairOf hd g)).eval u := by
  rw [evalMarg, pairMeas, POVMIn.map_map]

end Pairs

/-! ## The inconsistency of a coarse-grained global measurement -/

section Coarse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}
  {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ]

omit [Field F] in
/-- **The inconsistency of a coarse-graining of a global measurement**, against a family of
POVMs indexed by the same questions: one minus the average agreement, outcome by outcome of the
original measurement. `inconsistency_evalPOVM_eq` is the case of evaluation at the point. -/
theorem inconsistency_map_eq {Q : Type*} [Fintype Q] (μ : Q → ℝ) (hμ : ∑ q, μ q = 1)
    {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1)
    (G : POVMIn (LowIndDegPoly (F := F) (m := n) (d := d)) 𝒜)
    (f : Q → LowIndDegPoly (F := F) (m := n) (d := d) → F) (P : Q → POVMIn F ℬ) :
    K.inconsistency μ (fun q => G.map (f q)) P
      = 1 - ∑ q, μ q * ∑ g, K.bornProb (G.op g) ((P q).op (f q g)) := by
  have hfib : ∀ q, (∑ a : F, ∑ b : F, if a = b then 0 else
      K.bornProb ((G.map (f q)).op a) ((P q).op b))
      = ∑ g, ∑ b : F, if f q g = b then 0 else K.bornProb (G.op g) ((P q).op b) := by
    intro q
    have h1 : ∀ a b : F, (if a = b then (0 : ℝ) else
        K.bornProb ((G.map (f q)).op a) ((P q).op b))
        = ∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := n) (d := d) => f q g = a,
            if a = b then 0 else K.bornProb (G.op g) ((P q).op b) := by
      intro a b
      rw [POVMIn.map_op, K.bornProb_sum_left]
      split_ifs
      · simp
      · rfl
    simp_rw [h1]
    rw [← Finset.sum_fiberwise univ fun g : LowIndDegPoly (F := F) (m := n) (d := d) => f q g]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [(mem_filter.mp hg).2]
  have hsum : ∀ q, (∑ g, ∑ b : F, if f q g = b then 0 else
      K.bornProb (G.op g) ((P q).op b))
      = 1 - ∑ g, K.bornProb (G.op g) ((P q).op (f q g)) := by
    intro q
    simp_rw [sum_ite_eq_zero_sub, ← K.bornProb_sum_right, (P q).sum_op]
    rw [Finset.sum_sub_distrib, ← K.bornProb_sum_left, G.sum_op, K.bornProb_one_one hK]
  unfold BipartiteModel.inconsistency
  simp only [hfib, hsum, mul_sub, mul_one, Finset.sum_sub_distrib, hμ]

end Coarse

/-! ## The block marginals of the uniform padded point -/

section BlockMarg

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]

/-- The `z` block of a uniform padded point is uniform. -/
theorem sum_uniform_zBlk (f : Point F m → ℝ) :
    ∑ u, uniform (Point F (4 * m)) u * f (zBlk u) = ∑ z, uniform (Point F m) z * f z := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [uniform, ← Finset.mul_sum]
  rw [sum_point_pad_z, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  push_cast
  rw [show 4 * m = 2 * m + m + m by ring, pow_add, pow_add]
  field_simp

/-- The `x` block of a uniform padded point is uniform. -/
theorem sum_uniform_xBlk (f : Point F m → ℝ) :
    ∑ u, uniform (Point F (4 * m)) u * f (xBlk u) = ∑ x, uniform (Point F m) x * f x := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [uniform, ← Finset.mul_sum]
  rw [sum_point_pad_x, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  push_cast
  rw [show 4 * m = 2 * m + m + m by ring, pow_add, pow_add]
  field_simp

end BlockMarg

/-! ## The evaluated marginals -/

section Marginals

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
  {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
/-- `a ≤ c + b` for nonnegative reals gives `a² - 2ab ≤ c²`. -/
theorem sq_sub_two_mul_le_sq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c + b) :
    a ^ 2 - 2 * (a * b) ≤ c ^ 2 := by
  by_cases hab : a ≤ b
  · nlinarith [mul_nonneg ha hb, sq_nonneg c, mul_le_mul_of_nonneg_left hab ha]
  · push Not at hab
    have h1 : a - b ≤ c := by linarith
    have h2 : 0 ≤ a - b := by linarith
    nlinarith [mul_le_mul h1 h1 h2 hc, sq_nonneg b]

omit [DecidableEq F] [NeZero m] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- **The products estimate bounds the weight through `B` from below**: from
`∑_g E_u ‖(G_g ⊗ (1 - B_u(g(u)))) Φ‖² ≤ Δ`, the triangle inequality and Cauchy--Schwarz give
`∑_g E_u ‖(G_g ⊗ B_u(g(u))) Φ‖² ≥ 1 - 2√Δ`. -/
theorem one_sub_two_sqrt_le_sum_snorm_sq {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1)
    (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) 𝒜) (hG : IsPVMIn G.op)
    (B : Point F (4 * m) → F → ℬ) {Δ : ℝ}
    (hprod : ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
      (K.πA (G.op g) * K.πB (1 - B u (g.eval u))) ^ 2 ≤ Δ) :
    1 - 2 * Real.sqrt Δ ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
      (K.πA (G.op g) * K.πB (B u (g.eval u))) ^ 2 := by
  have hterm : ∀ (u : Point F (4 * m)) g,
      K.snorm (K.πA (G.op g) * K.πB 1) ^ 2
        - 2 * (K.snorm (K.πA (G.op g) * K.πB 1)
          * K.snorm (K.πA (G.op g) * K.πB (1 - B u (g.eval u))))
      ≤ K.snorm (K.πA (G.op g) * K.πB (B u (g.eval u))) ^ 2 := by
    intro u g
    refine sq_sub_two_mul_le_sq (K.snorm_nonneg _) (K.snorm_nonneg _) (K.snorm_nonneg _) ?_
    have h := K.snorm_add_le (K.πA (G.op g) * K.πB (B u (g.eval u)))
      (K.πA (G.op g) * K.πB (1 - B u (g.eval u)))
    rwa [← mul_add, ← map_add,
      show B u (g.eval u) + (1 - B u (g.eval u)) = (1 : ℬ) by abel] at h
  have hone : ∀ g, K.snorm (K.πA (G.op g) * K.πB 1) ^ 2 = K.bornProb (G.op g) 1 := fun g => by
    rw [K.snorm_sq_πA_mul_πB (hG.isStarProjection g), star_one, one_mul]
  have hsum1 : ∑ u, uniform (Point F (4 * m)) u
      * ∑ g, K.snorm (K.πA (G.op g) * K.πB 1) ^ 2 = 1 := by
    simp_rw [hone, sum_bornProb_M_one hK G, mul_one]
    exact sum_uniform_eq_one _
  have hCS : ∑ u, uniform (Point F (4 * m)) u
      * ∑ g, K.snorm (K.πA (G.op g) * K.πB 1)
        * K.snorm (K.πA (G.op g) * K.πB (1 - B u (g.eval u)))
      ≤ Real.sqrt Δ := by
    have h := sum_weighted_mul_le_sqrt
      (fun p : Point F (4 * m) × LowIndDegPoly (F := F) (m := 4 * m) (d := d) =>
        uniform (Point F (4 * m)) p.1)
      (fun p => K.snorm (K.πA (G.op p.2) * K.πB 1))
      (fun p => K.snorm (K.πA (G.op p.2) * K.πB (1 - B p.1 (p.2.eval p.1))))
      (fun p => uniform_nonneg _ _)
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at h
    simp only [← Finset.mul_sum] at h
    rw [hsum1, Real.sqrt_one, one_mul] at h
    exact h.trans (Real.sqrt_le_sqrt hprod)
  have hu : ∀ u : Point F (4 * m),
      (∑ g, K.snorm (K.πA (G.op g) * K.πB 1) ^ 2)
        - 2 * ∑ g, K.snorm (K.πA (G.op g) * K.πB 1)
          * K.snorm (K.πA (G.op g) * K.πB (1 - B u (g.eval u)))
      ≤ ∑ g, K.snorm (K.πA (G.op g) * K.πB (B u (g.eval u))) ^ 2 := by
    intro u
    have := Finset.sum_le_sum fun g (_ : g ∈ univ) => hterm u g
    rwa [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
  have hfinal := Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (hu u) (uniform_nonneg (Point F (4 * m)) u)
  have hsplit : ∑ u, uniform (Point F (4 * m)) u
      * ((∑ g, K.snorm (K.πA (G.op g) * K.πB 1) ^ 2)
        - 2 * ∑ g, K.snorm (K.πA (G.op g) * K.πB 1)
          * K.snorm (K.πA (G.op g) * K.πB (1 - B u (g.eval u))))
      = (∑ u, uniform (Point F (4 * m)) u
          * ∑ g, K.snorm (K.πA (G.op g) * K.πB 1) ^ 2)
        - 2 * ∑ u, uniform (Point F (4 * m)) u
          * ∑ g, K.snorm (K.πA (G.op g) * K.πB 1)
            * K.snorm (K.πA (G.op g) * K.πB (1 - B u (g.eval u))) := by
    rw [Finset.mul_sum univ (fun u => uniform (Point F (4 * m)) u
      * ∑ g, K.snorm (K.πA (G.op g) * K.πB 1)
        * K.snorm (K.πA (G.op g) * K.πB (1 - B u (g.eval u)))) 2,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [hsplit, hsum1] at hfinal
  linarith

variable {X Z : Point F m → F → ℬ}

/-- **The `Z` marginal of the completed measurement tracks the second player's `Z` point
measurement**: from the products estimate for the order `X_a Z_b` and the weight `δ_G` of the
non-good outcomes, `E_z ∑_g ⟨G_g ⊗ Z_{g_Z(z)}(z)⟩ ≥ 1 - 2√Δ - 2/q - δ_G`, where `g_Z` is the
second component of the relabelled outcome. -/
theorem marg_Z_ge (hd : 1 ≤ d) {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1)
    (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) 𝒜) (hG : IsPVMIn G.op)
    (hX : ∀ x, IsPVMIn (X x)) (hZ : ∀ z, IsPVMIn (Z z)) {Δ δG : ℝ}
    (hprod : ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
      (K.πA (G.op g) * K.πB (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2 ≤ Δ)
    (hbad : ∑ g ∈ univ.filter (fun g => ¬ IsGood g), K.bornProb (G.op g) 1 ≤ δG) :
    1 - 2 * Real.sqrt Δ - 2 / Fintype.card F - δG
      ≤ ∑ z, uniform (Point F m) z
          * ∑ g, K.bornProb (G.op g) (Z z ((PolyPair.proj .Z (pairOf hd g)).eval z)) := by
  have hW0 : ∀ g, 0 ≤ K.bornProb (G.op g) 1 := fun g =>
    K.bornProb_nonneg (hG.nonneg g) zero_le_one
  have hq0 : (0 : ℝ) ≤ 2 / Fintype.card F := by positivity
  have h1 := one_sub_two_sqrt_le_sum_snorm_sq hK G hG (ordComb ordXZ X Z) hprod
  have hswap : ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
      (K.πA (G.op g) * K.πB (ordComb ordXZ X Z u (g.eval u))) ^ 2
      = ∑ g, ∑ u, uniform (Point F (4 * m)) u * K.snorm
        (K.πA (G.op g) * K.πB (ordComb ordXZ X Z u (g.eval u))) ^ 2 := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  have hg : ∀ g, ∑ u, uniform (Point F (4 * m)) u * K.snorm
      (K.πA (G.op g) * K.πB (ordComb ordXZ X Z u (g.eval u))) ^ 2
      ≤ 2 / Fintype.card F * K.bornProb (G.op g) 1
        + ∑ z, uniform (Point F m) z
          * K.bornProb (G.op g) (Z z ((PolyPair.proj .Z (pairOf hd g)).eval z))
        + (if IsGood g then (0 : ℝ) else K.bornProb (G.op g) 1) := by
    intro g
    have hM0 : 0 ≤ ∑ z, uniform (Point F m) z
        * K.bornProb (G.op g) (Z z ((PolyPair.proj .Z (pairOf hd g)).eval z)) :=
      Finset.sum_nonneg fun z _ => mul_nonneg (uniform_nonneg _ _)
        (K.bornProb_nonneg (hG.nonneg g) ((hZ z).nonneg _))
    by_cases hgood : IsGood g
    · rw [ite_eq_left hgood, add_zero]
      have h := sum_uniform_snorm_sq_ordComb_XZ_le_of_isLinAB hd K (hG.isStarProjection g) hX hZ
        (isLinAB_of_isGood hgood)
      have hre : ∀ u₀ : Point F (4 * m), K.bornProb (G.op g) (Z (zBlk u₀) ((gB hd g).eval u₀))
          = K.bornProb (G.op g)
            (Z (zBlk u₀) ((PolyPair.proj .Z (pairOf hd g)).eval (zBlk u₀))) := fun u₀ => by
        rw [pairOf_of_isGood hd hgood, PolyPair.proj_Z, eval_gZ hd hgood]
      simp_rw [hre] at h
      rw [sum_uniform_zBlk (fun z => K.bornProb (G.op g)
        (Z z ((PolyPair.proj .Z (pairOf hd g)).eval z)))] at h
      exact h
    · rw [ite_eq_right hgood]
      have hle : ∀ u : Point F (4 * m), K.snorm (K.πA (G.op g)
          * K.πB (ordComb ordXZ X Z u (g.eval u))) ^ 2 ≤ K.bornProb (G.op g) 1 := fun u =>
        snorm_sq_ordComb_ordXZ_le K (hG.isStarProjection g) (hX _) (hZ _) _ _ _
      calc _ ≤ ∑ u, uniform (Point F (4 * m)) u * K.bornProb (G.op g) 1 :=
            Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hle u) (uniform_nonneg _ _)
        _ = K.bornProb (G.op g) 1 := by rw [← Finset.sum_mul, sum_uniform_eq_one, one_mul]
        _ ≤ _ := by nlinarith [mul_nonneg hq0 (hW0 g)]
  have hsumg := Finset.sum_le_sum fun g (_ : g ∈ univ) => hg g
  have hA : ∑ g, 2 / Fintype.card F * K.bornProb (G.op g) 1 = 2 / Fintype.card F := by
    rw [← Finset.mul_sum, sum_bornProb_M_one hK G, mul_one]
  have hB : ∑ g, ∑ z, uniform (Point F m) z
      * K.bornProb (G.op g) (Z z ((PolyPair.proj .Z (pairOf hd g)).eval z))
      = ∑ z, uniform (Point F m) z
        * ∑ g, K.bornProb (G.op g) (Z z ((PolyPair.proj .Z (pairOf hd g)).eval z)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ => (Finset.mul_sum _ _ _).symm
  have hC : ∑ g, (if IsGood g then (0 : ℝ) else K.bornProb (G.op g) 1)
      = ∑ g ∈ univ.filter (fun g => ¬ IsGood g), K.bornProb (G.op g) 1 := by
    rw [Finset.sum_filter]
    simp only [ite_not]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC] at hsumg
  linarith

/-- **The `X` marginal**, from the order `Z_b X_a`: the mirror image. -/
theorem marg_X_ge (hd : 1 ≤ d) {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1)
    (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) 𝒜) (hG : IsPVMIn G.op)
    (hX : ∀ x, IsPVMIn (X x)) (hZ : ∀ z, IsPVMIn (Z z)) {Δ δG : ℝ}
    (hprod : ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
      (K.πA (G.op g) * K.πB (1 - ordComb ordZX X Z u (g.eval u))) ^ 2 ≤ Δ)
    (hbad : ∑ g ∈ univ.filter (fun g => ¬ IsGood g), K.bornProb (G.op g) 1 ≤ δG) :
    1 - 2 * Real.sqrt Δ - 2 / Fintype.card F - δG
      ≤ ∑ x, uniform (Point F m) x
          * ∑ g, K.bornProb (G.op g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x)) := by
  have hW0 : ∀ g, 0 ≤ K.bornProb (G.op g) 1 := fun g =>
    K.bornProb_nonneg (hG.nonneg g) zero_le_one
  have hq0 : (0 : ℝ) ≤ 2 / Fintype.card F := by positivity
  have h1 := one_sub_two_sqrt_le_sum_snorm_sq hK G hG (ordComb ordZX X Z) hprod
  have hswap : ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
      (K.πA (G.op g) * K.πB (ordComb ordZX X Z u (g.eval u))) ^ 2
      = ∑ g, ∑ u, uniform (Point F (4 * m)) u * K.snorm
        (K.πA (G.op g) * K.πB (ordComb ordZX X Z u (g.eval u))) ^ 2 := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  have hg : ∀ g, ∑ u, uniform (Point F (4 * m)) u * K.snorm
      (K.πA (G.op g) * K.πB (ordComb ordZX X Z u (g.eval u))) ^ 2
      ≤ 2 / Fintype.card F * K.bornProb (G.op g) 1
        + ∑ x, uniform (Point F m) x
          * K.bornProb (G.op g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x))
        + (if IsGood g then (0 : ℝ) else K.bornProb (G.op g) 1) := by
    intro g
    have hM0 : 0 ≤ ∑ x, uniform (Point F m) x
        * K.bornProb (G.op g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x)) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (uniform_nonneg _ _)
        (K.bornProb_nonneg (hG.nonneg g) ((hX x).nonneg _))
    by_cases hgood : IsGood g
    · rw [ite_eq_left hgood, add_zero]
      have h := sum_uniform_snorm_sq_ordComb_ZX_le_of_isLinAB hd K (hG.isStarProjection g) hX hZ
        (isLinAB_of_isGood hgood)
      have hre : ∀ u₀ : Point F (4 * m), K.bornProb (G.op g) (X (xBlk u₀) ((gA hd g).eval u₀))
          = K.bornProb (G.op g)
            (X (xBlk u₀) ((PolyPair.proj .X (pairOf hd g)).eval (xBlk u₀))) := fun u₀ => by
        rw [pairOf_of_isGood hd hgood, PolyPair.proj_X, eval_gX hd hgood]
      simp_rw [hre] at h
      rw [sum_uniform_xBlk (fun x => K.bornProb (G.op g)
        (X x ((PolyPair.proj .X (pairOf hd g)).eval x)))] at h
      exact h
    · rw [ite_eq_right hgood]
      have hle : ∀ u : Point F (4 * m), K.snorm (K.πA (G.op g)
          * K.πB (ordComb ordZX X Z u (g.eval u))) ^ 2 ≤ K.bornProb (G.op g) 1 := fun u => by
        rw [ordComb, ptComb_ordZX_eq]
        exact snorm_sq_ordComb_ordXZ_le K (hG.isStarProjection g) (hZ _) (hX _) _ _ _
      calc _ ≤ ∑ u, uniform (Point F (4 * m)) u * K.bornProb (G.op g) 1 :=
            Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hle u) (uniform_nonneg _ _)
        _ = K.bornProb (G.op g) 1 := by rw [← Finset.sum_mul, sum_uniform_eq_one, one_mul]
        _ ≤ _ := by nlinarith [mul_nonneg hq0 (hW0 g)]
  have hsumg := Finset.sum_le_sum fun g (_ : g ∈ univ) => hg g
  have hA : ∑ g, 2 / Fintype.card F * K.bornProb (G.op g) 1 = 2 / Fintype.card F := by
    rw [← Finset.mul_sum, sum_bornProb_M_one hK G, mul_one]
  have hB : ∑ g, ∑ x, uniform (Point F m) x
      * K.bornProb (G.op g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x))
      = ∑ x, uniform (Point F m) x
        * ∑ g, K.bornProb (G.op g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
  have hC : ∑ g, (if IsGood g then (0 : ℝ) else K.bornProb (G.op g) 1)
      = ∑ g ∈ univ.filter (fun g => ¬ IsGood g), K.bornProb (G.op g) 1 := by
    rw [Finset.sum_filter]
    simp only [ite_not]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC] at hsumg
  linarith

/-- **`lem:qld-global-sandwich`, the `Z` marginal in consistency form**: the evaluated `Z`
marginal of the completed measurement against a family `N` whose elements are the `Z z a`. -/
theorem inconsistency_evalMarg_Z_le (hd : 1 ≤ d) {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1)
    (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) 𝒜) (hG : IsPVMIn G.op)
    (hX : ∀ x, IsPVMIn (X x)) (hZ : ∀ z, IsPVMIn (Z z)) (N : Point F m → POVMIn F ℬ)
    (hN : ∀ z a, (N z).op a = Z z a) {Δ δG : ℝ}
    (hprod : ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
      (K.πA (G.op g) * K.πB (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2 ≤ Δ)
    (hbad : ∑ g ∈ univ.filter (fun g => ¬ IsGood g), K.bornProb (G.op g) 1 ≤ δG) :
    K.inconsistency (uniform (Point F m)) (fun z => evalMarg (pairMeas hd G) .Z z) N
      ≤ 2 * Real.sqrt Δ + 2 / Fintype.card F + δG := by
  have h := marg_Z_ge hd hK G hG hX hZ hprod hbad
  simp_rw [evalMarg_pairMeas]
  rw [inconsistency_map_eq _ (sum_uniform_eq_one _) hK G
    (fun z g => (PolyPair.proj .Z (pairOf hd g)).eval z) N]
  simp_rw [hN]
  linarith

/-- **`lem:qld-global-sandwich`, the `X` marginal in consistency form.** -/
theorem inconsistency_evalMarg_X_le (hd : 1 ≤ d) {K : BipartiteModel 𝒞 𝒜 ℬ} (hK : ‖K.ψ‖ = 1)
    (G : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) 𝒜) (hG : IsPVMIn G.op)
    (hX : ∀ x, IsPVMIn (X x)) (hZ : ∀ z, IsPVMIn (Z z)) (N : Point F m → POVMIn F ℬ)
    (hN : ∀ x a, (N x).op a = X x a) {Δ δG : ℝ}
    (hprod : ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm
      (K.πA (G.op g) * K.πB (1 - ordComb ordZX X Z u (g.eval u))) ^ 2 ≤ Δ)
    (hbad : ∑ g ∈ univ.filter (fun g => ¬ IsGood g), K.bornProb (G.op g) 1 ≤ δG) :
    K.inconsistency (uniform (Point F m)) (fun x => evalMarg (pairMeas hd G) .X x) N
      ≤ 2 * Real.sqrt Δ + 2 / Fintype.card F + δG := by
  have h := marg_X_ge hd hK G hG hX hZ hprod hbad
  simp_rw [evalMarg_pairMeas]
  rw [inconsistency_map_eq _ (sum_uniform_eq_one _) hK G
    (fun x g => (PolyPair.proj .X (pairOf hd g)).eval x) N]
  simp_rw [hN]
  linarith

end Marginals

end MIPRE.QLD

end

end
