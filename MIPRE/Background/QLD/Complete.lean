/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Separate
import MIPRE.Background.QLD.Simul
import MIPRE.Foundations.RegisterReindex
import MIPRE.Background.LIDT.BlockPoly

/-!
# Completing the pair measurement and its evaluated marginals (`lem:qld-global-complete`,
`lem:qld-global-sandwich`)

Stage 4 ends with the interface `SimulPair` (`lem:qld-simultaneous`): a projective measurement
with outcomes pairs `(g_X, g_Z)` of polynomials in `m` variables, whose evaluated marginals are
consistent with the opposite party's expanded point measurements. This file builds it from a
global measurement `G` with outcomes in `LowIndDegPoly F (4m) d` (the polynomials on the padded
point) and the estimates of stage 4b, abstractly: for a projective `G` on Alice's register and
two projective families `X x`, `Z z` on Bob's.

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
The register transport to the shape of `SimulPair` (`reindex_aOp_aOp`, `isPVM_reindex`) and the
instance itself are in `PaddedLIDT.lean`.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## Reindexing a projective family, and the identity extension along associativity -/

section Reindex

variable {d d' Λ : Type*} [Fintype d] [DecidableEq d] [Fintype d'] [DecidableEq d'] [Fintype Λ]

/-- A reindexed projective family is projective. -/
theorem isPVM_reindex (e : d ≃ d') {P : Λ → Matrix d d ℂ} (h : IsPVM P) :
    IsPVM fun a => Matrix.reindex e e (P a) where
  isSelfAdjoint a := by rw [Matrix.conjTranspose_reindex, h.isSelfAdjoint]
  idem a := by
    rw [← reindexStarAlgEquiv_apply, ← map_mul, h.idem]
  sum_eq_one := by
    simp only [← reindexStarAlgEquiv_apply]
    rw [← map_sum, h.sum_eq_one, map_one]

/-- A reindexed projective POVM is projective. -/
theorem isPVM_reindex_povm {A : Type*} [Fintype A] (e : d ≃ d') {M : POVM A d}
    (h : IsPVM fun a => ((M.mats a).val)) : IsPVM fun a => (((M.reindex e).mats a).val) := by
  simp only [POVM.reindex_mats]
  exact isPVM_reindex e h

variable {E E' : Type*} [Fintype E] [DecidableEq E] [Fintype E'] [DecidableEq E']

omit [Fintype d] [DecidableEq d] [Fintype E] [Fintype E'] in
/-- Extending twice by the identity and reassociating is extending once by the product ancilla. -/
theorem reindex_aOp_aOp (X : Matrix d d ℂ) :
    Matrix.reindex (Equiv.prodAssoc d E E') (Equiv.prodAssoc d E E')
        (aOp (aOp X : Matrix (d × E) (d × E) ℂ) : Matrix ((d × E) × E') ((d × E) × E') ℂ)
      = (aOp X : Matrix (d × (E × E')) (d × (E × E')) ℂ) := by
  simp only [aOp]
  rw [Matrix.kronecker_assoc, Matrix.one_kronecker_one]

/-- The POVM form of `reindex_aOp_aOp`. -/
theorem POVM.aOp_aOp_reindex {A : Type*} [Fintype A] (M : POVM A d) :
    ((M.aOp (E := E)).aOp (E := E')).reindex (Equiv.prodAssoc d E E') = M.aOp (E := E × E') :=
  POVM.ext' fun a => by
    rw [POVM.reindex_mats, POVM.aOp_mats, POVM.aOp_mats, POVM.aOp_mats, reindex_aOp_aOp]

end Reindex

section PVM

variable {R A : Type*} [Fintype R] [DecidableEq R] [Fintype A]

/-- A projective measurement's family is a projective family. -/
theorem ProjectiveMeasurement.isPVM_M (G : ProjectiveMeasurement Unit A (Matrix R R ℂ)) :
    IsPVM fun a => G.M () a :=
  ⟨fun a => G.selfAdjoint () a, fun a => G.projective () a, G.normalized ()⟩

end PVM

end MIPRE

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
          rw [patch, if_neg (fun h => (mem_abSet.mp h).elim hka hkb)] at this
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
          rw [patch, if_neg (fun h => (mem_abSet.mp h).elim hka hkb)] at this
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
    (hg : IsGood g) : pairOf hd g = (gX hd g, gZ hd g) := if_pos hg

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- **The completed pair measurement**: the global measurement coarse-grained by the relabelling.
The non-good outcomes are absorbed into the pair `(0, 0)`: the paper's complement `R`, added to a
fixed legal outcome. -/
def pairMeas (hd : 1 ≤ d)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix R R ℂ)) : POVM (PolyPair F m d) R :=
  (G.toPOVM ()).map (pairOf hd)

theorem pairMeas_mats (hd : 1 ≤ d)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix R R ℂ)) (p : PolyPair F m d) :
    (((pairMeas hd G).mats p).val)
      = ∑ g ∈ univ.filter fun g => pairOf hd g = p, G.M () g :=
  POVM.map_mats _ _ _

/-- **The completed pair measurement is projective.** -/
theorem isPVM_pairMeas (hd : 1 ≤ d)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix R R ℂ)) : IsPVM fun p => (((pairMeas hd G).mats p).val) := by
  have hfun : (fun p => (((pairMeas hd G).mats p).val))
      = fun p => ∑ g ∈ univ.filter fun g => pairOf hd g = p, G.M () g :=
    funext fun p => pairMeas_mats hd G p
  rw [hfun]
  exact G.isPVM_M.coarse _

/-- The evaluated marginal of the completed measurement is the global measurement coarse-grained
by the evaluated component of the pair. -/
theorem evalMarg_pairMeas (hd : 1 ≤ d)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix R R ℂ)) (W : Bas) (u : Point F m) :
    evalMarg (pairMeas hd G) W u
      = (G.toPOVM ()).map fun g => (PolyPair.proj W (pairOf hd g)).eval u := by
  rw [evalMarg, pairMeas, POVM.map_map]

end Pairs

/-! ## The inconsistency of a coarse-grained global measurement -/

section Coarse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ} {RA RB : Type*} [Fintype RA]
  [DecidableEq RA] [Fintype RB] [DecidableEq RB]

omit [Field F] in
/-- **The inconsistency of a coarse-graining of a projective measurement**, against a family of
POVMs indexed by the same questions: one minus the average agreement, outcome by outcome of the
original measurement. `inconsistency_evalPOVM_eq` is the case of evaluation at the point. -/
theorem inconsistency_map_eq {Q : Type*} [Fintype Q] (μ : Q → ℝ) (hμ : ∑ q, μ q = 1)
    {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := n) (d := d)) (Matrix RA RA ℂ))
    (f : Q → LowIndDegPoly (F := F) (m := n) (d := d) → F) (P : Q → POVM F RB) :
    inconsistency μ Φ (fun q => (G.toPOVM ()).map (f q)) P
      = 1 - ∑ q, μ q * ∑ g, bornProb Φ (G.M () g) (((P q).mats (f q g)).val) := by
  have hfib : ∀ q, (∑ a : F, ∑ b : F, if a = b then 0 else
      bornProb Φ ((((G.toPOVM ()).map (f q)).mats a).val) (((P q).mats b).val))
      = ∑ g, ∑ b : F, if f q g = b then 0 else
          bornProb Φ (G.M () g) (((P q).mats b).val) := by
    intro q
    have h1 : ∀ a b : F, (if a = b then (0 : ℝ) else
        bornProb Φ ((((G.toPOVM ()).map (f q)).mats a).val) (((P q).mats b).val))
        = ∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := n) (d := d) => f q g = a,
            if a = b then 0 else bornProb Φ (G.M () g) (((P q).mats b).val) := by
      intro a b
      rw [POVM.map_mats, bornProb_sum_left]
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
      bornProb Φ (G.M () g) (((P q).mats b).val))
      = 1 - ∑ g, bornProb Φ (G.M () g) (((P q).mats (f q g)).val) := by
    intro q
    simp_rw [sum_ite_eq_zero_sub, ← bornProb_sum_right, POVM.sum_val]
    rw [Finset.sum_sub_distrib, ← bornProb_sum_left, G.normalized, bornProb_one_one hΦ]
  unfold inconsistency
  simp only [bornProb_def, hfib, hsum, mul_sub, mul_one, Finset.sum_sub_distrib, hμ]

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

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m] {RA RB : Type*}
  [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]

omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] [Fintype RA] [DecidableEq RA] [Fintype RB]
  [DecidableEq RB] in
/-- `a ≤ c + b` for nonnegative reals gives `a² - 2ab ≤ c²`. -/
theorem sq_sub_two_mul_le_sq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c + b) :
    a ^ 2 - 2 * (a * b) ≤ c ^ 2 := by
  by_cases hab : a ≤ b
  · nlinarith [mul_nonneg ha hb, sq_nonneg c, mul_le_mul_of_nonneg_left hab ha]
  · push Not at hab
    have h1 : a - b ≤ c := by linarith
    have h2 : 0 ≤ a - b := by linarith
    nlinarith [mul_le_mul h1 h1 h2 hc, sq_nonneg b]

omit [DecidableEq F] [NeZero m] in
/-- **The products estimate bounds the weight through `B` from below**: from
`∑_g E_u ‖(G_g ⊗ (1 - B_u(g(u)))) Φ‖² ≤ Δ`, the triangle inequality and Cauchy--Schwarz give
`∑_g E_u ‖(G_g ⊗ B_u(g(u))) Φ‖² ≥ 1 - 2√Δ`. -/
theorem one_sub_two_sqrt_le_sum_snorm_sq {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (B : Point F (4 * m) → F → Matrix RB RB ℂ) {Δ : ℝ}
    (hprod : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - B u (g.eval u))) ^ 2 ≤ Δ) :
    1 - 2 * Real.sqrt Δ ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (B u (g.eval u))) ^ 2 := by
  have hsa : ∀ g, (G.M () g)ᴴ = G.M () g := fun g => G.selfAdjoint () g
  have hidem : ∀ g, G.M () g * G.M () g = G.M () g := fun g => G.projective () g
  have hterm : ∀ (u : Point F (4 * m)) g,
      snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp 1) ^ 2
        - 2 * (snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp 1)
          * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - B u (g.eval u))))
      ≤ snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (B u (g.eval u))) ^ 2 := by
    intro u g
    refine sq_sub_two_mul_le_sq (snorm_nonneg _ _) (snorm_nonneg _ _) (snorm_nonneg _ _) ?_
    have h := snorm_add_le Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (B u (g.eval u)))
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - B u (g.eval u)))
    rwa [← Matrix.mul_add, ← bOp_add,
      show B u (g.eval u) + (1 - B u (g.eval u)) = (1 : Matrix RB RB ℂ) by abel] at h
  have hone : ∀ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp 1) ^ 2
      = bornProb Φ (G.M () g) 1 := fun g => by
    rw [snorm_sq_aOp_mul_bOp Φ (hsa g) (hidem g), Matrix.conjTranspose_one, Matrix.one_mul]
  have hsum1 : ∑ u, uniform (Point F (4 * m)) u
      * ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp 1) ^ 2 = 1 := by
    simp_rw [hone, sum_bornProb_M_one hΦ G, mul_one]
    exact sum_uniform_eq_one _
  have hCS : ∑ u, uniform (Point F (4 * m)) u
      * ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp 1)
        * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - B u (g.eval u)))
      ≤ Real.sqrt Δ := by
    have h := sum_weighted_mul_le_sqrt
      (fun p : Point F (4 * m) × LowIndDegPoly (F := F) (m := 4 * m) (d := d) =>
        uniform (Point F (4 * m)) p.1)
      (fun p => snorm Φ ((aOp (G.M () p.2) : Matrix (RA × RB) _ ℂ) * bOp 1))
      (fun p => snorm Φ ((aOp (G.M () p.2) : Matrix (RA × RB) _ ℂ)
        * bOp (1 - B p.1 (p.2.eval p.1))))
      (fun p => uniform_nonneg _ _)
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at h
    simp only [← Finset.mul_sum] at h
    rw [hsum1, Real.sqrt_one, one_mul] at h
    exact h.trans (Real.sqrt_le_sqrt hprod)
  have hu : ∀ u : Point F (4 * m),
      (∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp 1) ^ 2)
        - 2 * ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp 1)
          * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - B u (g.eval u)))
      ≤ ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (B u (g.eval u))) ^ 2 := by
    intro u
    have := Finset.sum_le_sum fun g (_ : g ∈ univ) => hterm u g
    rwa [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
  have hfinal := Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (hu u) (uniform_nonneg (Point F (4 * m)) u)
  have hsplit : ∑ u, uniform (Point F (4 * m)) u
      * ((∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp 1) ^ 2)
        - 2 * ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp 1)
          * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - B u (g.eval u))))
      = (∑ u, uniform (Point F (4 * m)) u
          * ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp 1) ^ 2)
        - 2 * ∑ u, uniform (Point F (4 * m)) u
          * ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp 1)
            * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - B u (g.eval u))) := by
    rw [Finset.mul_sum univ (fun u => uniform (Point F (4 * m)) u
      * ∑ g, snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp 1)
        * snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - B u (g.eval u)))) 2,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [hsplit, hsum1] at hfinal
  linarith

variable {X Z : Point F m → F → Matrix RB RB ℂ}

/-- **The `Z` marginal of the completed measurement tracks Bob's `Z` point measurement**: from
the products estimate for the order `X_a Z_b` and the weight `δ_G` of the non-good outcomes,
`E_z ∑_g ⟨G_g ⊗ Z_{g_Z(z)}(z)⟩ ≥ 1 - 2√Δ - 2/q - δ_G`, where `g_Z` is the second component of
the relabelled outcome. -/
theorem marg_Z_ge (hd : 1 ≤ d) {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z)) {Δ δG : ℝ}
    (hprod : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2
      ≤ Δ)
    (hbad : ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1 ≤ δG) :
    1 - 2 * Real.sqrt Δ - 2 / Fintype.card F - δG
      ≤ ∑ z, uniform (Point F m) z
          * ∑ g, bornProb Φ (G.M () g) (Z z ((PolyPair.proj .Z (pairOf hd g)).eval z)) := by
  have hsa : ∀ g, (G.M () g)ᴴ = G.M () g := fun g => G.selfAdjoint () g
  have hidem : ∀ g, G.M () g * G.M () g = G.M () g := fun g => G.projective () g
  have hW0 : ∀ g, 0 ≤ bornProb Φ (G.M () g) 1 := fun g =>
    bornProb_nonneg Φ (posSemidef_of_proj (hsa g) (hidem g)) Matrix.PosSemidef.one
  have hq0 : (0 : ℝ) ≤ 2 / Fintype.card F := by positivity
  have h1 := one_sub_two_sqrt_le_sum_snorm_sq hΦ G (ordComb ordXZ X Z) hprod
  have hswap : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordXZ X Z u (g.eval u))) ^ 2
      = ∑ g, ∑ u, uniform (Point F (4 * m)) u * snorm Φ
        ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordXZ X Z u (g.eval u))) ^ 2 := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  have hg : ∀ g, ∑ u, uniform (Point F (4 * m)) u * snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordXZ X Z u (g.eval u))) ^ 2
      ≤ 2 / Fintype.card F * bornProb Φ (G.M () g) 1
        + ∑ z, uniform (Point F m) z
          * bornProb Φ (G.M () g) (Z z ((PolyPair.proj .Z (pairOf hd g)).eval z))
        + (if IsGood g then (0 : ℝ) else bornProb Φ (G.M () g) 1) := by
    intro g
    have hM0 : 0 ≤ ∑ z, uniform (Point F m) z
        * bornProb Φ (G.M () g) (Z z ((PolyPair.proj .Z (pairOf hd g)).eval z)) :=
      Finset.sum_nonneg fun z _ => mul_nonneg (uniform_nonneg _ _)
        (bornProb_nonneg Φ (posSemidef_of_proj (hsa g) (hidem g)) ((hZ z).posSemidef _))
    by_cases hgood : IsGood g
    · rw [if_pos hgood, add_zero]
      have h := sum_uniform_snorm_sq_ordComb_XZ_le_of_isLinAB hd Φ (hsa g) (hidem g) hX hZ
        (isLinAB_of_isGood hgood)
      have hre : ∀ u₀ : Point F (4 * m), bornProb Φ (G.M () g) (Z (zBlk u₀) ((gB hd g).eval u₀))
          = bornProb Φ (G.M () g)
            (Z (zBlk u₀) ((PolyPair.proj .Z (pairOf hd g)).eval (zBlk u₀))) := fun u₀ => by
        rw [pairOf_of_isGood hd hgood, PolyPair.proj_Z, eval_gZ hd hgood]
      simp_rw [hre] at h
      rw [sum_uniform_zBlk (fun z => bornProb Φ (G.M () g)
        (Z z ((PolyPair.proj .Z (pairOf hd g)).eval z)))] at h
      exact h
    · rw [if_neg hgood]
      have hle : ∀ u : Point F (4 * m), snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (ordComb ordXZ X Z u (g.eval u))) ^ 2 ≤ bornProb Φ (G.M () g) 1 := fun u =>
        snorm_sq_ordComb_ordXZ_le Φ (hsa g) (hidem g) (hX _) (hZ _) _ _ _
      calc _ ≤ ∑ u, uniform (Point F (4 * m)) u * bornProb Φ (G.M () g) 1 :=
            Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hle u) (uniform_nonneg _ _)
        _ = bornProb Φ (G.M () g) 1 := by rw [← Finset.sum_mul, sum_uniform_eq_one, one_mul]
        _ ≤ _ := by nlinarith [mul_nonneg hq0 (hW0 g)]
  have hsumg := Finset.sum_le_sum fun g (_ : g ∈ univ) => hg g
  have hA : ∑ g, 2 / Fintype.card F * bornProb Φ (G.M () g) 1 = 2 / Fintype.card F := by
    rw [← Finset.mul_sum, sum_bornProb_M_one hΦ G, mul_one]
  have hB : ∑ g, ∑ z, uniform (Point F m) z
      * bornProb Φ (G.M () g) (Z z ((PolyPair.proj .Z (pairOf hd g)).eval z))
      = ∑ z, uniform (Point F m) z
        * ∑ g, bornProb Φ (G.M () g) (Z z ((PolyPair.proj .Z (pairOf hd g)).eval z)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ => (Finset.mul_sum _ _ _).symm
  have hC : ∑ g, (if IsGood g then (0 : ℝ) else bornProb Φ (G.M () g) 1)
      = ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1 := by
    rw [Finset.sum_filter]
    simp only [ite_not]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC] at hsumg
  linarith

/-- **The `X` marginal**, from the order `Z_b X_a`: the mirror image. -/
theorem marg_X_ge (hd : 1 ≤ d) {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z)) {Δ δG : ℝ}
    (hprod : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - ordComb ordZX X Z u (g.eval u))) ^ 2
      ≤ Δ)
    (hbad : ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1 ≤ δG) :
    1 - 2 * Real.sqrt Δ - 2 / Fintype.card F - δG
      ≤ ∑ x, uniform (Point F m) x
          * ∑ g, bornProb Φ (G.M () g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x)) := by
  have hsa : ∀ g, (G.M () g)ᴴ = G.M () g := fun g => G.selfAdjoint () g
  have hidem : ∀ g, G.M () g * G.M () g = G.M () g := fun g => G.projective () g
  have hW0 : ∀ g, 0 ≤ bornProb Φ (G.M () g) 1 := fun g =>
    bornProb_nonneg Φ (posSemidef_of_proj (hsa g) (hidem g)) Matrix.PosSemidef.one
  have hq0 : (0 : ℝ) ≤ 2 / Fintype.card F := by positivity
  have h1 := one_sub_two_sqrt_le_sum_snorm_sq hΦ G (ordComb ordZX X Z) hprod
  have hswap : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordZX X Z u (g.eval u))) ^ 2
      = ∑ g, ∑ u, uniform (Point F (4 * m)) u * snorm Φ
        ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordZX X Z u (g.eval u))) ^ 2 := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  have hg : ∀ g, ∑ u, uniform (Point F (4 * m)) u * snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (ordComb ordZX X Z u (g.eval u))) ^ 2
      ≤ 2 / Fintype.card F * bornProb Φ (G.M () g) 1
        + ∑ x, uniform (Point F m) x
          * bornProb Φ (G.M () g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x))
        + (if IsGood g then (0 : ℝ) else bornProb Φ (G.M () g) 1) := by
    intro g
    have hM0 : 0 ≤ ∑ x, uniform (Point F m) x
        * bornProb Φ (G.M () g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x)) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (uniform_nonneg _ _)
        (bornProb_nonneg Φ (posSemidef_of_proj (hsa g) (hidem g)) ((hX x).posSemidef _))
    by_cases hgood : IsGood g
    · rw [if_pos hgood, add_zero]
      have h := sum_uniform_snorm_sq_ordComb_ZX_le_of_isLinAB hd Φ (hsa g) (hidem g) hX hZ
        (isLinAB_of_isGood hgood)
      have hre : ∀ u₀ : Point F (4 * m), bornProb Φ (G.M () g) (X (xBlk u₀) ((gA hd g).eval u₀))
          = bornProb Φ (G.M () g)
            (X (xBlk u₀) ((PolyPair.proj .X (pairOf hd g)).eval (xBlk u₀))) := fun u₀ => by
        rw [pairOf_of_isGood hd hgood, PolyPair.proj_X, eval_gX hd hgood]
      simp_rw [hre] at h
      rw [sum_uniform_xBlk (fun x => bornProb Φ (G.M () g)
        (X x ((PolyPair.proj .X (pairOf hd g)).eval x)))] at h
      exact h
    · rw [if_neg hgood]
      have hle : ∀ u : Point F (4 * m), snorm Φ ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ)
          * bOp (ordComb ordZX X Z u (g.eval u))) ^ 2 ≤ bornProb Φ (G.M () g) 1 := fun u => by
        rw [ordComb, ptComb_ordZX_eq]
        exact snorm_sq_ordComb_ordXZ_le Φ (hsa g) (hidem g) (hZ _) (hX _) _ _ _
      calc _ ≤ ∑ u, uniform (Point F (4 * m)) u * bornProb Φ (G.M () g) 1 :=
            Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hle u) (uniform_nonneg _ _)
        _ = bornProb Φ (G.M () g) 1 := by rw [← Finset.sum_mul, sum_uniform_eq_one, one_mul]
        _ ≤ _ := by nlinarith [mul_nonneg hq0 (hW0 g)]
  have hsumg := Finset.sum_le_sum fun g (_ : g ∈ univ) => hg g
  have hA : ∑ g, 2 / Fintype.card F * bornProb Φ (G.M () g) 1 = 2 / Fintype.card F := by
    rw [← Finset.mul_sum, sum_bornProb_M_one hΦ G, mul_one]
  have hB : ∑ g, ∑ x, uniform (Point F m) x
      * bornProb Φ (G.M () g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x))
      = ∑ x, uniform (Point F m) x
        * ∑ g, bornProb Φ (G.M () g) (X x ((PolyPair.proj .X (pairOf hd g)).eval x)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
  have hC : ∑ g, (if IsGood g then (0 : ℝ) else bornProb Φ (G.M () g) 1)
      = ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1 := by
    rw [Finset.sum_filter]
    simp only [ite_not]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC] at hsumg
  linarith

/-- **`lem:qld-global-sandwich`, the `Z` marginal in consistency form**: the evaluated `Z`
marginal of the completed measurement against a family `N` whose elements are the `Z z a`. -/
theorem inconsistency_evalMarg_Z_le (hd : 1 ≤ d) {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z)) (N : Point F m → POVM F RB)
    (hN : ∀ z a, ((N z).mats a).val = Z z a) {Δ δG : ℝ}
    (hprod : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - ordComb ordXZ X Z u (g.eval u))) ^ 2
      ≤ Δ)
    (hbad : ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1 ≤ δG) :
    inconsistency (uniform (Point F m)) Φ (fun z => evalMarg (pairMeas hd G) .Z z) N
      ≤ 2 * Real.sqrt Δ + 2 / Fintype.card F + δG := by
  have h := marg_Z_ge hd hΦ G hX hZ hprod hbad
  simp_rw [evalMarg_pairMeas]
  rw [inconsistency_map_eq _ (sum_uniform_eq_one _) hΦ G
    (fun z g => (PolyPair.proj .Z (pairOf hd g)).eval z) N]
  simp_rw [hN]
  linarith

/-- **`lem:qld-global-sandwich`, the `X` marginal in consistency form.** -/
theorem inconsistency_evalMarg_X_le (hd : 1 ≤ d) {Φ : RA × RB → ℂ} (hΦ : star Φ ⬝ᵥ Φ = 1)
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
      (Matrix RA RA ℂ))
    (hX : ∀ x, IsPVM (X x)) (hZ : ∀ z, IsPVM (Z z)) (N : Point F m → POVM F RB)
    (hN : ∀ x a, ((N x).mats a).val = X x a) {Δ δG : ℝ}
    (hprod : ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm Φ
      ((aOp (G.M () g) : Matrix (RA × RB) _ ℂ) * bOp (1 - ordComb ordZX X Z u (g.eval u))) ^ 2
      ≤ Δ)
    (hbad : ∑ g ∈ univ.filter (fun g => ¬ IsGood g), bornProb Φ (G.M () g) 1 ≤ δG) :
    inconsistency (uniform (Point F m)) Φ (fun x => evalMarg (pairMeas hd G) .X x) N
      ≤ 2 * Real.sqrt Δ + 2 / Fintype.card F + δG := by
  have h := marg_X_ge hd hΦ G hX hZ hprod hbad
  simp_rw [evalMarg_pairMeas]
  rw [inconsistency_map_eq _ (sum_uniform_eq_one _) hΦ G
    (fun x g => (PolyPair.proj .X (pairOf hd g)).eval x) N]
  simp_rw [hN]
  linarith

end Marginals

end MIPRE.QLD

end
