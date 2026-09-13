/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/BlockCalc.lean
-/
/-
# Block calculus on `H^n`: diagonal, single-block and column operators

Proof-side toolkit for Lemma 3.2 of the paper applied inside `M_n(M)`
(`Orthogonalization/MvN/Polar.lean`), extending the entry calculus of
`Orthogonalization/MvN/Matrix.lean` on `H^n = BlockSpace H (Fin n)`:

* extensionality by entries (`ext_entry`) and the entries of products with an
  amplification;
* the algebra of block-diagonal operators `blockProj q = ⊕ᵢ q i` (products,
  sums, adjoints, projections, positivity, order, injectivity);
* the single-block operators `single i x = e_{ii} ⊗ x` and their entries,
  products, sums and membership in `M_n(M)`, and the characterization of the
  operators supported in one block (`eq_single_of_conj`);
* the column operators `col k X = ∑ᵢ e_{ik} ⊗ X i` and the identities
  `(col k X)* (col k Y) = e_{kk} ⊗ ∑ᵢ (X i)* (Y i)`,
  `(col k X)* (e_{ii} ⊗ y) (col k X) = e_{kk} ⊗ (X i)* y (X i)`;
* square roots of block-diagonal operators (`sqrt_blockProj`, `sqrt_single`)
  and the kernel of a square root (`sqrt_mul_proj_eq_self`);
* the right and left supports of `Orthogonalization/MvN/Defs.lean`: they are
  projections, `x (rightSupport x) = x`, and they lie below every projection
  supporting `x` on the right, resp. on the left;
* the diagonal trace identity `∑ᵢ E((V*V)ᵢᵢ) = ∑ᵢ E((VV*)ᵢᵢ)` for `E` tracial on
  a corner `p M p` and `V` with entries in `p M p`.

No statement of the paper is made here.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Matrix
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.TypeIIINet

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

/- The real-algebra structure of `H^n →L[ℂ] H^n` (needed by `CFC.sqrt`) is found by instance
search only after unfolding `PiLp`, which exceeds the default heartbeat budget. -/
set_option synthInstance.maxHeartbeats 100000

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder InnerProductSpace
open FinDim

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Extensionality by entries -/

/-- Two operators on `H^n` with the same entries are equal. -/
theorem ext_entry {n : ℕ} {X Y : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)}
    (h : ∀ i j, entry X i j = entry Y i j) : X = Y := by
  calc X = ∑ i, ∑ j, embed i ∘L entry X i j ∘L proj j := eq_sum_embed_entry_proj X
    _ = ∑ i, ∑ j, embed i ∘L entry Y i j ∘L proj j := by simp only [h]
    _ = Y := (eq_sum_embed_entry_proj Y).symm

theorem entry_amplify_mul {n : ℕ} (x : H →L[ℂ] H)
    (X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) (i j : Fin n) :
    entry (amplify n x * X) i j = x * entry X i j := by
  ext v
  rw [entry_apply, mul_apply_eq_comp, proj_amplify, mul_apply_eq_comp, entry_apply]

theorem entry_mul_amplify {n : ℕ} (X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n))
    (x : H →L[ℂ] H) (i j : Fin n) : entry (X * amplify n x) i j = entry X i j * x := by
  ext v
  rw [entry_apply, mul_apply_eq_comp, amplify_embed, mul_apply_eq_comp, entry_apply]

/-- The entries of an operator `X = (1_n ⊗ p) X (1_n ⊗ p)` lie in the corner `p M p`. -/
theorem corner_entry_of_amplify {n : ℕ} {p : H →L[ℂ] H}
    {X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)}
    (h : amplify n p * X * amplify n p = X) (i j : Fin n) :
    p * entry X i j * p = entry X i j := by
  rw [← entry_amplify_mul, ← entry_mul_amplify, h]

/-! ### The algebra of block-diagonal operators -/

theorem blockProj_mul {n : ℕ} (q q' : Fin n → H →L[ℂ] H) :
    blockProj q * blockProj q' = blockProj (fun i => q i * q' i) := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  simp only [mul_apply_eq_comp, blockProj_apply_coord]

theorem blockProj_zero {n : ℕ} : blockProj (fun _ : Fin n => (0 : H →L[ℂ] H)) = 0 :=
  amplify_zero n

theorem blockProj_one {n : ℕ} : blockProj (fun _ : Fin n => (1 : H →L[ℂ] H)) = 1 :=
  amplify_one n

theorem blockProj_add {n : ℕ} (q q' : Fin n → H →L[ℂ] H) :
    blockProj (fun i => q i + q' i) = blockProj q + blockProj q' := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  simp only [add_apply, PiLp.add_apply, blockProj_apply_coord]

theorem blockProj_sub {n : ℕ} (q q' : Fin n → H →L[ℂ] H) :
    blockProj (fun i => q i - q' i) = blockProj q - blockProj q' := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  simp only [sub_apply, PiLp.sub_apply, blockProj_apply_coord]

theorem blockProj_sum {n : ℕ} {κ : Type*} (s : Finset κ) (q : κ → Fin n → H →L[ℂ] H) :
    blockProj (fun i => ∑ k ∈ s, q k i) = ∑ k ∈ s, blockProj (q k) := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  rw [blockProj_apply_coord, sumCLM, sumCLM, sumA]
  simp only [blockProj_apply_coord]

theorem blockProj_star {n : ℕ} (q : Fin n → H →L[ℂ] H) :
    star (blockProj q) = blockProj (fun i => star (q i)) := by
  symm
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro w w'
  simp only [PiLp.inner_apply, blockProj_apply_coord]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

theorem isStarProjection_blockProj {n : ℕ} {q : Fin n → H →L[ℂ] H}
    (h : ∀ i, IsStarProjection (q i)) : IsStarProjection (blockProj q) := by
  refine ⟨?_, ?_⟩
  · show blockProj q * blockProj q = blockProj q
    rw [blockProj_mul]
    congr 1
    funext i
    exact (h i).isIdempotentElem.eq
  · rw [IsSelfAdjoint, blockProj_star]
    congr 1
    funext i
    exact (h i).isSelfAdjoint.star_eq

theorem blockProj_nonneg {n : ℕ} {q : Fin n → H →L[ℂ] H} (h : ∀ i, 0 ≤ q i) :
    0 ≤ blockProj q := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff']
  refine ⟨?_, fun w => ?_⟩
  · rw [IsSelfAdjoint, blockProj_star]
    congr 1
    funext i
    exact (IsSelfAdjoint.of_nonneg (h i)).star_eq
  · simp only [PiLp.inner_apply, blockProj_apply_coord]
    exact Finset.sum_nonneg fun j _ =>
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (h j)).inner_nonneg_left _

theorem blockProj_le_blockProj {n : ℕ} {q q' : Fin n → H →L[ℂ] H} (h : ∀ i, q i ≤ q' i) :
    blockProj q ≤ blockProj q' := by
  rw [← sub_nonneg, ← blockProj_sub]
  exact blockProj_nonneg fun i => sub_nonneg.mpr (h i)

theorem blockProj_inj {n : ℕ} {q q' : Fin n → H →L[ℂ] H} (h : blockProj q = blockProj q') :
    q = q' := by
  funext i
  have := congrArg (fun X => entry X i i) h
  simpa only [entry_blockProj, if_true] using this

theorem amplify_mul_blockProj {n : ℕ} (x : H →L[ℂ] H) (q : Fin n → H →L[ℂ] H) :
    amplify n x * blockProj q = blockProj (fun i => x * q i) :=
  blockProj_mul _ _

theorem blockProj_mul_amplify {n : ℕ} (q : Fin n → H →L[ℂ] H) (x : H →L[ℂ] H) :
    blockProj q * amplify n x = blockProj (fun i => q i * x) :=
  blockProj_mul _ _

/-! ### Single-block operators `e_{ii} ⊗ x` -/

/-- The operator `e_{ii} ⊗ x` on `H^n`: `x` in the `(i, i)` block, zero elsewhere. -/
noncomputable def single {n : ℕ} (i : Fin n) (x : H →L[ℂ] H) :
    BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n) :=
  blockProj (fun j => if j = i then x else 0)

theorem single_apply_coord {n : ℕ} (i : Fin n) (x : H →L[ℂ] H) (w : BlockSpace H (Fin n))
    (j : Fin n) : single i x w j = if j = i then x (w j) else 0 := by
  show blockProj (fun j => if j = i then x else 0) w j = _
  rw [blockProj_apply_coord]
  split_ifs <;> rfl

theorem entry_single {n : ℕ} (i : Fin n) (x : H →L[ℂ] H) (j k : Fin n) :
    entry (single i x) j k = if j = i then (if k = i then x else 0) else 0 := by
  show entry (blockProj (fun j => if j = i then x else 0)) j k = _
  rw [entry_blockProj]
  by_cases hj : j = i
  · subst hj
    by_cases hk : k = j
    · subst hk
      simp
    · simp [hk, Ne.symm hk]
  · simp [hj]

theorem entry_single_same {n : ℕ} (i : Fin n) (x : H →L[ℂ] H) : entry (single i x) i i = x := by
  simp [entry_single]

theorem entry_single_diag {n : ℕ} (i : Fin n) (x : H →L[ℂ] H) (j : Fin n) :
    entry (single i x) j j = if j = i then x else 0 := by
  rw [entry_single]
  split_ifs <;> rfl

theorem single_mul_single_same {n : ℕ} (i : Fin n) (x y : H →L[ℂ] H) :
    single i x * single i y = single i (x * y) := by
  unfold single
  rw [blockProj_mul]
  congr 1
  funext j
  split_ifs
  · rfl
  · exact zero_mul _

theorem single_mul_single_ne {n : ℕ} {i j : Fin n} (h : i ≠ j) (x y : H →L[ℂ] H) :
    single i x * single j y = 0 := by
  unfold single
  rw [blockProj_mul, ← blockProj_zero]
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp [h]
  · simp [hk]

theorem single_zero {n : ℕ} (i : Fin n) : single i (0 : H →L[ℂ] H) = 0 := by
  unfold single
  simp only [ite_self]
  exact blockProj_zero

theorem single_sum {n : ℕ} {κ : Type*} (s : Finset κ) (i : Fin n) (x : κ → H →L[ℂ] H) :
    single i (∑ k ∈ s, x k) = ∑ k ∈ s, single i (x k) := by
  unfold single
  rw [← blockProj_sum]
  congr 1
  funext j
  split_ifs <;> simp

theorem single_star {n : ℕ} (i : Fin n) (x : H →L[ℂ] H) :
    star (single i x) = single i (star x) := by
  unfold single
  rw [blockProj_star]
  congr 1
  funext j
  split_ifs
  · rfl
  · exact star_zero _

theorem single_inj {n : ℕ} {i : Fin n} {x y : H →L[ℂ] H} (h : single i x = single i y) : x = y := by
  have := congrArg (fun X => entry X i i) h
  simpa only [entry_single_same] using this

theorem isStarProjection_single {n : ℕ} (i : Fin n) {x : H →L[ℂ] H} (hx : IsStarProjection x) :
    IsStarProjection (single i x) := by
  refine isStarProjection_blockProj fun j => ?_
  split_ifs
  · exact hx
  · exact IsStarProjection.zero _

theorem isStarProjection_of_single {n : ℕ} {i : Fin n} {x : H →L[ℂ] H}
    (h : IsStarProjection (single i x)) : IsStarProjection x := by
  refine ⟨?_, ?_⟩
  · have := h.isIdempotentElem.eq
    rw [single_mul_single_same] at this
    exact single_inj this
  · have := h.isSelfAdjoint.star_eq
    rw [single_star] at this
    exact single_inj this

theorem single_mem {M : VonNeumannAlgebra H} {n : ℕ} (i : Fin n) {x : H →L[ℂ] H} (hx : x ∈ M) :
    single i x ∈ matrixAlgebra M n := by
  refine blockProj_mem fun j => ?_
  split_ifs
  · exact hx
  · exact zero_mem _

theorem sum_single {n : ℕ} (q : Fin n → H →L[ℂ] H) : ∑ i, single i (q i) = blockProj q := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  rw [sumCLM, sumA, blockProj_apply_coord]
  simp only [single_apply_coord, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem single_mul_blockProj {n : ℕ} (i : Fin n) (x : H →L[ℂ] H) (q : Fin n → H →L[ℂ] H) :
    single i x * blockProj q = single i (x * q i) := by
  unfold single
  rw [blockProj_mul]
  congr 1
  funext j
  split_ifs with h
  · subst h
    rfl
  · exact zero_mul _

theorem blockProj_mul_single {n : ℕ} (q : Fin n → H →L[ℂ] H) (i : Fin n) (x : H →L[ℂ] H) :
    blockProj q * single i x = single i (q i * x) := by
  unfold single
  rw [blockProj_mul]
  congr 1
  funext j
  split_ifs with h
  · subst h
    rfl
  · exact mul_zero _

theorem single_mul_amplify {n : ℕ} (i : Fin n) (x y : H →L[ℂ] H) :
    single i x * amplify n y = single i (x * y) :=
  single_mul_blockProj i x _

theorem amplify_mul_single {n : ℕ} (y : H →L[ℂ] H) (i : Fin n) (x : H →L[ℂ] H) :
    amplify n y * single i x = single i (y * x) :=
  blockProj_mul_single _ i x

theorem entry_single_mul {n : ℕ} (i : Fin n) (y : H →L[ℂ] H)
    (X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) (j k : Fin n) :
    entry (single i y * X) j k = if j = i then y * entry X i k else 0 := by
  ext v
  rw [entry_apply, mul_apply_eq_comp, proj_apply, single_apply_coord]
  split_ifs with h
  · subst h
    rfl
  · rfl

theorem entry_mul_single {n : ℕ} (X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n))
    (i : Fin n) (y : H →L[ℂ] H) (j k : Fin n) :
    entry (X * single i y) j k = if k = i then entry X j i * y else 0 := by
  rw [entry_mul]
  simp only [entry_single, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- An operator with `X = (e_{ii} ⊗ z) X (e_{ii} ⊗ z)` has its `(i, i)` entry in the corner
`z (·) z`. -/
theorem entry_eq_conj_of_conj {n : ℕ} {i : Fin n} {z : H →L[ℂ] H}
    {X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)}
    (h : single i z * X * single i z = X) : z * entry X i i * z = entry X i i := by
  conv_rhs => rw [← h]
  rw [entry_mul_single, entry_single_mul]
  simp

/-- An operator with `X = (e_{ii} ⊗ z) X (e_{ii} ⊗ z)` is supported in the `(i, i)` block. -/
theorem eq_single_of_conj {n : ℕ} {i : Fin n} {z : H →L[ℂ] H}
    {X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)}
    (h : single i z * X * single i z = X) : X = single i (entry X i i) := by
  refine ext_entry fun j k => ?_
  conv_lhs => rw [← h]
  rw [entry_mul_single, entry_single_mul, entry_single]
  split_ifs <;> simp [entry_eq_conj_of_conj h]

/-! ### Column operators `∑ᵢ e_{ik} ⊗ X i` -/

/-- The column operator `col k X = ∑ᵢ e_{ik} ⊗ X i` on `H^n` (blocks `X i` in column `k`). -/
noncomputable def col {n : ℕ} (k : Fin n) (X : Fin n → H →L[ℂ] H) :
    BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n) :=
  blockMap X ∘L proj k

theorem entry_col {n : ℕ} (k : Fin n) (X : Fin n → H →L[ℂ] H) (i j : Fin n) :
    entry (col k X) i j = if j = k then X i else 0 := by
  rw [col, entry_blockMap_comp_proj]
  by_cases h : j = k
  · simp [h]
  · simp [h, Ne.symm h]

theorem col_mem {M : VonNeumannAlgebra H} {n : ℕ} {X : Fin n → H →L[ℂ] H} (hX : ∀ i, X i ∈ M)
    (k : Fin n) : col k X ∈ matrixAlgebra M n :=
  blockMap_comp_proj_mem hX k

/-- `(col k X)* (col k Y) = e_{kk} ⊗ ∑ᵢ (X i)* (Y i)`. -/
theorem star_col_mul_col {n : ℕ} (k : Fin n) (X Y : Fin n → H →L[ℂ] H) :
    star (col k X) * col k Y = single k (∑ i, star (X i) * Y i) := by
  refine ext_entry fun i j => ?_
  rw [entry_mul, entry_single]
  simp only [entry_star, entry_col]
  by_cases hi : i = k
  · subst hi
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  · simp [hi]

theorem col_mul_single {n : ℕ} (k : Fin n) (X : Fin n → H →L[ℂ] H) (y : H →L[ℂ] H) :
    col k X * single k y = col k (fun i => X i * y) := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  show proj j (blockMap X (proj k (single k y w))) =
    proj j (blockMap (fun i => X i * y) (proj k w))
  rw [proj_blockMap_apply, proj_blockMap_apply, proj_apply, proj_apply, single_apply_coord,
    mul_apply_eq_comp, if_pos rfl]

theorem blockProj_mul_col {n : ℕ} (q : Fin n → H →L[ℂ] H) (k : Fin n) (X : Fin n → H →L[ℂ] H) :
    blockProj q * col k X = col k (fun i => q i * X i) := by
  refine ContinuousLinearMap.ext fun w => ?_
  show blockProj q (blockMap X (proj k w)) = blockMap (fun i => q i * X i) (proj k w)
  exact blockProj_blockMap q X (proj k w)

/-- `(col k X)* (e_{ii} ⊗ y) (col k X) = e_{kk} ⊗ (X i)* y (X i)`. -/
theorem star_col_mul_single_mul_col {n : ℕ} (k : Fin n) (X : Fin n → H →L[ℂ] H) (i : Fin n)
    (y : H →L[ℂ] H) :
    star (col k X) * single i y * col k X = single k (star (X i) * y * X i) := by
  rw [mul_assoc, single, blockProj_mul_col, star_col_mul_col]
  congr 1
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    mul_assoc]

/-! ### Square roots -/

/-- The square root of a block-diagonal positive operator is block-diagonal. -/
theorem sqrt_blockProj {n : ℕ} {q : Fin n → H →L[ℂ] H} (h : ∀ i, 0 ≤ q i) :
    CFC.sqrt (blockProj q) = blockProj (fun i => CFC.sqrt (q i)) := by
  refine CFC.sqrt_unique ?_ (blockProj_nonneg fun i => CFC.sqrt_nonneg _)
  rw [blockProj_mul]
  congr 1
  funext i
  exact sqrt_mul_sqrt_self (h i)

theorem sqrt_single {n : ℕ} (i : Fin n) {y : H →L[ℂ] H} (hy : 0 ≤ y) :
    CFC.sqrt (single i y) = single i (CFC.sqrt y) := by
  have h' : ∀ j : Fin n, 0 ≤ (if j = i then y else 0) := fun j => by
    split_ifs
    · exact hy
    · exact le_rfl
  unfold single
  rw [sqrt_blockProj h']
  congr 1
  funext j
  split_ifs
  · rfl
  · exact CFC.sqrt_zero

/-- `√a ξ = 0` whenever `a ξ = 0` (`a ≥ 0`): `‖√a ξ‖² = ⟪ξ, a ξ⟫`. -/
theorem sqrt_apply_eq_zero_of {a : H →L[ℂ] H} (ha : 0 ≤ a) {ξ : H} (h : a ξ = 0) :
    CFC.sqrt a ξ = 0 := by
  have hsa : star (CFC.sqrt a) = CFC.sqrt a :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
  have h1 : ⟪CFC.sqrt a ξ, CFC.sqrt a ξ⟫_ℂ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hsa,
      ← mul_apply_eq_comp, sqrt_mul_sqrt_self ha, h, inner_zero_right]
  exact inner_self_eq_zero.mp h1

/-- If `a p = a` with `a ≥ 0` then `√a p = √a` (the kernels of `a` and `√a` agree). -/
theorem sqrt_mul_proj_eq_self {a p : H →L[ℂ] H} (ha : 0 ≤ a) (h : a * p = a) :
    CFC.sqrt a * p = CFC.sqrt a := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [mul_apply_eq_comp, ← sub_eq_zero, ← map_sub]
  refine sqrt_apply_eq_zero_of ha ?_
  rw [map_sub, ← mul_apply_eq_comp, h, sub_self]

/-! ### Right and left supports -/

theorem isStarProjection_rightSupport (x : H →L[ℂ] H) : IsStarProjection (rightSupport x) :=
  isStarProjection_starProjection

theorem isStarProjection_leftSupport (x : H →L[ℂ] H) : IsStarProjection (leftSupport x) :=
  isStarProjection_starProjection

/-- `x (rightSupport x) = x`: `1 − rightSupport x` projects onto the (closed) kernel of `x`. -/
theorem mul_rightSupport (x : H →L[ℂ] H) : x * rightSupport x = x := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [mul_apply_eq_comp]
  have h1 : v - rightSupport x v ∈ (LinearMap.ker (x : H →ₗ[ℂ] H))ᗮᗮ :=
    Submodule.sub_starProjection_mem_orthogonal v
  rw [Submodule.orthogonal_orthogonal_eq_closure,
    IsClosed.submodule_topologicalClosure_eq (ContinuousLinearMap.isClosed_ker x),
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, sub_eq_zero] at h1
  exact h1.symm

/-- The right support of `x` lies below every projection `Q` with `x Q = x`
(`Q` need not even be a projection: `x (1 − Q) = 0` puts `range (1 − Q)` inside `ker x`). -/
theorem rightSupport_mul_eq_self_of {x Q : H →L[ℂ] H} (h : x * Q = x) :
    rightSupport x * Q = rightSupport x := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [mul_apply_eq_comp, ← sub_eq_zero, ← map_sub, rightSupport,
    Submodule.starProjection_apply_eq_zero_iff]
  refine Submodule.le_orthogonal_orthogonal _ ?_
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, ← mul_apply_eq_comp, h, sub_self]

/-- The left support of `x` lies below every projection `P` with `P x = x`: the closure of
`range x` is inside the closed range of `P`. -/
theorem leftSupport_mul_eq_self_of {x P : H →L[ℂ] H} (hP : IsStarProjection P) (h : P * x = x) :
    leftSupport x * P = leftSupport x := by
  obtain ⟨_, hP'⟩ := isStarProjection_iff_eq_starProjection_range.mp hP
  have hle : (LinearMap.range (x : H →ₗ[ℂ] H)).topologicalClosure ≤
      LinearMap.range (P : H →ₗ[ℂ] H) := by
    refine Submodule.topologicalClosure_minimal _ ?_
      (ContinuousLinearMap.IsIdempotentElem.isClosed_range hP.isIdempotentElem)
    rintro _ ⟨v, rfl⟩
    exact ⟨x v, by rw [ContinuousLinearMap.coe_coe, ← mul_apply_eq_comp, h]; rfl⟩
  rw [hP']
  exact Submodule.starProjection_comp_starProjection_of_le hle

/-- `√(x* x) (rightSupport x) = √(x* x)`. -/
theorem sqrt_star_mul_self_mul_rightSupport (x : H →L[ℂ] H) :
    CFC.sqrt (star x * x) * rightSupport x = CFC.sqrt (star x * x) :=
  sqrt_mul_proj_eq_self (star_mul_self_nonneg x) (by rw [mul_assoc, mul_rightSupport])

/-! ### The diagonal trace on a corner -/

/-- `∑ᵢ E((V* V)ᵢᵢ) = ∑ᵢ E((V V*)ᵢᵢ)` for `E` tracial on the corner `p M p` and `V` with
entries in `p M p`. -/
theorem sum_entry_star_mul_self_eq_of_corner {M : VonNeumannAlgebra H} {n : ℕ} {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    (hE : ∀ x ∈ M, p * x * p = x → ∀ y ∈ M, p * y * p = y → E (x * y) = E (y * x))
    {V : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)} (hV : ∀ i j, entry V i j ∈ M)
    (hVp : ∀ i j, p * entry V i j * p = entry V i j) :
    ∑ i, E (entry (star V * V) i i) = ∑ i, E (entry (V * star V) i i) := by
  simp only [entry_star_mul, entry_mul_star, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  have hc : p * star (entry V i k) * p = star (entry V i k) := by
    conv_rhs => rw [← hVp i k]
    rw [star_mul, star_mul, hp.isSelfAdjoint.star_eq, mul_assoc]
  exact hE _ (star_mem (hV i k)) hc _ (hV i k) (hVp i k)

end Orthogonalization.MvN
