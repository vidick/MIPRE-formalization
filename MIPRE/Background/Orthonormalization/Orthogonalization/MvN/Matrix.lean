/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/MvN/Matrix.lean
-/
/-
# The block calculus of `M_n(M)` on `H^n`

Proof-side toolkit for tier T3 (`PLAN.md` §9): the amplification
`x ↦ x ⊕ ⋯ ⊕ x` of `MvN/Defs.lean`, the block entries
`X_{ij} = proj i ∘ X ∘ embed j` of an operator `X` on
`H^n = BlockSpace H (Fin n)`, their algebra (`(XY)_{ij} = ∑ₖ X_{ik} Y_{kj}`,
`(X*)_{ij} = (X_{ji})*`, `X = ∑ᵢⱼ embed i ∘ X_{ij} ∘ proj j`), and the
membership criterion `X ∈ M_n(M) ↔ ∀ i j, X_{ij} ∈ M` for the matrix algebra
`matrixAlgebra M n = (1_n ⊗ M')'`, over an arbitrary complex Hilbert space
`H`. The diagonal trace helper `∑ᵢ E((V*V)ᵢᵢ) = ∑ᵢ E((VV*)ᵢᵢ)` for a tracial
`E` on `M` is what the matrix comparison clause of the center-valued trace
(`IsCenterValuedTrace.equiv_of_eq_matrix`) consumes. No statement of the
paper is made here.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Generated
import MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.Blocks
import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Defs

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.MvN

open scoped BigOperators ComplexOrder InnerProductSpace
open FinDim CommutingRepetition.VN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Amplification `x ↦ x ⊕ ⋯ ⊕ x` -/

theorem amplify_apply_coord (n : ℕ) (x : H →L[ℂ] H) (w : BlockSpace H (Fin n)) (j : Fin n) :
    amplify n x w j = x (w j) :=
  blockProj_apply_coord _ _ _

theorem proj_amplify {n : ℕ} (x : H →L[ℂ] H) (i : Fin n) (w : BlockSpace H (Fin n)) :
    proj i (amplify n x w) = x (proj i w) := by
  rw [proj_apply, proj_apply, amplify_apply_coord]

theorem amplify_embed {n : ℕ} (x : H →L[ℂ] H) (i : Fin n) (v : H) :
    amplify n x (embed i v) = embed i (x v) := by
  ext j
  rw [amplify_apply_coord, embed_apply, embed_apply]
  split_ifs
  · rfl
  · exact map_zero x

theorem amplify_mul (n : ℕ) (x y : H →L[ℂ] H) :
    amplify n (x * y) = amplify n x * amplify n y := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  simp only [mul_apply_eq_comp, amplify_apply_coord]

theorem amplify_one (n : ℕ) : amplify n (1 : H →L[ℂ] H) = 1 := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  simp only [one_apply_eq_self, amplify_apply_coord]

theorem amplify_zero (n : ℕ) : amplify n (0 : H →L[ℂ] H) = 0 := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  simp only [zero_apply, PiLp.zero_apply, amplify_apply_coord]

theorem amplify_add (n : ℕ) (x y : H →L[ℂ] H) :
    amplify n (x + y) = amplify n x + amplify n y := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  simp only [add_apply, PiLp.add_apply, amplify_apply_coord]

theorem amplify_sub (n : ℕ) (x y : H →L[ℂ] H) :
    amplify n (x - y) = amplify n x - amplify n y := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  simp only [sub_apply, PiLp.sub_apply, amplify_apply_coord]

theorem amplify_smul (n : ℕ) (c : ℂ) (x : H →L[ℂ] H) :
    amplify n (c • x) = c • amplify n x := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  simp only [smul_apply, PiLp.smul_apply, amplify_apply_coord]

theorem amplify_sum (n : ℕ) {κ : Type*} (s : Finset κ) (x : κ → H →L[ℂ] H) :
    amplify n (∑ k ∈ s, x k) = ∑ k ∈ s, amplify n (x k) := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  rw [amplify_apply_coord, sumCLM, sumCLM, sumA]
  simp only [amplify_apply_coord]

theorem amplify_star (n : ℕ) (x : H →L[ℂ] H) : amplify n (star x) = star (amplify n x) := by
  rw [ContinuousLinearMap.star_eq_adjoint (amplify n x), ContinuousLinearMap.eq_adjoint_iff]
  intro w w'
  simp only [PiLp.inner_apply, amplify_apply_coord]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

theorem isStarProjection_amplify {n : ℕ} {p : H →L[ℂ] H} (hp : IsStarProjection p) :
    IsStarProjection (amplify n p) := by
  refine ⟨?_, ?_⟩
  · show amplify n p * amplify n p = amplify n p
    rw [← amplify_mul, hp.isIdempotentElem.eq]
  · rw [IsSelfAdjoint, ← amplify_star, hp.isSelfAdjoint.star_eq]

/-! ### Membership in `M_n(M)` as commutation with the amplified commutant -/

/-- Membership in `M_n(M)`, unfolded (`matrixAlgebra` is the centralizer of the amplified
commutant `{y ⊕ ⋯ ⊕ y | y ∈ M'}`). -/
theorem mem_matrixAlgebra_iff_mem_centralizer {M : VonNeumannAlgebra H} {n : ℕ}
    {X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)} :
    X ∈ matrixAlgebra M n ↔
      X ∈ StarSubalgebra.centralizer ℂ
        (Set.range fun y : M.commutant => amplify n (y : H →L[ℂ] H)) :=
  Iff.rfl

/-- `X ∈ M_n(M)` iff `X` commutes with the amplification of every `y ∈ M'` (the `star`
condition of the centralizer is the same one for `star y ∈ M'`). -/
theorem mem_matrixAlgebra_iff_commute {M : VonNeumannAlgebra H} {n : ℕ}
    {X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)} :
    X ∈ matrixAlgebra M n ↔ ∀ y ∈ M.commutant, amplify n y * X = X * amplify n y := by
  rw [mem_matrixAlgebra_iff_mem_centralizer, StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h y hy
    exact (h _ ⟨⟨y, hy⟩, rfl⟩).1
  · rintro h g ⟨y, rfl⟩
    exact ⟨h y y.2, by rw [← amplify_star]; exact h _ (star_mem y.2)⟩

theorem amplify_mul_eq_of_mem {M : VonNeumannAlgebra H} {n : ℕ}
    {X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)} (hX : X ∈ matrixAlgebra M n)
    {y : H →L[ℂ] H} (hy : y ∈ M.commutant) : amplify n y * X = X * amplify n y :=
  mem_matrixAlgebra_iff_commute.mp hX y hy

/-- `M ∋ x ↦ x ⊕ ⋯ ⊕ x ∈ M_n(M)`. -/
theorem amplify_mem {M : VonNeumannAlgebra H} {n : ℕ} {x : H →L[ℂ] H} (hx : x ∈ M) :
    amplify n x ∈ matrixAlgebra M n := by
  rw [mem_matrixAlgebra_iff_commute]
  intro y hy
  rw [← amplify_mul, ← amplify_mul, commutant_mul_of_mem hx hy]

/-! ### Block entries -/

omit [CompleteSpace H] in
theorem entry_apply {n : ℕ} (X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) (i j : Fin n)
    (v : H) : entry X i j v = proj i (X (embed j v)) := rfl

/-- Coordinate `i` of `X w` is `∑ⱼ X_{ij} (w j)`. -/
theorem apply_coord_eq_sum_entry {n : ℕ} (X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n))
    (w : BlockSpace H (Fin n)) (i : Fin n) : X w i = ∑ j, entry X i j (w j) := by
  conv_lhs => rw [← sum_embed_proj_apply w]
  rw [map_sum, sumA]
  rfl

/-- `X = ∑ᵢⱼ embed i ∘ X_{ij} ∘ proj j`. -/
theorem eq_sum_embed_entry_proj {n : ℕ} (X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) :
    X = ∑ i, ∑ j, embed i ∘L entry X i j ∘L proj j := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext k
  rw [apply_coord_eq_sum_entry]
  simp only [sumCLM, sumA, ContinuousLinearMap.comp_apply, embed_apply, proj_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [CompleteSpace H] in
theorem entry_zero {n : ℕ} (i j : Fin n) :
    entry (0 : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) i j = 0 := by
  ext v
  simp only [entry_apply, zero_apply, map_zero]

theorem entry_one {n : ℕ} (i j : Fin n) :
    entry (1 : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) i j = if i = j then 1 else 0 := by
  ext v
  rw [entry_apply, one_apply_eq_self, proj_embed]
  split_ifs <;> rfl

omit [CompleteSpace H] in
theorem entry_add {n : ℕ} (X Y : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) (i j : Fin n) :
    entry (X + Y) i j = entry X i j + entry Y i j := by
  ext v
  simp only [entry_apply, add_apply, map_add]

omit [CompleteSpace H] in
theorem entry_sub {n : ℕ} (X Y : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) (i j : Fin n) :
    entry (X - Y) i j = entry X i j - entry Y i j := by
  ext v
  simp only [entry_apply, sub_apply, map_sub]

omit [CompleteSpace H] in
theorem entry_smul {n : ℕ} (c : ℂ) (X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n))
    (i j : Fin n) : entry (c • X) i j = c • entry X i j := by
  ext v
  simp only [entry_apply, smul_apply, map_smul]

omit [CompleteSpace H] in
theorem entry_sum {n : ℕ} {κ : Type*} (s : Finset κ)
    (X : κ → BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) (i j : Fin n) :
    entry (∑ k ∈ s, X k) i j = ∑ k ∈ s, entry (X k) i j := by
  ext v
  rw [entry_apply, sumCLM, sumCLM, map_sum]
  rfl

/-- `(XY)_{ij} = ∑ₖ X_{ik} Y_{kj}`. -/
theorem entry_mul {n : ℕ} (X Y : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) (i j : Fin n) :
    entry (X * Y) i j = ∑ k, entry X i k * entry Y k j := by
  ext v
  rw [entry_apply, mul_apply_eq_comp, sumCLM]
  conv_lhs => rw [← sum_embed_proj_apply (Y (embed j v))]
  rw [map_sum, map_sum]
  rfl

/-- `(X*)_{ij} = (X_{ji})*`. -/
theorem entry_star {n : ℕ} (X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)) (i j : Fin n) :
    entry (star X) i j = star (entry X j i) := by
  show proj i ∘L star X ∘L embed j = star (proj j ∘L X ∘L embed i)
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, adjoint_embed, adjoint_proj,
    ContinuousLinearMap.comp_assoc]

theorem entry_amplify {n : ℕ} (x : H →L[ℂ] H) (i j : Fin n) :
    entry (amplify n x) i j = if i = j then x else 0 := by
  ext v
  rw [entry_apply, amplify_embed, proj_embed]
  split_ifs <;> rfl

theorem entry_blockProj {n : ℕ} (q : Fin n → H →L[ℂ] H) (i j : Fin n) :
    entry (blockProj q) i j = if i = j then q i else 0 := by
  ext v
  rw [entry_apply, proj_blockProj_embed]
  split_ifs <;> rfl

/-- The entries of the "column" matrix `blockMap X ∘ proj k`, with `X i` in column `k`. -/
theorem entry_blockMap_comp_proj {n : ℕ} (X : Fin n → H →L[ℂ] H) (k i j : Fin n) :
    entry (blockMap X ∘L proj k) i j = if k = j then X i else 0 := by
  ext v
  rw [entry_apply, ContinuousLinearMap.comp_apply, proj_blockMap_apply, proj_embed]
  split_ifs
  · rfl
  · exact map_zero (X i)

/-! ### The membership criterion: `X ∈ M_n(M) ↔ ∀ i j, X_{ij} ∈ M` -/

/-- The entries of an element of `M_n(M)` lie in `M`: they commute with every `y ∈ M'`
because `X` commutes with `y ⊕ ⋯ ⊕ y`. -/
theorem entry_mem {M : VonNeumannAlgebra H} {n : ℕ}
    {X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)} (hX : X ∈ matrixAlgebra M n)
    (i j : Fin n) : entry X i j ∈ M := by
  refine mem_of_commute_commutant M fun y hy => ?_
  ext v
  simp only [mul_apply_eq_comp, entry_apply]
  rw [← proj_amplify, ← mul_apply_eq_comp (amplify n y) X, amplify_mul_eq_of_mem hX hy,
    mul_apply_eq_comp, amplify_embed]

/-- An operator on `H^n` whose entries lie in `M` is in `M_n(M)`. -/
theorem mem_matrixAlgebra_of_entry {M : VonNeumannAlgebra H} {n : ℕ}
    {X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)} (h : ∀ i j, entry X i j ∈ M) :
    X ∈ matrixAlgebra M n := by
  rw [mem_matrixAlgebra_iff_commute]
  intro y hy
  refine ContinuousLinearMap.ext fun w => ?_
  ext k
  rw [mul_apply_eq_comp, mul_apply_eq_comp, amplify_apply_coord, apply_coord_eq_sum_entry,
    apply_coord_eq_sum_entry, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [amplify_apply_coord]
  have := DFunLike.congr_fun (commutant_mul_of_mem (h k l) hy) (w l)
  simpa only [mul_apply_eq_comp] using this

/-- **The membership criterion**: `X ∈ M_n(M) ↔ ∀ i j, X_{ij} ∈ M`. -/
theorem mem_matrixAlgebra_iff {M : VonNeumannAlgebra H} {n : ℕ}
    {X : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)} :
    X ∈ matrixAlgebra M n ↔ ∀ i j, entry X i j ∈ M :=
  ⟨fun hX i j => entry_mem hX i j, mem_matrixAlgebra_of_entry⟩

/-- A diagonal matrix with entries in `M` lies in `M_n(M)`. -/
theorem blockProj_mem {M : VonNeumannAlgebra H} {n : ℕ} {q : Fin n → H →L[ℂ] H}
    (hq : ∀ i, q i ∈ M) : blockProj q ∈ matrixAlgebra M n := by
  refine mem_matrixAlgebra_of_entry fun i j => ?_
  rw [entry_blockProj]
  split_ifs
  · exact hq i
  · exact zero_mem _

/-- A "column" matrix `blockMap X ∘ proj k` with entries in `M` lies in `M_n(M)`. -/
theorem blockMap_comp_proj_mem {M : VonNeumannAlgebra H} {n : ℕ} {X : Fin n → H →L[ℂ] H}
    (hX : ∀ i, X i ∈ M) (k : Fin n) : blockMap X ∘L proj k ∈ matrixAlgebra M n := by
  refine mem_matrixAlgebra_of_entry fun i j => ?_
  rw [entry_blockMap_comp_proj]
  split_ifs
  · exact hX i
  · exact zero_mem _

/-! ### `V* V` and `V V*` read blockwise -/

/-- `(V* V)_{ij} = ∑ₖ (V_{ki})* V_{kj}`. -/
theorem entry_star_mul {n : ℕ} (V : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n))
    (i j : Fin n) : entry (star V * V) i j = ∑ k, star (entry V k i) * entry V k j := by
  rw [entry_mul]
  simp only [entry_star]

/-- `(V V*)_{ij} = ∑ₖ V_{ik} (V_{jk})*`. -/
theorem entry_mul_star {n : ℕ} (V : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n))
    (i j : Fin n) : entry (V * star V) i j = ∑ k, entry V i k * star (entry V j k) := by
  rw [entry_mul]
  simp only [entry_star]

/-! ### Diagonal trace helpers -/

/-- The diagonal sum `X ↦ ∑ᵢ E(Xᵢᵢ)` of a tracial `E` on `M` is tracial on the matrices with
entries in `M`: `∑ᵢ E((XY)ᵢᵢ) = ∑ᵢ E((YX)ᵢᵢ)`. -/
theorem sum_entry_mul_eq {M : VonNeumannAlgebra H} {n : ℕ}
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) (hE : ∀ x ∈ M, ∀ y ∈ M, E (x * y) = E (y * x))
    {X Y : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)} (hX : ∀ i j, entry X i j ∈ M)
    (hY : ∀ i j, entry Y i j ∈ M) :
    ∑ i, E (entry (X * Y) i i) = ∑ i, E (entry (Y * X) i i) := by
  simp only [entry_mul, map_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => hE _ (hX i k) _ (hY k i)

/-- `∑ᵢ E((V* V)ᵢᵢ) = ∑ᵢ E((V V*)ᵢᵢ)` for a tracial `E` on `M` and `V` with entries in `M`. -/
theorem sum_entry_star_mul_self_eq {M : VonNeumannAlgebra H} {n : ℕ}
    (E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) (hE : ∀ x ∈ M, ∀ y ∈ M, E (x * y) = E (y * x))
    {V : BlockSpace H (Fin n) →L[ℂ] BlockSpace H (Fin n)} (hV : ∀ i j, entry V i j ∈ M) :
    ∑ i, E (entry (star V * V) i i) = ∑ i, E (entry (V * star V) i i) :=
  sum_entry_mul_eq E hE (fun i j => by rw [entry_star]; exact star_mem (hV j i)) hV

end Orthogonalization.MvN
