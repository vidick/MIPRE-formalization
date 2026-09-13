/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Blocks/Bicommutant.lean
-/
/-
# The bicommutant theorem and Schur's lemma in finite dimension

Proof-side machinery for tier T1b (`PLAN.md` §3, §8): for a unital `*`-subalgebra
`A` of `B(L)`, `L` a finite-dimensional Hilbert space,

* the **bicommutant theorem** `A'' = A` (`centralizer_centralizer_coe`,
  `mem_of_mem_centralizer_centralizer`), by the standard amplification argument
  on `L^n`, `n = dim L`: with `b` a basis of `L` and `Ξ := (b 1, …, b n) ∈ L^n`,
  the projection `P` onto `A Ξ` commutes with the amplification `x ⊕ ⋯ ⊕ x` of
  every `x ∈ A`, so its blocks lie in `A'`, so `P` commutes with the
  amplification of any `T ∈ A''`; since `Ξ ∈ A Ξ` this forces `T Ξ ∈ A Ξ`,
  i.e. `T = x` on the basis for some `x ∈ A`;
* **Schur's lemma** (`exists_eq_smul_one_of_mem_centralizer`): if `A` acts
  irreducibly then `A' = ℂ·1` (an eigenspace of an element of `A'` is
  `A`-invariant), hence `A = B(L)` (`eq_top_of_isIrreducible`).

No statement of the paper is made here; this file only supplies tools.
-/
import Mathlib
import MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.Blocks

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace Orthogonalization.Blocks

open scoped InnerProductSpace
open Module Orthogonalization.FinDim

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]

/-! ### Projections onto invariant subspaces -/

/-- The projection onto a subspace invariant under a `*`-closed set of operators commutes
with them (general form, for any subspace admitting an orthogonal projection). -/
theorem starProjection_commute_of_invariant' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (W : Submodule ℂ E) [W.HasOrthogonalProjection]
    {x : E →L[ℂ] E} (hx : ∀ v ∈ W, x v ∈ W) (hx' : ∀ v ∈ W, (star x) v ∈ W) :
    Commute x W.starProjection := by
  have hPsa : star W.starProjection = W.starProjection :=
    (isStarProjection_starProjection (U := W)).isSelfAdjoint.star_eq
  -- invariance of `W` under `y` reads `P y P = y P`
  have key : ∀ y : E →L[ℂ] E, (∀ v ∈ W, y v ∈ W) →
      W.starProjection * y * W.starProjection = y * W.starProjection := by
    intro y hy
    ext v
    simp only [mul_apply_eq_comp]
    exact Submodule.starProjection_eq_self_iff.mpr (hy _ (W.starProjection_apply_mem v))
  have h1 := key x hx
  -- the same for `star x`, then take adjoints: `P x P = P x`
  have h2 := congrArg star (key (star x) hx')
  rw [star_mul, star_mul, star_mul, star_star, hPsa] at h2
  show x * W.starProjection = W.starProjection * x
  rw [← h2, ← mul_assoc, h1]

/-- The projection onto a subspace invariant under a `*`-closed set of operators commutes
with them. -/
theorem starProjection_commute_of_invariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (W : Submodule ℂ E) {x : E →L[ℂ] E}
    (hx : ∀ v ∈ W, x v ∈ W) (hx' : ∀ v ∈ W, (star x) v ∈ W) : Commute x W.starProjection :=
  starProjection_commute_of_invariant' W hx hx'

/-! ### Amplification `x ↦ x ⊕ ⋯ ⊕ x` on the block space `L^ι` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- The amplification `x ⊕ ⋯ ⊕ x` of an operator `x` on `L` to `L^ι`. -/
noncomputable def ampl (x : L →L[ℂ] L) : BlockSpace L ι →L[ℂ] BlockSpace L ι :=
  blockProj fun _ : ι => x

theorem ampl_apply_coord (x : L →L[ℂ] L) (w : BlockSpace L ι) (j : ι) :
    ampl ι x w j = x (w j) :=
  blockProj_apply_coord _ _ _

theorem proj_ampl (x : L →L[ℂ] L) (k : ι) (w : BlockSpace L ι) :
    proj k (ampl ι x w) = x (proj k w) := by
  rw [proj_apply, proj_apply, ampl_apply_coord]

theorem ampl_embed (x : L →L[ℂ] L) (k : ι) (v : L) :
    ampl ι x (embed k v) = embed k (x v) := by
  ext j
  rw [ampl_apply_coord, embed_apply, embed_apply]
  split_ifs
  · rfl
  · exact map_zero x

theorem ampl_mul (x y : L →L[ℂ] L) : ampl ι (x * y) = ampl ι x * ampl ι y := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  simp only [mul_apply_eq_comp, ampl_apply_coord]

theorem ampl_one : ampl ι (1 : L →L[ℂ] L) = 1 := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  simp only [one_apply_eq_self, ampl_apply_coord]

theorem ampl_add (x y : L →L[ℂ] L) : ampl ι (x + y) = ampl ι x + ampl ι y := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  simp only [add_apply, PiLp.add_apply, ampl_apply_coord]

theorem ampl_smul (c : ℂ) (x : L →L[ℂ] L) : ampl ι (c • x) = c • ampl ι x := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext j
  simp only [smul_apply, PiLp.smul_apply, ampl_apply_coord]

theorem ampl_star (x : L →L[ℂ] L) : ampl ι (star x) = star (ampl ι x) := by
  rw [ContinuousLinearMap.star_eq_adjoint (ampl ι x), ContinuousLinearMap.eq_adjoint_iff]
  intro w w'
  simp only [PiLp.inner_apply, ampl_apply_coord]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- `x ↦ ampl ι x ξ`, as a linear map. -/
noncomputable def amplAt (ξ : BlockSpace L ι) : (L →L[ℂ] L) →ₗ[ℂ] BlockSpace L ι where
  toFun x := ampl ι x ξ
  map_add' x y := by simp only [ampl_add, add_apply]
  map_smul' c x := by simp only [ampl_smul, smul_apply, RingHom.id_apply]

theorem amplAt_apply (ξ : BlockSpace L ι) (x : L →L[ℂ] L) : amplAt ξ x = ampl ι x ξ := rfl

/-! ### Blocks of an operator on `L^ι` -/

/-- The `(k, l)` block `proj k ∘ X ∘ embed l` of an operator `X` on `L^ι`. -/
noncomputable def blockEntry (X : BlockSpace L ι →L[ℂ] BlockSpace L ι) (k l : ι) : L →L[ℂ] L :=
  proj k ∘L X ∘L embed l

omit [FiniteDimensional ℂ L] [Fintype ι] in
theorem blockEntry_apply (X : BlockSpace L ι →L[ℂ] BlockSpace L ι) (k l : ι) (v : L) :
    blockEntry X k l v = proj k (X (embed l v)) := rfl

/-- Coordinate `k` of `X w` is `∑ l, X_{kl} (w l)`. -/
theorem apply_coord_eq_sum_blockEntry (X : BlockSpace L ι →L[ℂ] BlockSpace L ι)
    (w : BlockSpace L ι) (k : ι) : X w k = ∑ l, blockEntry X k l (w l) := by
  conv_lhs => rw [← sum_embed_proj_apply w]
  rw [map_sum, sumA]
  rfl

/-- If `X` commutes with the amplification of every `y ∈ s`, its blocks lie in the
centralizer of `s`. -/
theorem blockEntry_mem_centralizer {s : Set (L →L[ℂ] L)}
    {X : BlockSpace L ι →L[ℂ] BlockSpace L ι} (hX : ∀ y ∈ s, Commute (ampl ι y) X) (k l : ι) :
    blockEntry X k l ∈ Set.centralizer s := by
  rw [Set.mem_centralizer_iff]
  intro y hy
  ext v
  simp only [mul_apply_eq_comp, blockEntry_apply]
  rw [← proj_ampl, ← mul_apply_eq_comp (ampl ι y) X, (hX y hy).eq, mul_apply_eq_comp, ampl_embed]

/-- Conversely, an operator commuting with all the blocks of `X` has its amplification
commuting with `X`. -/
theorem commute_ampl_of_blockEntry {X : BlockSpace L ι →L[ℂ] BlockSpace L ι} {T : L →L[ℂ] L}
    (h : ∀ k l, Commute T (blockEntry X k l)) : Commute (ampl ι T) X := by
  show ampl ι T * X = X * ampl ι T
  refine ContinuousLinearMap.ext fun w => ?_
  ext k
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ampl_apply_coord, apply_coord_eq_sum_blockEntry,
    apply_coord_eq_sum_blockEntry, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ampl_apply_coord]
  have := DFunLike.congr_fun (h k l).eq (w l)
  simpa only [mul_apply_eq_comp] using this

/-! ### The bicommutant theorem -/

/-- The bicommutant theorem, for an arbitrary finite basis `b` of `L`. -/
theorem mem_of_mem_centralizer_centralizer_aux (A : StarSubalgebra ℂ (L →L[ℂ] L))
    (b : Basis ι ℂ L) {T : L →L[ℂ] L}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (L →L[ℂ] L)))) : T ∈ A := by
  -- the vector `Ξ = (b k)_k ∈ L^ι`
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : BlockSpace L ι, Ξ = ∑ k, embed k (b k) := ⟨_, rfl⟩
  have hΞk : ∀ k, proj k Ξ = b k := by
    intro k
    rw [hΞ, proj_apply, sumA]
    simp only [embed_apply]
    rw [Finset.sum_ite_eq]
    simp
  -- the subspace `W = A Ξ`
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ (BlockSpace L ι),
      W = (Subalgebra.toSubmodule A.toSubalgebra).map (amplAt Ξ) := ⟨_, rfl⟩
  have hWmem : ∀ x ∈ A, ampl ι x Ξ ∈ W := by
    intro x hx
    rw [hW, Submodule.mem_map]
    exact ⟨x, by simpa using hx, rfl⟩
  have hWex : ∀ v ∈ W, ∃ x ∈ A, ampl ι x Ξ = v := by
    intro v hv
    rw [hW, Submodule.mem_map] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨x, by simpa using hx, rfl⟩
  have hinv : ∀ y ∈ A, ∀ v ∈ W, ampl ι y v ∈ W := by
    intro y hy v hv
    obtain ⟨x, hx, rfl⟩ := hWex v hv
    rw [← mul_apply_eq_comp (ampl ι y) (ampl ι x), ← ampl_mul]
    exact hWmem _ (mul_mem hy hx)
  -- the projection onto `W` commutes with the amplified `A`, hence with `ampl T`
  have hcomm : ∀ y ∈ (A : Set (L →L[ℂ] L)), Commute (ampl ι y) W.starProjection := fun y hy =>
    starProjection_commute_of_invariant W (hinv y hy)
      (by rw [← ampl_star]; exact hinv _ (star_mem hy))
  have hTP : Commute (ampl ι T) W.starProjection :=
    commute_ampl_of_blockEntry fun k l =>
      (Set.mem_centralizer_iff.mp hT _ (blockEntry_mem_centralizer hcomm k l)).symm
  -- `Ξ ∈ W`, so `ampl T Ξ = ampl T (P Ξ) = P (ampl T Ξ) ∈ W`
  have hΞW : Ξ ∈ W := by
    have := hWmem 1 (one_mem A)
    rwa [ampl_one, one_apply_eq_self] at this
  have hTΞ : ampl ι T Ξ ∈ W := by
    have h1 : W.starProjection Ξ = Ξ := Submodule.starProjection_eq_self_iff.mpr hΞW
    have : ampl ι T Ξ = W.starProjection (ampl ι T Ξ) := by
      conv_lhs => rw [← h1]
      rw [← mul_apply_eq_comp (ampl ι T) W.starProjection Ξ,
        ← mul_apply_eq_comp W.starProjection (ampl ι T) Ξ, hTP.eq]
    rw [this]
    exact W.starProjection_apply_mem _
  obtain ⟨x, hx, hxT⟩ := hWex _ hTΞ
  -- read off the coordinates: `x (b k) = T (b k)` for all `k`, so `T = x`
  have hcoord : ∀ k, x (b k) = T (b k) := by
    intro k
    have := congrArg (proj k) hxT
    rwa [proj_ampl, proj_ampl, hΞk] at this
  have hTx : T = x := by
    apply ContinuousLinearMap.coe_injective
    refine b.ext fun k => ?_
    simp only [ContinuousLinearMap.coe_coe]
    exact (hcoord k).symm
  rw [hTx]
  exact hx

/-- **Bicommutant theorem** (membership form): `A'' ⊆ A` for a unital `*`-subalgebra `A`
of `B(L)`, `L` finite-dimensional. -/
theorem mem_of_mem_centralizer_centralizer (A : StarSubalgebra ℂ (L →L[ℂ] L)) {T : L →L[ℂ] L}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (L →L[ℂ] L)))) : T ∈ A :=
  mem_of_mem_centralizer_centralizer_aux A (stdOrthonormalBasis ℂ L).toBasis hT

/-- **Bicommutant theorem**: `A'' = A` for a unital `*`-subalgebra `A` of `B(L)`, `L`
finite-dimensional. -/
theorem centralizer_centralizer_coe (A : StarSubalgebra ℂ (L →L[ℂ] L)) :
    Set.centralizer (Set.centralizer (A : Set (L →L[ℂ] L))) = (A : Set (L →L[ℂ] L)) :=
  Set.Subset.antisymm (fun _ hT => mem_of_mem_centralizer_centralizer A hT)
    Set.subset_centralizer_centralizer

/-! ### Schur's lemma -/

/-- `A` acts irreducibly on `L`: every `A`-invariant subspace is trivial. -/
def IsIrreducible (A : StarSubalgebra ℂ (L →L[ℂ] L)) : Prop :=
  ∀ W : Submodule ℂ L, (∀ x ∈ A, ∀ v ∈ W, x v ∈ W) → W = ⊥ ∨ W = ⊤

/-- Every operator on a nontrivial finite-dimensional complex space has an eigenvalue. -/
theorem exists_hasEigenvalue [Nontrivial L] (S : L →L[ℂ] L) :
    ∃ c : ℂ, Module.End.HasEigenvalue (S : L →ₗ[ℂ] L) c :=
  Module.End.exists_eigenvalue _

/-- The centralizer of a `*`-subalgebra is closed under `star`. -/
theorem star_mem_centralizer (A : StarSubalgebra ℂ (L →L[ℂ] L)) {S : L →L[ℂ] L}
    (hS : S ∈ Set.centralizer (A : Set (L →L[ℂ] L))) :
    star S ∈ Set.centralizer (A : Set (L →L[ℂ] L)) := by
  rw [Set.mem_centralizer_iff] at hS ⊢
  intro y hy
  have := congrArg star (hS (star y) (star_mem hy))
  rwa [star_mul, star_mul, star_star, eq_comm] at this

/-- **Schur's lemma**: the commutant of an irreducible `*`-subalgebra is `ℂ·1`. -/
theorem exists_eq_smul_one_of_mem_centralizer (A : StarSubalgebra ℂ (L →L[ℂ] L))
    (hA : IsIrreducible A) {S : L →L[ℂ] L} (hS : S ∈ Set.centralizer (A : Set (L →L[ℂ] L))) :
    ∃ c : ℂ, S = c • (1 : L →L[ℂ] L) := by
  rcases subsingleton_or_nontrivial L with hL | hL
  · exact ⟨0, ContinuousLinearMap.ext fun v => Subsingleton.elim _ _⟩
  obtain ⟨c, hc⟩ := exists_hasEigenvalue S
  refine ⟨c, ?_⟩
  -- the eigenspace of `S` for `c` is nonzero and `A`-invariant, hence everything
  have hWne : Module.End.eigenspace (S : L →ₗ[ℂ] L) c ≠ ⊥ := Module.End.hasEigenvalue_iff.mp hc
  have hinv : ∀ x ∈ A, ∀ v ∈ Module.End.eigenspace (S : L →ₗ[ℂ] L) c,
      x v ∈ Module.End.eigenspace (S : L →ₗ[ℂ] L) c := by
    intro x hx v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    change S v = c • v at hv
    change S (x v) = c • x v
    rw [← mul_apply_eq_comp S x, ← Set.mem_centralizer_iff.mp hS x hx, mul_apply_eq_comp, hv,
      map_smul]
  rcases hA _ hinv with h | h
  · exact absurd h hWne
  ext v
  have hv : v ∈ Module.End.eigenspace (S : L →ₗ[ℂ] L) c := by
    rw [h]; exact Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hv
  change S v = c • v at hv
  rw [hv, smul_apply, one_apply_eq_self]

/-! ### Irreducible `*`-subalgebras are everything -/

/-- An irreducible `*`-subalgebra of `B(L)` contains every operator. -/
theorem mem_of_isIrreducible (A : StarSubalgebra ℂ (L →L[ℂ] L)) (hA : IsIrreducible A)
    (T : L →L[ℂ] L) : T ∈ A := by
  apply mem_of_mem_centralizer_centralizer A
  rw [Set.mem_centralizer_iff]
  intro S hS
  obtain ⟨c, rfl⟩ := exists_eq_smul_one_of_mem_centralizer A hA hS
  rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- An irreducible `*`-subalgebra of `B(L)` is all of `B(L)`. -/
theorem eq_top_of_isIrreducible (A : StarSubalgebra ℂ (L →L[ℂ] L)) (hA : IsIrreducible A) :
    A = ⊤ :=
  eq_top_iff.mpr fun T _ => mem_of_isIrreducible A hA T

end Orthogonalization.Blocks
