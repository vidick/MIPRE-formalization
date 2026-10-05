/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Repeat.Game
public import MIPRE.Foundations.TensorFamily
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import MIPRE.Tactics

@[expose] public section

/-!
# Tensor powers of permutation strategies

Paper II, Claim II:3043 and the completeness half of `thm:repetition` (II:11103), in the
direct form of the plan (`planning/aldous-lyons-track.md`, Phase 2): a perfect Z-aligned
permutation strategy commuting along edges for a tailored game `G` gives one for the product
`G.repeat k`, its `k`-th tensor power.

* `slot i : Matrix ι ι ℂ →ₐ[ℂ] Matrix (Fin k → ι) (Fin k → ι) ℂ`, `M ↦ 1 ⊗ ⋯ ⊗ M ⊗ ⋯ ⊗ 1`
  with `M` in the `i`-th factor, an algebra map; on `ℂ^{m^k}` after reindexing, `slotE`. It
  sends signed permutation matrices to signed permutation matrices (`isSignedPerm_slot`, the
  Kronecker closure of Claim II:3043 in the form needed here) and diagonal matrices to diagonal
  ones; the images of two different slots commute (`commute_slot_slot`); and the product of the
  slots of a family is its tensor product (`prod_slot_finRange`).
* `PermStrategy.repeat S k`: the observable of the variable `(i, v)` of `x⃗` (`varEquiv`) is
  `slotE i (S.U xᵢ v)`. Its measurement at `x⃗` is the tensor product of the coordinates'
  measurements (`proj_repeat`), the factors of the Fourier transform commuting and being
  regrouped by coordinate.
* `PermStrategy.proj_mul_eq_zero_of_value_eq_one`: in a perfect permutation strategy, a
  rejected pair of answers to an edge is never produced, `P^x_a P^y_b = 0`.
* `value_repeat_eq_one`: the tensor power of a perfect strategy is perfect.
* `PermStrategy.comap`: a permutation strategy pulled back along a map of questions that
  preserves the lengths, the edges and the acceptance on the edges; at questions where the
  lengths differ, which carry no edge, the observables are the identity. With it,
  `HasPerfectZPC.repeat_doubled`: a perfect strategy for the doubled game gives one for the
  doubled product, which is the form `TailoredVerifier.HasPerfectZPC` reads.
-/

namespace MIPRE.Tailored

open Matrix Finset
open scoped ComplexOrder

/-! ## Slot embeddings -/

section Slot

variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The entries of `1 ⊗ ⋯ ⊗ M ⊗ ⋯ ⊗ 1`. -/
theorem tensorFamily_update_apply (i : Fin k) (M : Matrix ι ι ℂ) (v w : Fin k → ι) :
    tensorFamily (Function.update (fun _ => (1 : Matrix ι ι ℂ)) i M) v w =
      M (v i) (w i) * ∏ j ∈ univ \ {i}, (1 : Matrix ι ι ℂ) (v j) (w j) := by
  rw [tensorFamily_apply]
  have : (fun j => Function.update (fun _ => (1 : Matrix ι ι ℂ)) i M j (v j) (w j)) =
      Function.update (fun j => (1 : Matrix ι ι ℂ) (v j) (w j)) i (M (v i) (w i)) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [this, Finset.prod_update_of_mem (Finset.mem_univ i)]

/-- **The slot embedding** `M ↦ 1 ⊗ ⋯ ⊗ M ⊗ ⋯ ⊗ 1`, `M` in the factor `i`: an algebra map. -/
noncomputable def slot (i : Fin k) : Matrix ι ι ℂ →ₐ[ℂ] Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  AlgHom.ofLinearMap
    { toFun := fun M => tensorFamily (Function.update (fun _ => 1) i M)
      map_add' := fun A B => by
        ext v w
        simp only [Matrix.add_apply, tensorFamily_update_apply, add_mul]
      map_smul' := fun c A => by
        ext v w
        simp only [Matrix.smul_apply, tensorFamily_update_apply, smul_eq_mul, RingHom.id_apply,
          mul_assoc] }
    (by
      change tensorFamily (Function.update (fun _ => (1 : Matrix ι ι ℂ)) i 1) = 1
      rw [Function.update_eq_self_iff.2 rfl]
      exact tensorFamily_one)
    (fun A B => by
      change tensorFamily (Function.update (fun _ => (1 : Matrix ι ι ℂ)) i (A * B)) =
        tensorFamily (Function.update (fun _ => 1) i A) *
          tensorFamily (Function.update (fun _ => 1) i B)
      rw [tensorFamily_mul]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj])

theorem slot_apply (i : Fin k) (M : Matrix ι ι ℂ) :
    slot i M = tensorFamily (Function.update (fun _ => 1) i M) := rfl

/-- The images of two different slots commute. -/
theorem commute_slot_slot {i j : Fin k} (hij : i ≠ j) (A B : Matrix ι ι ℂ) :
    Commute (slot i A) (slot j B) := by
  change tensorFamily _ * tensorFamily _ = tensorFamily _ * tensorFamily _
  rw [tensorFamily_mul, tensorFamily_mul]
  congr 1
  funext l
  by_cases hli : l = i
  · subst hli; simp [Function.update_of_ne hij]
  · by_cases hlj : l = j
    · subst hlj; simp [Function.update_of_ne hli]
    · simp [Function.update_of_ne hli, Function.update_of_ne hlj]

/-- A product of slots, one per coordinate of a duplicate-free list. -/
theorem prod_slot_of_nodup (P : Fin k → Matrix ι ι ℂ) :
    ∀ l : List (Fin k), l.Nodup →
      (l.map fun i => slot i (P i)).prod = tensorFamily fun j => if j ∈ l then P j else 1
  | [], _ => by simp [tensorFamily_one]
  | i :: l, hl => by
    rw [List.map_cons, List.prod_cons, prod_slot_of_nodup P l (List.nodup_cons.1 hl).2,
      slot_apply, tensorFamily_mul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp [(List.nodup_cons.1 hl).1]
    · simp [hj]

/-- **The product of the slots of a family, in order, is its tensor product.** -/
theorem prod_slot_finRange (P : Fin k → Matrix ι ι ℂ) :
    ((List.finRange k).map fun i => slot i (P i)).prod = tensorFamily P := by
  rw [prod_slot_of_nodup P _ (List.nodup_finRange k)]
  simp

omit [Fintype ι] [DecidableEq ι] in
/-- A tensor product with a zero factor is zero. -/
theorem tensorFamily_eq_zero {P : Fin k → Matrix ι ι ℂ} {i : Fin k} (h : P i = 0) :
    tensorFamily P = 0 := by
  ext v w
  rw [tensorFamily_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])

/-- **A slot of a signed permutation matrix is a signed permutation matrix.** -/
theorem isSignedPerm_slot (i : Fin k) {M : Matrix ι ι ℂ} (hM : IsSignedPerm M) :
    IsSignedPerm (slot i M) := by
  obtain ⟨σ, s, rfl⟩ := hM
  refine ⟨Equiv.piCongrRight (Function.update (fun _ => Equiv.refl ι) i σ),
    fun w => s (w i), ?_⟩
  ext v w
  rw [slot_apply, tensorFamily_update_apply, signedPermMatrix_apply, signedPermMatrix_apply]
  simp only [Matrix.one_apply]
  rw [Finset.prod_boole]
  have key : (Equiv.piCongrRight (Function.update (fun _ => Equiv.refl ι) i σ)) w = v ↔
      σ (w i) = v i ∧ ∀ j ∈ univ \ {i}, v j = w j := by
    rw [funext_iff]
    constructor
    · intro h
      refine ⟨by simpa using h i, fun j hj => ?_⟩
      have hji : j ≠ i := by simpa using hj
      simpa [Function.update_of_ne hji] using (h j).symm
    · rintro ⟨h1, h2⟩ j
      by_cases hji : j = i
      · subst hji; simpa using h1
      · simpa [Function.update_of_ne hji] using (h2 j (by simpa using hji)).symm
  by_cases h1 : σ (w i) = v i <;> by_cases h2 : ∀ j ∈ univ \ {i}, v j = w j <;>
    simp [h1, key]

/-- **A slot of a diagonal matrix is diagonal.** -/
theorem isDiag_slot (i : Fin k) {M : Matrix ι ι ℂ} (hM : M.IsDiag) : (slot i M).IsDiag := by
  intro v w hvw
  rw [slot_apply, tensorFamily_update_apply]
  by_cases hi : v i = w i
  · obtain ⟨j, hj⟩ : ∃ j, v j ≠ w j := Function.ne_iff.1 hvw
    have hji : j ≠ i := fun h => hj (h ▸ hi)
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := j) (by simpa using hji) (by simp [hj]))
  · exact mul_eq_zero_of_left (hM hi) _

/-- The reindexing of `ℂ^{Fin k → Fin m}` as `ℂ^{m^k}`. -/
noncomputable def powEquiv (m k : ℕ) : (Fin k → Fin m) ≃ Fin (m ^ k) :=
  Fintype.equivFinOfCardEq (by simp)

/-- Reindexing a square matrix is the algebra equivalence `reindexAlgEquiv`. -/
theorem reindex_eq_reindexAlgEquiv {κ κ' : Type*} [Fintype κ] [Fintype κ'] [DecidableEq κ]
    [DecidableEq κ'] (e : κ ≃ κ') (M : Matrix κ κ ℂ) :
    Matrix.reindex e e M = Matrix.reindexAlgEquiv ℂ ℂ e M := by
  rw [Matrix.coe_reindexAlgEquiv]

/-- The slot embedding into the matrices on `ℂ^{m^k}`. -/
noncomputable def slotE (m : ℕ) (i : Fin k) : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ]
    Matrix (Fin (m ^ k)) (Fin (m ^ k)) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (powEquiv m k)).toAlgHom.comp (slot i)

theorem slotE_apply (m : ℕ) (i : Fin k) (M : Matrix (Fin m) (Fin m) ℂ) :
    slotE m i M = Matrix.reindex (powEquiv m k) (powEquiv m k) (slot i M) := rfl

theorem isSignedPerm_slotE {m : ℕ} (i : Fin k) {M : Matrix (Fin m) (Fin m) ℂ}
    (hM : IsSignedPerm M) : IsSignedPerm (slotE m i M) :=
  (isSignedPerm_slot i hM).reindex _

theorem isDiag_slotE {m : ℕ} (i : Fin k) {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsDiag) :
    (slotE m i M).IsDiag := by
  rw [slotE_apply, Matrix.reindex_apply]
  exact (isDiag_slot i hM).submatrix (powEquiv m k).symm.injective

theorem commute_slotE_slotE {m : ℕ} {i j : Fin k} (hij : i ≠ j)
    (A B : Matrix (Fin m) (Fin m) ℂ) : Commute (slotE m i A) (slotE m j B) :=
  (commute_slot_slot hij A B).map (Matrix.reindexAlgEquiv ℂ ℂ (powEquiv m k))

theorem commute_slotE {m : ℕ} (i : Fin k) {A B : Matrix (Fin m) (Fin m) ℂ}
    (h : Commute A B) : Commute (slotE m i A) (slotE m i B) :=
  h.map _

/-- Slots in two coordinates of commuting matrices commute, whether the coordinates agree or
not. -/
theorem commute_slotE_of {m : ℕ} {i j : Fin k} {A B : Matrix (Fin m) (Fin m) ℂ}
    (h : i = j → Commute A B) : Commute (slotE m i A) (slotE m j B) := by
  by_cases hij : i = j
  · subst hij; exact commute_slotE i (h rfl)
  · exact commute_slotE_slotE hij A B

/-- The factors of a Fourier transform pass through an algebra map. -/
theorem fourierFactor_map {R S : Type*} [Ring R] [Algebra ℂ R] [Ring S] [Algebra ℂ S]
    (φ : R →ₐ[ℂ] S) (u : R) (b : Bool) : fourierFactor (φ u) b = φ (fourierFactor u b) := by
  simp [fourierFactor, map_smul, map_add, map_one]

end Slot

/-! ## Perfect permutation strategies produce only accepted answers -/

variable {X : Type*} [Fintype X]

namespace PermStrategy

variable {G : TailoredGame X} (S : PermStrategy G)

/-- On an edge, `P^x_a P^y_b` is its own `Xᴴ X`: the two projections commute. -/
theorem proj_mul_eq_conjTranspose_mul {x y : X} (hxy : 0 < G.μ x y)
    (a : Fin (G.len x) → Bool) (b : Fin (G.len y) → Bool) :
    S.proj x a * S.proj y b = (S.proj x a * S.proj y b)ᴴ * (S.proj x a * S.proj y b) := by
  have hP := S.isPVMIn_proj x
  have hQ := S.isPVMIn_proj y
  have hc := S.commute_proj hxy a b
  rw [conjTranspose_mul, ← star_eq_conjTranspose, ← star_eq_conjTranspose, hP.star_eq,
    hQ.star_eq]
  symm
  calc S.proj y b * S.proj x a * (S.proj x a * S.proj y b)
      = S.proj y b * (S.proj x a * S.proj x a) * S.proj y b := by simp only [mul_assoc]
    _ = S.proj y b * (S.proj x a * S.proj y b) := by rw [hP.idem, mul_assoc]
    _ = S.proj y b * (S.proj y b * S.proj x a) := by rw [hc.eq]
    _ = S.proj x a * S.proj y b := by rw [← mul_assoc, hQ.idem, hc.eq]

/-- On an edge, the probability of a pair of answers is nonnegative. -/
theorem trace_proj_mul_nonneg {x y : X} (hxy : 0 < G.μ x y)
    (a : Fin (G.len x) → Bool) (b : Fin (G.len y) → Bool) :
    0 ≤ (S.proj x a * S.proj y b).trace.re := by
  rw [S.proj_mul_eq_conjTranspose_mul hxy a b]
  exact (Complex.nonneg_iff.1 (posSemidef_conjTranspose_mul_self _).trace_nonneg).1

/-- **A perfect permutation strategy never produces a rejected pair of answers on an edge.** -/
theorem proj_mul_eq_zero_of_value_eq_one (hS : S.value = 1) {x y : X} (hxy : 0 < G.μ x y)
    {a : Fin (G.len x) → Bool} {b : Fin (G.len y) → Bool}
    (hrej : ¬G.Accepts x y (List.ofFn a) (List.ofFn b)) : S.proj x a * S.proj y b = 0 := by
  classical
  set w : (x : X) → (y : X) → (Fin (G.len x) → Bool) → (Fin (G.len y) → Bool) → ℝ :=
    fun x y a b => (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) with hw
  have hm : (0 : ℝ) < S.m := by exact_mod_cast S.m_pos
  have hw0 : ∀ x y, 0 < G.μ x y → ∀ a b, 0 ≤ w x y a b :=
    fun x y h a b => div_nonneg (S.trace_proj_mul_nonneg h a b) hm.le
  -- the rejected mass at each question pair
  set rej : X → X → ℝ := fun x y => ∑ a, ∑ b,
    (if G.Accepts x y (List.ofFn a) (List.ofFn b) then 0 else 1) * w x y a b with hrejdef
  have hsplit : ∀ x y, ∑ a, ∑ b,
      (if G.Accepts x y (List.ofFn a) (List.ofFn b) then (1 : ℝ) else 0) * w x y a b =
        1 - rej x y := by
    intro x y
    have h1 : ∑ a, ∑ b, w x y a b = 1 := S.sum_trace_proj_mul x y
    have e : ∑ a, ∑ b,
        (if G.Accepts x y (List.ofFn a) (List.ofFn b) then (1 : ℝ) else 0) * w x y a b =
          ∑ a, ∑ b, w x y a b - rej x y := by
      simp only [hrejdef]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> ring
    rw [e, h1]
  have hval : S.value = ∑ x, ∑ y, G.μ x y * (1 - rej x y) := by
    unfold value
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [← hsplit, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hw]
    ring
  have hrej0 : ∀ x y, 0 < G.μ x y → 0 ≤ rej x y := fun x y h =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      mul_nonneg (by split_ifs <;> norm_num) (hw0 x y h a b)
  -- `∑ μ · rej = 0`, a sum of nonnegative terms
  have htot : ∑ x, ∑ y, G.μ x y * rej x y = 0 := by
    have h1 : ∑ x, ∑ y, G.μ x y * (1 - rej x y) = 1 := hval ▸ hS
    have h2 : ∑ x, ∑ y, G.μ x y * (1 - rej x y) =
        ∑ x, ∑ y, G.μ x y - ∑ x, ∑ y, G.μ x y * rej x y := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [h2, G.μ_sum_one] at h1
    linarith
  have hterm0 : ∀ x y, 0 ≤ G.μ x y * rej x y := by
    intro x y
    rcases (G.μ_nonneg x y).lt_or_eq with h | h
    · exact mul_nonneg h.le (hrej0 x y h)
    · rw [← h, zero_mul]
  have hxy0 : G.μ x y * rej x y = 0 := by
    have hx := (Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
      Finset.sum_nonneg fun y _ => hterm0 x y).1 htot x (Finset.mem_univ x)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hterm0 x y).1 hx y (Finset.mem_univ y)
  have hrejxy : rej x y = 0 := (mul_eq_zero.1 hxy0).resolve_left hxy.ne'
  -- the rejected pair has probability zero
  have hwab : w x y a b = 0 := by
    have hterm : ∀ a' b', 0 ≤ (if G.Accepts x y (List.ofFn a') (List.ofFn b') then (0 : ℝ) else 1) *
        w x y a' b' := fun a' b' => mul_nonneg (by split_ifs <;> norm_num) (hw0 x y hxy a' b')
    have ha := (Finset.sum_eq_zero_iff_of_nonneg fun a' _ =>
      Finset.sum_nonneg fun b' _ => hterm a' b').1 hrejxy a (Finset.mem_univ a)
    have hab := (Finset.sum_eq_zero_iff_of_nonneg fun b' _ => hterm a b').1 ha b
      (Finset.mem_univ b)
    simpa [hrej] using hab
  have htr : (S.proj x a * S.proj y b).trace.re = 0 := by
    have := hwab
    simp only [hw, div_eq_zero_iff] at this
    exact this.resolve_right hm.ne'
  -- a positive semidefinite matrix of trace zero is zero
  rw [S.proj_mul_eq_conjTranspose_mul hxy a b] at htr ⊢
  have hnn := (posSemidef_conjTranspose_mul_self (S.proj x a * S.proj y b)).trace_nonneg
  have him : ((S.proj x a * S.proj y b)ᴴ * (S.proj x a * S.proj y b)).trace.im = 0 :=
    ((Complex.nonneg_iff.1 hnn).2).symm
  have h0 : ((S.proj x a * S.proj y b)ᴴ * (S.proj x a * S.proj y b)).trace = 0 :=
    Complex.ext htr him
  rw [trace_conjTranspose_mul_self_eq_zero_iff.1 h0, mul_zero]

end PermStrategy

/-! ## The tensor power of a permutation strategy -/

namespace TailoredGame

variable (G : TailoredGame X) {k : ℕ}

/-- An edge of the product is an edge in every coordinate. -/
theorem pos_of_repeat_pos {x y : Fin k → X} (h : 0 < (G.repeat k).μ x y) (i : Fin k) :
    0 < G.μ (x i) (y i) := by
  rcases (G.μ_nonneg (x i) (y i)).lt_or_eq with hi | hi
  · exact hi
  · rw [repeat_μ, Finset.prod_eq_zero (Finset.mem_univ i) hi.symm] at h
    exact absurd h (lt_irrefl 0)

end TailoredGame

/-- **The `k`-th tensor power of a permutation strategy**, for the product game: the observable
of the variable `(i, v)` of `x⃗` is `S.U xᵢ v` in the `i`-th tensor factor. -/
noncomputable def PermStrategy.repeat {G : TailoredGame X} (S : PermStrategy G) (k : ℕ) :
    PermStrategy (G.repeat k) where
  m := S.m ^ k
  m_pos := pow_pos S.m_pos k
  U x g := slotE S.m ((G.varEquiv x) g).1 (S.U (x ((G.varEquiv x) g).1) ((G.varEquiv x) g).2)
  signedPerm x g := isSignedPerm_slotE _ (S.signedPerm _ _)
  invol x g := by rw [← map_mul, S.invol, map_one]
  comm x g h := (commute_slotE_of fun hij => by
    obtain ⟨⟨i, v⟩, rfl⟩ := (G.varEquiv x).symm.surjective g
    obtain ⟨⟨j, w⟩, rfl⟩ := (G.varEquiv x).symm.surjective h
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hij ⊢
    subst hij
    exact S.comm _ _ _).eq
  zAligned x g hg := by
    have := (G.lt_lenRSum_iff x g).1 hg
    exact isDiag_slotE _ (S.zAligned _ _ this)
  commEdges x y hxy g h := (commute_slotE_of fun hij => by
    obtain ⟨⟨i, v⟩, rfl⟩ := (G.varEquiv x).symm.surjective g
    obtain ⟨⟨j, w⟩, rfl⟩ := (G.varEquiv y).symm.surjective h
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hij ⊢
    subst hij
    exact S.commEdges _ _ (G.pos_of_repeat_pos hxy i) _ _).eq

namespace PermStrategy

variable {G : TailoredGame X} (S : PermStrategy G) (k : ℕ)

/-- The tensor product of the coordinates' measurements, on `ℂ^{m^k}`. -/
noncomputable def tensorProj (x : Fin k → X)
    (a : (i : Fin k) → Fin (G.len (x i)) → Bool) : Matrix (Fin (S.m ^ k)) (Fin (S.m ^ k)) ℂ :=
  Matrix.reindex (powEquiv S.m k) (powEquiv S.m k) (tensorFamily fun i => S.proj (x i) (a i))

/-- The variables of `x⃗` regrouped by coordinate: a permutation of all of them. -/
theorem finRange_perm_flatMap (x : Fin k → X) :
    (List.finRange (G.lenRSum x + G.lenLSum x)).Perm
      ((List.finRange k).flatMap fun i =>
        (List.finRange (G.len (x i))).map fun v => (G.varEquiv x).symm ⟨i, v⟩) := by
  rw [List.perm_ext_iff_of_nodup (List.nodup_finRange _)]
  · intro g
    simp only [List.mem_finRange, List.mem_flatMap, List.mem_map, true_and, true_iff]
    exact ⟨((G.varEquiv x) g).1, ((G.varEquiv x) g).2, by simp⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun i _ => (List.nodup_finRange _).map fun v w h => ?_, ?_⟩
    · have := congrArg (G.varEquiv x) h
      simp only [Equiv.apply_symm_apply, Sigma.mk.injEq, heq_eq_eq, true_and] at this
      exact this
    · refine (List.nodup_finRange k).pairwise_of_forall_ne fun i _ j _ hij => ?_
      rw [Function.onFun, List.disjoint_left]
      intro g hg hg'
      simp only [List.mem_map, List.mem_finRange, true_and] at hg hg'
      obtain ⟨v, rfl⟩ := hg
      obtain ⟨w, hw⟩ := hg'
      have := congrArg (fun g => ((G.varEquiv x) g).1) hw
      simp only [Equiv.apply_symm_apply] at this
      exact hij this.symm

/-- **The measurement of the tensor power is the tensor product of the coordinates'
measurements.** -/
theorem proj_repeat (x : Fin k → X) (a : Fin (G.lenRSum x + G.lenLSum x) → Bool) :
    (S.repeat k).proj x a =
      S.tensorProj k x fun i v => a ((G.varEquiv x).symm ⟨i, v⟩) := by
  set F : Fin (G.lenRSum x + G.lenLSum x) → Matrix (Fin (S.m ^ k)) (Fin (S.m ^ k)) ℂ :=
    fun g => fourierFactor ((S.repeat k).U x g) (a g) with hF
  have hF' : ∀ p : (i : Fin k) × Fin (G.len (x i)),
      F ((G.varEquiv x).symm p) = slotE S.m p.1
        (fourierFactor (S.U (x p.1) p.2) (a ((G.varEquiv x).symm p))) := by
    intro p
    simp only [hF, PermStrategy.repeat]
    rw [Equiv.apply_symm_apply, fourierFactor_map]
  have hcomm : List.Pairwise Commute
      ((List.finRange (G.lenRSum x + G.lenLSum x)).map F) := by
    refine List.pairwise_map.2 (List.pairwise_of_forall fun g h => ?_)
    obtain ⟨p, rfl⟩ := (G.varEquiv x).symm.surjective g
    obtain ⟨q, rfl⟩ := (G.varEquiv x).symm.surjective h
    rw [hF', hF']
    refine commute_slotE_of fun hpq => ?_
    obtain ⟨i, v⟩ := p
    obtain ⟨j, w⟩ := q
    simp only at hpq
    subst hpq
    exact ((Commute.fourierFactor_right (S.comm _ _ _) _).symm.fourierFactor_right _).symm
  change ((List.finRange _).map F).prod = _
  rw [((finRange_perm_flatMap (G := G) k x).map F).prod_eq' hcomm, List.map_flatMap, List.flatMap_def,
    List.prod_flatten]
  simp only [List.map_map, Function.comp_def, hF']
  have hin : ∀ i, ((List.finRange (G.len (x i))).map fun v =>
      slotE S.m i (fourierFactor (S.U (x i) v) (a ((G.varEquiv x).symm ⟨i, v⟩)))).prod =
        slotE S.m i (S.proj (x i) fun v => a ((G.varEquiv x).symm ⟨i, v⟩)) := by
    intro i
    have e : (fun v => slotE S.m i (fourierFactor (S.U (x i) v) (a ((G.varEquiv x).symm ⟨i, v⟩)))) =
        (slotE S.m i) ∘ fun v => fourierFactor (S.U (x i) v) (a ((G.varEquiv x).symm ⟨i, v⟩)) := rfl
    rw [e, ← List.map_map, ← map_list_prod]
    rfl
  simp only [hin]
  rw [tensorProj, reindex_eq_reindexAlgEquiv, ← prod_slot_finRange, map_list_prod,
    List.map_map]
  rfl

/-- A product of two tensor products is zero when one coordinate's product is. -/
theorem reindex_tensorFamily_mul_eq_zero {m : ℕ} (P Q : Fin k → Matrix (Fin m) (Fin m) ℂ)
    (i : Fin k) (h : P i * Q i = 0) :
    Matrix.reindex (powEquiv m k) (powEquiv m k) (tensorFamily P) *
      Matrix.reindex (powEquiv m k) (powEquiv m k) (tensorFamily Q) = 0 := by
  rw [reindex_eq_reindexAlgEquiv, reindex_eq_reindexAlgEquiv, ← map_mul,
    tensorFamily_mul, tensorFamily_eq_zero (i := i) h, map_zero]

/-- **The tensor power of a perfect permutation strategy is perfect.** -/
theorem value_repeat_eq_one (hS : S.value = 1) : (S.repeat k).value = 1 := by
  refine (S.repeat k).value_eq_one_of fun x y hxy a b hrej => ?_
  have hcoord : ∀ (z : Fin k → X) (c : Fin ((G.repeat k).len z) → Bool) (i : Fin k),
      G.coord z (List.ofFn c) i = List.ofFn fun v => c ((G.varEquiv z).symm ⟨i, v⟩) := by
    intro z c i
    simp only [TailoredGame.coord, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    congr 1
    funext v
    split_ifs with h
    · rfl
    · exact absurd ((G.varEquiv z).symm ⟨i, v⟩).isLt h
  rw [G.repeat_accepts_iff] at hrej
  push Not at hrej
  obtain ⟨i, hi⟩ := hrej (List.length_ofFn) (List.length_ofFn)
  rw [hcoord, hcoord] at hi
  have h0 := S.proj_mul_eq_zero_of_value_eq_one hS (G.pos_of_repeat_pos hxy i) hi
  rw [proj_repeat S k x a, proj_repeat S k y b]
  exact reindex_tensorFamily_mul_eq_zero k _ _ i h0

end PermStrategy

/-! ## Pulling a permutation strategy back along a map of questions -/

section Comap

variable {Y : Type*} [Fintype Y] {G : TailoredGame X} {G' : TailoredGame Y}

/-- The lengths at `y` are those at `φ y`. -/
def SameLens (G : TailoredGame X) (G' : TailoredGame Y) (φ : Y → X) (y : Y) : Prop :=
  G'.lenR y = G.lenR (φ y) ∧ G'.lenL y = G.lenL (φ y)

theorem SameLens.len_eq {φ : Y → X} {y : Y} (h : SameLens G G' φ y) :
    G'.len y = G.len (φ y) := by
  unfold TailoredGame.len; rw [h.1, h.2]

/-- The Fourier transform reindexed along `Fin.cast`. -/
theorem fourierProj_cast {R : Type*} [Ring R] [Algebra ℂ R] {n n' : ℕ} (hn : n = n')
    (U : Fin n' → R) (a : Fin n → Bool) :
    fourierProj (fun j => U (Fin.cast hn j)) a = fourierProj U fun j => a (Fin.cast hn.symm j) := by
  subst hn
  rfl

open Classical in
/-- **A permutation strategy pulled back along `φ`**: at a question with the lengths of its
image, the observables of the image; elsewhere the identity. The hypothesis is that the edges
of `G'` join such questions and are sent to edges of `G`. -/
noncomputable def PermStrategy.comap (S : PermStrategy G) (G' : TailoredGame Y) (φ : Y → X)
    (hedge : ∀ y₁ y₂, 0 < G'.μ y₁ y₂ →
      SameLens G G' φ y₁ ∧ SameLens G G' φ y₂ ∧ 0 < G.μ (φ y₁) (φ y₂)) :
    PermStrategy G' where
  m := S.m
  m_pos := S.m_pos
  U y j := if h : SameLens G G' φ y then S.U (φ y) (Fin.cast h.len_eq j) else 1
  signedPerm y j := by
    split_ifs
    · exact S.signedPerm _ _
    · exact IsSignedPerm.one
  invol y j := by
    split_ifs
    · exact S.invol _ _
    · exact one_mul 1
  comm y i j := by
    split_ifs
    · exact S.comm _ _ _
    · rfl
  zAligned y j hj := by
    split_ifs with h
    · exact S.zAligned _ _ (by simpa [← h.1] using hj)
    · exact Matrix.isDiag_one
  commEdges y₁ y₂ h i j := by
    obtain ⟨h₁, h₂, hpos⟩ := hedge y₁ y₂ h
    rw [dite_eq_left h₁, dite_eq_left h₂]
    exact S.commEdges _ _ hpos _ _

theorem PermStrategy.proj_comap (S : PermStrategy G) (φ : Y → X) (hedge) {y : Y}
    (h : SameLens G G' φ y) (a : Fin (G'.len y) → Bool) :
    (S.comap G' φ hedge).proj y a = S.proj (φ y) fun j => a (Fin.cast h.len_eq.symm j) := by
  unfold PermStrategy.proj PermStrategy.comap
  simp only [dite_eq_left h]
  exact fourierProj_cast h.len_eq _ a

/-- **A perfect strategy pulls back to a perfect strategy**, when the acceptance on the edges
of `G'` is implied by that on their images. -/
theorem PermStrategy.value_comap_eq_one (S : PermStrategy G) (hS : S.value = 1) (φ : Y → X)
    (hedge)
    (hacc : ∀ y₁ y₂, 0 < G'.μ y₁ y₂ → ∀ a b,
      G.Accepts (φ y₁) (φ y₂) a b → G'.Accepts y₁ y₂ a b) :
    (S.comap G' φ hedge).value = 1 := by
  refine PermStrategy.value_eq_one_of _ fun y₁ y₂ hpos a b hrej => ?_
  obtain ⟨h₁, h₂, hpos'⟩ := hedge y₁ y₂ hpos
  rw [S.proj_comap φ hedge h₁, S.proj_comap φ hedge h₂]
  refine S.proj_mul_eq_zero_of_value_eq_one hS hpos' fun hacc' => hrej ?_
  refine hacc y₁ y₂ hpos _ _ ?_
  have e₁ : List.ofFn (fun j => a (Fin.cast h₁.len_eq.symm j)) = List.ofFn a :=
    (List.ofFn_congr h₁.len_eq a).symm
  have e₂ : List.ofFn (fun j => b (Fin.cast h₂.len_eq.symm j)) = List.ofFn b :=
    (List.ofFn_congr h₂.len_eq b).symm
  rwa [e₁, e₂] at hacc'

end Comap

/-! ## The doubled product -/

namespace TailoredGame

variable {G : TailoredGame X} {k : ℕ}

/-- **A perfect ZPC strategy for the doubled game gives one for the doubled product**: the
tensor power of the strategy for `G.doubled`, read at `(p, x⃗)` on the questions
`(p, x₁), …, (p, x_k)`. -/
theorem HasPerfectZPC.repeat_doubled (h : G.doubled.HasPerfectZPC) :
    (G.repeat k).doubled.HasPerfectZPC := by
  obtain ⟨S, hS⟩ := h
  let φ : Bool × (Fin k → X) → Fin k → Bool × X := fun p i => (p.1, p.2 i)
  have hedge : ∀ p q, 0 < (G.repeat k).doubled.μ p q →
      SameLens (G.doubled.repeat k) (G.repeat k).doubled φ p ∧
        SameLens (G.doubled.repeat k) (G.repeat k).doubled φ q ∧
          0 < (G.doubled.repeat k).μ (φ p) (φ q) := by
    rintro ⟨s, x⟩ ⟨t, y⟩ hpos
    refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
    simp only [doubled_μ] at hpos
    split_ifs at hpos with hst
    · simp only [repeat_μ, doubled_μ, φ, hst, and_self, ite_true]
      simpa using hpos
    · exact absurd hpos (lt_irrefl 0)
  refine ⟨(S.repeat k).comap _ φ hedge, (S.repeat k).value_comap_eq_one
    (S.value_repeat_eq_one k hS) φ hedge fun p q _ a b hacc => ?_⟩
  exact hacc

end TailoredGame

end MIPRE.Tailored

end
