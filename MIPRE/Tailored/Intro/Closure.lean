/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.SignedPerm
public import MIPRE.Tailored.Intro.Encoded
public import MIPRE.Foundations.Weyl
public import MIPRE.Foundations.Introspection.Readout

@[expose] public section

/-!
# Signed permutations built by the honest introspection strategy

Phase 3 of `planning/aldous-lyons-track.md` (issue #281) shows that the honest strategy of the
introspection verifier is a ZPC strategy: all its observables are signed permutation matrices,
the readable ones diagonal. The strategy is assembled from Weyl operators and classical
read-outs, so the closure lemmas are:

* `isSignedPerm_wX`, `isSignedPerm_wZ`, `isDiag_wZ`: the shift `wX a` is a permutation matrix,
  the phase `wZ b` a `±1` diagonal;
* `isSignedPerm_blockDiag`: a block-diagonal matrix with signed-permutation blocks is one;
* `isSignedPerm_controlled`: so is a controlled sum `∑_z readout f z ⊗ U z`, the operator
  applying `U (f i)` on the second factor when the first is in the basis state `i`;
  `isDiag_controlled` when the blocks are diagonal.
-/

namespace MIPRE.Tailored

open Matrix Finset MIPRE.Weyl
open scoped Kronecker

set_option linter.unusedSectionVars false

/-! ## Signs -/

/-- The sign of an element of `ZMod 2` is the sign of its bit. -/
theorem sgn_eq_bitSign (x : ZMod 2) : sgn x = bitSign (decide (x = 1)) := by
  fin_cases x <;> rfl

/-! ## Weyl operators -/

section Weyl

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The shift `wX a` is the permutation matrix of the translation by `a`. -/
theorem wX_eq_signedPermMatrix (a : n → F) :
    wX a = signedPermMatrix (Equiv.addRight a) (fun _ => false) := by
  ext i j
  simp [wX, signedPermMatrix, bitSign, eq_comm]

theorem isSignedPerm_wX (a : n → F) : IsSignedPerm (wX a) :=
  ⟨_, _, wX_eq_signedPermMatrix a⟩

/-- The phase `wZ b` is a `±1` diagonal. -/
theorem wZ_eq_diagonal_bitSign (b : n → F) :
    wZ b = diagonal fun i => bitSign (decide (trDot b i = 1)) := by
  simp only [wZ, sgn_eq_bitSign]

theorem isSignedPerm_wZ (b : n → F) : IsSignedPerm (wZ b) := by
  rw [wZ_eq_diagonal_bitSign]
  exact IsSignedPerm.diagonal _

theorem isDiag_wZ (b : n → F) : (wZ b).IsDiag := by
  rw [wZ_eq_diagonal_bitSign]
  exact isDiag_diagonal _

/-! ### Linear data processing

Paper II, Corollary II:2938 (`cor:linear_data_processed_PVM_is_ZPC_and_left_multiplication`),
in the form the honest strategy uses it: an `F₂`-linear bit `φ` of the outcome of the
eigenbasis measurement of a Weyl family `w` has observable `w c`, where `c` represents `φ`
through the trace form. Every `F₂`-linear functional is such a `trDot · c`
(`exists_trDotL_eq`), since the trace form is nondegenerate. -/

/-- The trace form as a linear map to the dual. -/
noncomputable def trDotDual : (n → F) →ₗ[ZMod 2] Module.Dual (ZMod 2) (n → F) where
  toFun := trDotL
  map_add' c c' := by
    ext a
    simp [trDot_add_right]
  map_smul' r c := by
    ext a
    rcases (show r = 0 ∨ r = 1 from by revert r; decide) with rfl | rfl <;> simp

/-- **The trace form is nondegenerate**: every `F₂`-linear functional on `F_q^n` is
`trDot · c` for some `c`. -/
theorem exists_trDotL_eq (φ : Module.Dual (ZMod 2) (n → F)) : ∃ c : n → F, trDotL c = φ := by
  have : Module.Finite (ZMod 2) (n → F) := Module.Finite.of_finite
  have hinj : Function.Injective (trDotDual (F := F) (n := n)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra hne
    exact trDotL_ne_zero hne hc
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm |>.mp hinj) φ

/-- **The observable of the bit `trDot · c` of the eigenbasis measurement of `w` is `w c`.** -/
theorem encObs_proj_trDot (w : (n → F) → Matrix (n → F) (n → F) ℂ) {k : ℕ} (c : Fin k → n → F)
    (i : Fin k) :
    encObs (proj w) (fun e j => decide (trDot e (c j) = 1)) i = w (c i) := by
  rw [eq_sum_proj (w := w) (c i), encObs, pvmObs]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← sgn_eq_bitSign, trDot_comm]

/-- **Linear data processing** (II:2938): the observable of an `F₂`-linear bit of the outcome
of the eigenbasis measurement of `w` is an operator of the family. -/
theorem exists_encObs_proj_linear (w : (n → F) → Matrix (n → F) (n → F) ℂ) {k : ℕ}
    (φ : Fin k → Module.Dual (ZMod 2) (n → F)) (i : Fin k) :
    ∃ c : n → F, encObs (proj w) (fun e j => decide (φ j e = 1)) i = w c := by
  choose c hc using fun j => exists_trDotL_eq (φ j)
  refine ⟨c i, ?_⟩
  rw [← encObs_proj_trDot w c i]
  congr 1
  funext e j
  rw [← hc j, trDotL_apply]

/-- The `X`-basis measurement's linear bits are permutation matrices. -/
theorem isSignedPerm_encObs_xProj {k : ℕ} (φ : Fin k → Module.Dual (ZMod 2) (n → F))
    (i : Fin k) : IsSignedPerm (encObs (xProj (F := F) (n := n)) (fun e j => decide (φ j e = 1)) i) := by
  obtain ⟨c, hc⟩ := exists_encObs_proj_linear wX φ i
  rw [show (xProj (F := F) (n := n)) = proj wX from rfl, hc]
  exact isSignedPerm_wX c

/-- The `Z`-basis measurement's bits, linear or not, are `±1` diagonals. -/
theorem isSignedPerm_encObs_zProj {k : ℕ} (enc : (n → F) → Fin k → Bool) (i : Fin k) :
    IsSignedPerm (encObs (zProj (F := F) (n := n)) enc i) ∧
      (encObs (zProj (F := F) (n := n)) enc i).IsDiag := by
  have : encObs (zProj (F := F) (n := n)) enc i = diagonal fun e => bitSign (enc e i) := by
    rw [encObs, pvmObs]
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, zProj, diagonal_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [this]
  exact ⟨IsSignedPerm.diagonal _, isDiag_diagonal _⟩

end Weyl

/-! ## Block-diagonal and controlled sums -/

section Blocks

variable {Ω Ω' : Type*} [DecidableEq Ω] [DecidableEq Ω']

/-- The block-diagonal matrix with blocks `V i`. -/
def blockDiag (V : Ω → Matrix Ω' Ω' ℂ) : Matrix (Ω × Ω') (Ω × Ω') ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then V p.1 p.2 q.2 else 0

/-- **A block-diagonal matrix with signed-permutation blocks is a signed permutation.** -/
theorem isSignedPerm_blockDiag (V : Ω → Matrix Ω' Ω' ℂ) (hV : ∀ i, IsSignedPerm (V i)) :
    IsSignedPerm (blockDiag V) := by
  choose σ s hσ using hV
  refine ⟨Equiv.prodShear (Equiv.refl Ω) σ, fun q => s q.1 q.2, ?_⟩
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [blockDiag, of_apply, signedPermMatrix, Equiv.prodShear_apply, Equiv.refl_apply,
    Prod.mk.injEq]
  by_cases hij : i = j
  · subst hij
    rw [hσ i]
    simp [signedPermMatrix]
  · simp [hij, Ne.symm hij]

theorem isDiag_blockDiag (V : Ω → Matrix Ω' Ω' ℂ) (hV : ∀ i, (V i).IsDiag) :
    (blockDiag V).IsDiag := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hne
  simp only [blockDiag, of_apply]
  by_cases hij : i = j
  · subst hij
    have hab : a ≠ b := fun h => hne (by rw [h])
    simp [hV i hab]
  · simp [hij]

variable [Fintype Ω] {K : Type*} [Fintype K] [DecidableEq K]

/-- A controlled sum is block diagonal. -/
theorem controlled_eq_blockDiag (f : Ω → K) (U : K → Matrix Ω' Ω' ℂ) :
    ∑ z, Introspection.readout f z ⊗ₖ U z = blockDiag fun i => U (f i) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.sum_apply, kroneckerMap_apply, Introspection.readout, diagonal_apply,
    blockDiag, of_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- **A controlled sum of signed permutations is a signed permutation.** -/
theorem isSignedPerm_controlled (f : Ω → K) (U : K → Matrix Ω' Ω' ℂ)
    (hU : ∀ z, IsSignedPerm (U z)) : IsSignedPerm (∑ z, Introspection.readout f z ⊗ₖ U z) := by
  rw [controlled_eq_blockDiag]
  exact isSignedPerm_blockDiag _ fun i => hU (f i)

theorem isDiag_controlled (f : Ω → K) (U : K → Matrix Ω' Ω' ℂ) (hU : ∀ z, (U z).IsDiag) :
    (∑ z, Introspection.readout f z ⊗ₖ U z).IsDiag := by
  rw [controlled_eq_blockDiag]
  exact isDiag_blockDiag _ fun i => hU (f i)

/-- **The bit observables of a controlled measurement are controlled bit observables**: if the
measurement is `readout f z ⊗ Q z a` at the outcome `(z, a)`, the observable of a bit is the
controlled sum of the bit observables of the `Q z`. -/
theorem encObs_controlled [Fintype Ω'] {Λ : Type*} [Fintype Λ] {k : ℕ}
    (f : Ω → K) (Q : K → Λ → Matrix Ω' Ω' ℂ) (enc : K × Λ → Fin k → Bool) (i : Fin k) :
    encObs (fun za : K × Λ => Introspection.readout f za.1 ⊗ₖ Q za.1 za.2) enc i =
      ∑ z, Introspection.readout f z ⊗ₖ encObs (Q z) (fun a => enc (z, a)) i := by
  rw [encObs, pvmObs, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  ext ⟨u, u'⟩ ⟨v, v'⟩
  simp [encObs, pvmObs, Matrix.sum_apply, Finset.mul_sum, mul_left_comm]

end Blocks

/-! ## Relabellings and ancillas -/

section Relabel

variable {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']
variable {Λ : Type*} [Fintype Λ] {k : ℕ}

/-- Bit observables commute with a relabelling of the space. -/
theorem encObs_submatrix (P : Λ → Matrix Ω Ω ℂ) (e : Ω' → Ω) (enc : Λ → Fin k → Bool)
    (i : Fin k) :
    encObs (fun a => (P a).submatrix e e) enc i = (encObs P enc i).submatrix e e := by
  ext u v
  simp [encObs, pvmObs, Matrix.sum_apply]

/-- Bit observables commute with adding an ancilla on which the measurement is the identity. -/
theorem encObs_kronecker_one (P : Λ → Matrix Ω Ω ℂ) (enc : Λ → Fin k → Bool) (i : Fin k) :
    encObs (fun a => P a ⊗ₖ (1 : Matrix Ω' Ω' ℂ)) enc i = encObs P enc i ⊗ₖ 1 := by
  ext u v
  simp [encObs, pvmObs, Matrix.sum_apply, Finset.sum_mul, mul_assoc]

theorem IsSignedPerm.kronecker_one {M : Matrix Ω Ω ℂ} (hM : IsSignedPerm M) :
    IsSignedPerm (M ⊗ₖ (1 : Matrix Ω' Ω' ℂ)) :=
  hM.kronecker IsSignedPerm.one

theorem IsSignedPerm.submatrix_equiv {M : Matrix Ω Ω ℂ} (hM : IsSignedPerm M) (e : Ω' ≃ Ω) :
    IsSignedPerm (M.submatrix e e) := by
  simpa [Matrix.reindex_apply] using hM.reindex e.symm

theorem isDiag_submatrix_equiv {M : Matrix Ω Ω ℂ} (hM : M.IsDiag) (e : Ω' ≃ Ω) :
    (M.submatrix e e).IsDiag :=
  hM.submatrix e.injective

theorem isDiag_kronecker_one {M : Matrix Ω Ω ℂ} (hM : M.IsDiag) :
    (M ⊗ₖ (1 : Matrix Ω' Ω' ℂ)).IsDiag :=
  hM.kronecker isDiag_one

end Relabel

end MIPRE.Tailored

end
