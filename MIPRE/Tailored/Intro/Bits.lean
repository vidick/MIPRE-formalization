/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.Closure
public import MIPRE.Foundations.Pasting

@[expose] public section

/-!
# The observable of one bit of an outcome

Phase 3c of `planning/aldous-lyons-track.md` (issue #281) computes, question by question, the
bit observables `encObs P enc i` of the honest strategy of the introspection verifier. Each is
the observable of one Boolean function of the outcome, `bitObs P f = ∑_λ (-1)^{f λ} P_λ`, and the
computation goes through the constructions the honest strategy is assembled from:

* `bitObs_congr`: only the outcomes with a nonzero projection matter;
* `bitObs_merge`, `bitObs_fibSum`, `bitObs_extend`, `bitObs_submatrix`, `bitObs_kronecker_one`:
  coarse-graining, zero extension, relabelling and an ancilla act on the bit function;
* `bitObs_const`, `bitObs_xor`: a constant bit is `±1`, and the observable of an exclusive or is
  the product;
* `bitObs_mul_fst`, `bitObs_mul_snd`: a bit of one factor of a joint measurement;
* `bitObs_kronecker`: a bit of an adaptive tensor `P a ⊗ Q a b` is controlled by `P`;
* `bitObs_readout`: a bit of a classical read-out is a `±1` diagonal.

`IsZBit P f` (a signed permutation, diagonal) and `IsXBit P f` (a signed permutation) are the two
properties the ZPC strategy needs of a readable and of a linear bit.
-/

namespace MIPRE.Tailored

open Finset Matrix
open scoped Kronecker

set_option linter.unusedSectionVars false

section General

variable {R : Type*} [Ring R] [Algebra ℂ R] {Λ : Type*} [Fintype Λ]

/-- The observable of the bit `f` of the outcome of `P`: `∑_λ (-1)^{f λ} P_λ`. -/
noncomputable def bitObs (P : Λ → R) (f : Λ → Bool) : R := pvmObs P fun l => bitSign (f l)

theorem encObs_eq_bitObs (P : Λ → R) {k : ℕ} (enc : Λ → Fin k → Bool) (i : Fin k) :
    encObs P enc i = bitObs P fun l => enc l i := rfl

/-- **Only the outcomes with a nonzero projection matter.** -/
theorem bitObs_congr {P : Λ → R} {f g : Λ → Bool} (h : ∀ l, P l ≠ 0 → f l = g l) :
    bitObs P f = bitObs P g := by
  unfold bitObs pvmObs
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : P l = 0
  · simp [hl]
  · dsimp only
    rw [h l hl]

theorem bitObs_merge {Λ' : Type*} [Fintype Λ'] [DecidableEq Λ'] (P : Λ → R) (φ : Λ → Λ')
    (f : Λ' → Bool) :
    bitObs (fun b => ∑ a ∈ univ.filter fun a => φ a = b, P a) f = bitObs P (f ∘ φ) :=
  encObs_merge P φ (fun b (_ : Fin 1) => f b) 0

theorem bitObs_extend {Λ' : Type*} [Fintype Λ'] (P : Λ → R) {ι : Λ → Λ'}
    (hι : Function.Injective ι) (f : Λ' → Bool) :
    bitObs (Function.extend ι P 0) f = bitObs P (f ∘ ι) :=
  encObs_extend P hι (fun b (_ : Fin 1) => f b) 0

theorem bitObs_comp_equiv {Λ' : Type*} [Fintype Λ'] (P : Λ → R) (e : Λ' ≃ Λ) (f : Λ → Bool) :
    bitObs (fun b => P (e b)) (f ∘ e) = bitObs P f := by
  unfold bitObs pvmObs
  exact Fintype.sum_equiv e _ _ fun _ => rfl

theorem bitObs_comp_equiv' {Λ' : Type*} [Fintype Λ'] (P : Λ → R) (e : Λ' ≃ Λ)
    (f : Λ' → Bool) : bitObs (fun b => P (e b)) f = bitObs P (f ∘ e.symm) := by
  rw [← bitObs_comp_equiv P e (f ∘ e.symm)]
  congr 1
  funext b
  simp

variable [StarRing R] {P : Λ → R}

theorem bitObs_const (hP : IsPVMIn P) (c : Bool) : bitObs P (fun _ => c) = bitSign c • 1 :=
  hP.pvmObs_const _

/-- **The observable of an exclusive or is the product.** -/
theorem bitObs_xor (hP : IsPVMIn P) (f g : Λ → Bool) :
    bitObs P (fun l => xor (f l) (g l)) = bitObs P f * bitObs P g := by
  unfold bitObs
  rw [hP.pvmObs_mul]
  congr 1
  funext l
  simp [bitSign_xor]

end General

section Matrix

variable {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']
variable {Λ : Type*} [Fintype Λ]

theorem fibSum_eq_merge {Λ' : Type*} [DecidableEq Λ'] (P : Λ → Matrix Ω Ω ℂ) (φ : Λ → Λ') :
    fibSum P φ = fun b => ∑ a ∈ univ.filter fun a => φ a = b, P a := rfl

theorem bitObs_fibSum {Λ' : Type*} [Fintype Λ'] [DecidableEq Λ'] (P : Λ → Matrix Ω Ω ℂ)
    (φ : Λ → Λ') (f : Λ' → Bool) : bitObs (fibSum P φ) f = bitObs P (f ∘ φ) :=
  bitObs_merge P φ f

theorem bitObs_submatrix (P : Λ → Matrix Ω Ω ℂ) (e : Ω' → Ω) (f : Λ → Bool) :
    bitObs (fun a => (P a).submatrix e e) f = (bitObs P f).submatrix e e :=
  encObs_submatrix P e (fun a (_ : Fin 1) => f a) 0

theorem bitObs_kronecker_one (P : Λ → Matrix Ω Ω ℂ) (f : Λ → Bool) :
    bitObs (fun a => P a ⊗ₖ (1 : Matrix Ω' Ω' ℂ)) f = bitObs P f ⊗ₖ 1 :=
  encObs_kronecker_one P (fun a (_ : Fin 1) => f a) 0

theorem bitObs_zero (f : Λ → Bool) : bitObs (fun _ : Λ => (0 : Matrix Ω Ω ℂ)) f = 0 := by
  simp [bitObs, pvmObs]

theorem bitObs_add_kronecker {A B : Type*} [Fintype A] [Fintype B] (P : A → Matrix Ω Ω ℂ)
    (Q : A → B → Matrix Ω' Ω' ℂ) (f : A × B → Bool) :
    bitObs (fun ab : A × B => P ab.1 ⊗ₖ Q ab.1 ab.2) f =
      ∑ a, P a ⊗ₖ bitObs (Q a) fun b => f (a, b) := by
  unfold bitObs pvmObs
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  ext ⟨u, u'⟩ ⟨v, v'⟩
  simp [Matrix.sum_apply, Finset.mul_sum, mul_left_comm]

/-- **A bit of one factor of a joint measurement**, the other factor summing to one. -/
theorem bitObs_mul_fst {A B : Type*} [Fintype A] [Fintype B] (P : A → Matrix Ω Ω ℂ)
    (Q : B → Matrix Ω Ω ℂ) (hQ : ∑ b, Q b = 1) (f : A → Bool) :
    bitObs (fun ab : A × B => P ab.1 * Q ab.2) (fun ab => f ab.1) = bitObs P f := by
  unfold bitObs pvmObs
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only
  rw [← Finset.smul_sum, ← Finset.mul_sum, hQ, mul_one]

theorem bitObs_mul_snd {A B : Type*} [Fintype A] [Fintype B] (P : A → Matrix Ω Ω ℂ)
    (Q : B → Matrix Ω Ω ℂ) (hP : ∑ a, P a = 1) (f : B → Bool) :
    bitObs (fun ab : A × B => P ab.1 * Q ab.2) (fun ab => f ab.2) = bitObs Q f := by
  unfold bitObs pvmObs
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  dsimp only
  rw [← Finset.smul_sum, ← Finset.sum_mul, hP, one_mul]

/-- A bit of a classical read-out is a `±1` diagonal. -/
theorem bitObs_readout {K : Type*} [Fintype K] [DecidableEq K] (φ : Ω → K) (f : K → Bool) :
    bitObs (Introspection.readout φ) f = diagonal fun i => bitSign (f (φ i)) := by
  ext i j
  simp only [bitObs, pvmObs, Matrix.sum_apply, Matrix.smul_apply, Introspection.readout,
    diagonal_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-! ### The two properties of a bit -/

/-- A readable bit: its observable is a diagonal signed permutation. -/
def IsZBit (P : Λ → Matrix Ω Ω ℂ) (f : Λ → Bool) : Prop :=
  IsSignedPerm (bitObs P f) ∧ (bitObs P f).IsDiag

/-- A linear bit: its observable is a signed permutation. -/
def IsXBit (P : Λ → Matrix Ω Ω ℂ) (f : Λ → Bool) : Prop := IsSignedPerm (bitObs P f)

theorem IsZBit.isXBit {P : Λ → Matrix Ω Ω ℂ} {f : Λ → Bool} (h : IsZBit P f) : IsXBit P f :=
  h.1

theorem isSignedPerm_bitSign_smul_one (c : Bool) :
    IsSignedPerm (bitSign c • (1 : Matrix Ω Ω ℂ)) := by
  cases c
  · simpa [bitSign] using (IsSignedPerm.one : IsSignedPerm (1 : Matrix Ω Ω ℂ))
  · simpa [bitSign] using (IsSignedPerm.neg_one : IsSignedPerm (-1 : Matrix Ω Ω ℂ))

theorem isDiag_bitSign_smul_one (c : Bool) : (bitSign c • (1 : Matrix Ω Ω ℂ)).IsDiag :=
  (isDiag_one).smul _

theorem isZBit_const {P : Λ → Matrix Ω Ω ℂ} (hP : IsPVMIn P) (c : Bool) :
    IsZBit P fun _ => c := by
  unfold IsZBit
  rw [bitObs_const hP]
  exact ⟨isSignedPerm_bitSign_smul_one c, isDiag_bitSign_smul_one c⟩

theorem isZBit_readout {K : Type*} [Fintype K] [DecidableEq K] (φ : Ω → K) (f : K → Bool) :
    IsZBit (Introspection.readout φ) f := by
  unfold IsZBit
  rw [bitObs_readout]
  exact ⟨IsSignedPerm.diagonal _, isDiag_diagonal _⟩

theorem IsZBit.congr {P : Λ → Matrix Ω Ω ℂ} {f g : Λ → Bool} (h : IsZBit P f)
    (hfg : ∀ l, P l ≠ 0 → f l = g l) : IsZBit P g := by
  unfold IsZBit at *
  rwa [← bitObs_congr hfg]

theorem IsXBit.congr {P : Λ → Matrix Ω Ω ℂ} {f g : Λ → Bool} (h : IsXBit P f)
    (hfg : ∀ l, P l ≠ 0 → f l = g l) : IsXBit P g := by
  unfold IsXBit at *
  rwa [← bitObs_congr hfg]

theorem IsXBit.xor {P : Λ → Matrix Ω Ω ℂ} (hP : IsPVMIn P) {f g : Λ → Bool} (hf : IsXBit P f)
    (hg : IsXBit P g) : IsXBit P fun l => Bool.xor (f l) (g l) := by
  unfold IsXBit at *
  rw [bitObs_xor hP]
  exact hf.mul hg

theorem IsZBit.xor {P : Λ → Matrix Ω Ω ℂ} (hP : IsPVMIn P) {f g : Λ → Bool} (hf : IsZBit P f)
    (hg : IsZBit P g) : IsZBit P fun l => Bool.xor (f l) (g l) := by
  unfold IsZBit at *
  rw [bitObs_xor hP]
  exact ⟨hf.1.mul hg.1, isDiag_mul hf.2 hg.2⟩

theorem isZBit_merge_iff {Λ' : Type*} [Fintype Λ'] [DecidableEq Λ'] (P : Λ → Matrix Ω Ω ℂ)
    (φ : Λ → Λ') (f : Λ' → Bool) :
    IsZBit (fun b => ∑ a ∈ univ.filter fun a => φ a = b, P a) f ↔ IsZBit P (f ∘ φ) := by
  unfold IsZBit
  rw [bitObs_merge]

theorem isXBit_merge_iff {Λ' : Type*} [Fintype Λ'] [DecidableEq Λ'] (P : Λ → Matrix Ω Ω ℂ)
    (φ : Λ → Λ') (f : Λ' → Bool) :
    IsXBit (fun b => ∑ a ∈ univ.filter fun a => φ a = b, P a) f ↔ IsXBit P (f ∘ φ) := by
  unfold IsXBit
  rw [bitObs_merge]

theorem IsZBit.submatrix_equiv {P : Λ → Matrix Ω Ω ℂ} {f : Λ → Bool} (h : IsZBit P f)
    (e : Ω' ≃ Ω) : IsZBit (fun a => (P a).submatrix e e) f := by
  unfold IsZBit at *
  rw [bitObs_submatrix]
  exact ⟨h.1.submatrix_equiv e, isDiag_submatrix_equiv h.2 e⟩

theorem IsXBit.submatrix_equiv {P : Λ → Matrix Ω Ω ℂ} {f : Λ → Bool} (h : IsXBit P f)
    (e : Ω' ≃ Ω) : IsXBit (fun a => (P a).submatrix e e) f := by
  unfold IsXBit at *
  rw [bitObs_submatrix]
  exact h.submatrix_equiv e

theorem IsZBit.kronecker_one {P : Λ → Matrix Ω Ω ℂ} {f : Λ → Bool} (h : IsZBit P f) :
    IsZBit (fun a => P a ⊗ₖ (1 : Matrix Ω' Ω' ℂ)) f := by
  unfold IsZBit at *
  rw [bitObs_kronecker_one]
  exact ⟨h.1.kronecker_one, isDiag_kronecker_one h.2⟩

theorem IsXBit.kronecker_one {P : Λ → Matrix Ω Ω ℂ} {f : Λ → Bool} (h : IsXBit P f) :
    IsXBit (fun a => P a ⊗ₖ (1 : Matrix Ω' Ω' ℂ)) f := by
  unfold IsXBit at *
  rw [bitObs_kronecker_one]
  exact h.kronecker_one

/-- **A bit controlled by a classical read-out**: if the measurement is `readout φ z ⊗ Q z a`
at `(z, a)`, the bit is a signed permutation when each `Q z`'s is. -/
theorem isXBit_controlled {K A : Type*} [Fintype K] [DecidableEq K] [Fintype A]
    (φ : Ω → K) (Q : K → A → Matrix Ω' Ω' ℂ) (f : K × A → Bool)
    (h : ∀ z, IsXBit (Q z) fun a => f (z, a)) :
    IsXBit (fun za : K × A => Introspection.readout φ za.1 ⊗ₖ Q za.1 za.2) f := by
  unfold IsXBit at *
  rw [bitObs_add_kronecker]
  exact isSignedPerm_controlled φ _ h

theorem isZBit_controlled {K A : Type*} [Fintype K] [DecidableEq K] [Fintype A]
    (φ : Ω → K) (Q : K → A → Matrix Ω' Ω' ℂ) (f : K × A → Bool)
    (h : ∀ z, IsZBit (Q z) fun a => f (z, a)) :
    IsZBit (fun za : K × A => Introspection.readout φ za.1 ⊗ₖ Q za.1 za.2) f := by
  unfold IsZBit at *
  rw [bitObs_add_kronecker]
  exact ⟨isSignedPerm_controlled φ _ fun z => (h z).1,
    isDiag_controlled φ _ fun z => (h z).2⟩

end Matrix

end MIPRE.Tailored

end
