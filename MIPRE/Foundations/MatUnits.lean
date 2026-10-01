/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.Prod
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import MIPRE.Tactics

@[expose] public section

/-!
# Unital dyadic matrix units

The orthonormalization step of the C6b port (`planning/c6b-plan.md`, §1, item 2) applies only in
algebras without nonzero abelian projections, and the class of models it is run in is cut out by a
purely algebraic condition that excludes them: unital `2ⁿ × 2ⁿ` matrix units for every `n`
(`reports/c6b-paper-proofs.md`, §3). This file is that condition and its algebra; the trace
estimate that turns it into the absence of abelian projections is
`MIPRE/Foundations/DyadicPair.lean`.

* **`IsMatUnits e`**: a family `e : ι → ι → A` of a `⋆`-ring is a system of unital matrix units,
  `eᵢⱼ eₗₘ = [j = l] eᵢₘ`, `eᵢⱼ⋆ = eⱼᵢ`, `∑ᵢ eᵢᵢ = 1`.
* **`HasDyadicUnits A`**: `A` has unital matrix units indexed by `Fin n → Fin 2`, for every `n`.
  Indexing by bit strings, rather than by `Fin (2 ^ n)`, is what makes the tensor-product
  construction below a plain recursion.
* **Transports.** The condition passes along unital `⋆`-homomorphisms (`HasDyadicUnits.map`), to
  the opposite ring (`.op`, transposing), to square matrices over the ring (`.matrix`, as
  scalar diagonals: the first player's algebra of an ancilla extension `M.expand e`) and to
  products (`.prod`).
* **Pauli sites.** A `⋆`-algebra with a self-adjoint anticommuting pair of symmetries `(xₖ, zₖ)` at
  each site `k : ℕ`, pairs at distinct sites commuting (`PauliSites`), has dyadic units
  (`PauliSites.hasDyadicUnits`): the single-site units are `xᵃ p xᵇ` with `p = (1 + z)/2`, and
  the `2ⁿ × 2ⁿ` units are their products over the sites `0, …, n - 1`. This is how the twisted
  Pauli algebra of the value lemma's amplification gets its units.
-/

namespace MIPRE

/-! ## Unital matrix units -/

/-- **Unital matrix units** (`def:dyadic-units`) in a `⋆`-ring, indexed by a finite type `ι`:
`eᵢⱼ eₗₘ = [j = l] eᵢₘ`, `eᵢⱼ⋆ = eⱼᵢ` and `∑ᵢ eᵢᵢ = 1`. -/
structure IsMatUnits {A : Type*} [Ring A] [StarRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ι → A) : Prop where
  /-- The multiplication rule `eᵢⱼ eₗₘ = [j = l] eᵢₘ`. -/
  mul : ∀ i j l m, e i j * e l m = if j = l then e i m else 0
  /-- The adjoint rule `eᵢⱼ⋆ = eⱼᵢ`. -/
  star_eq : ∀ i j, star (e i j) = e j i
  /-- The units are unital: `∑ᵢ eᵢᵢ = 1`. -/
  sum_diag : ∑ i, e i i = 1

namespace IsMatUnits

variable {A : Type*} [Ring A] [StarRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {e : ι → ι → A}

/-- `eᵢⱼ eⱼₘ = eᵢₘ`. -/
theorem mul_cancel (he : IsMatUnits e) (i j m : ι) : e i j * e j m = e i m := by
  rw [he.mul, ite_eq_left rfl]

/-- **Matrix units pass along a unital `⋆`-homomorphism** (`lem:dyadic-units-closure`). -/
theorem map (he : IsMatUnits e) {B F : Type*} [Ring B] [StarRing B] [FunLike F A B]
    [RingHomClass F A B] [StarHomClass F A B] (φ : F) : IsMatUnits fun i j => φ (e i j) where
  mul i j l m := by rw [← map_mul, he.mul]; split_ifs <;> simp
  star_eq i j := by rw [← map_star, he.star_eq]
  sum_diag := by rw [← map_sum, he.sum_diag, map_one]

/-- **Transposed matrix units in the opposite ring** (`lem:dyadic-units-closure`):
`eᵢⱼ ↦ op eⱼᵢ`. -/
theorem op (he : IsMatUnits e) : IsMatUnits fun i j => MulOpposite.op (e j i) where
  mul i j l m := by
    rw [← MulOpposite.op_mul, he.mul]
    by_cases h : j = l
    · subst h; simp
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h, MulOpposite.op_zero]
  star_eq i j := by rw [← MulOpposite.op_star, he.star_eq]
  sum_diag := by rw [← Finset.op_sum, he.sum_diag, MulOpposite.op_one]

/-- **Scalar-diagonal amplification** (`lem:dyadic-units-closure`): `eᵢⱼ ↦ diag(eᵢⱼ, …, eᵢⱼ)` in
the `α × α` matrices. -/
theorem diagonal (he : IsMatUnits e) (α : Type*) [Fintype α] [DecidableEq α] :
    IsMatUnits fun i j => Matrix.diagonal fun _ : α => e i j where
  mul i j l m := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [he.mul]
    split_ifs <;> simp
  star_eq i j := by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    simp only [Pi.star_def, he.star_eq]
  sum_diag := by
    rw [← Matrix.diagonal_one]
    ext a b
    simp only [Matrix.sum_apply, Matrix.diagonal_apply]
    split_ifs
    · rw [he.sum_diag]
    · simp

/-- **Componentwise matrix units in a product** (`lem:dyadic-units-closure`):
`eᵢⱼ ↦ (eᵢⱼ, fᵢⱼ)`. -/
theorem prod (he : IsMatUnits e) {B : Type*} [Ring B] [StarRing B] {f : ι → ι → B}
    (hf : IsMatUnits f) : IsMatUnits fun i j => (e i j, f i j) where
  mul i j l m := by rw [Prod.mk_mul_mk, he.mul, hf.mul]; split_ifs <;> rfl
  star_eq i j := by rw [Prod.star_def]; simp only [he.star_eq, hf.star_eq]
  sum_diag := by
    rw [Prod.ext_iff]
    simp only [Prod.fst_sum, Prod.snd_sum, he.sum_diag, hf.sum_diag, Prod.fst_one, Prod.snd_one,
      and_self]

end IsMatUnits

/-! ## Dyadic matrix units -/

/-- **Unital dyadic matrix units** (`def:dyadic-units`): a `⋆`-ring has unital matrix units of size
`2ⁿ` for every `n`, indexed by the bit strings `Fin n → Fin 2`. -/
def HasDyadicUnits (A : Type*) [Ring A] [StarRing A] : Prop :=
  ∀ n : ℕ, ∃ e : (Fin n → Fin 2) → (Fin n → Fin 2) → A, IsMatUnits e

namespace HasDyadicUnits

variable {A : Type*} [Ring A] [StarRing A]

/-- **Dyadic units pass along a unital `⋆`-homomorphism** (`lem:dyadic-units-closure`). -/
theorem map (h : HasDyadicUnits A) {B F : Type*} [Ring B] [StarRing B] [FunLike F A B]
    [RingHomClass F A B] [StarHomClass F A B] (φ : F) : HasDyadicUnits B :=
  fun n => by obtain ⟨e, he⟩ := h n; exact ⟨_, he.map φ⟩

/-- **Dyadic units pass to the opposite ring** (`lem:dyadic-units-closure`). -/
theorem op (h : HasDyadicUnits A) : HasDyadicUnits Aᵐᵒᵖ :=
  fun n => by obtain ⟨e, he⟩ := h n; exact ⟨_, he.op⟩

/-- **Dyadic units pass to square matrices over the ring** (`lem:dyadic-units-closure`), as scalar
diagonals. -/
theorem matrix (h : HasDyadicUnits A) (α : Type*) [Fintype α] [DecidableEq α] :
    HasDyadicUnits (Matrix α α A) :=
  fun n => by obtain ⟨e, he⟩ := h n; exact ⟨_, he.diagonal α⟩

/-- **Dyadic units pass to products** (`lem:dyadic-units-closure`), componentwise. -/
theorem prod (h : HasDyadicUnits A) {B : Type*} [Ring B] [StarRing B] (hB : HasDyadicUnits B) :
    HasDyadicUnits (A × B) := fun n => by
  obtain ⟨e, he⟩ := h n
  obtain ⟨f, hf⟩ := hB n
  exact ⟨_, he.prod hf⟩

end HasDyadicUnits

/-! ## Dyadic units from Pauli sites -/

/-- **Pauli sites** (`lem:pauli-sites-units`) in a `⋆`-ring: at each site `k : ℕ` a self-adjoint
anticommuting pair of symmetries `(x k, z k)`, the pairs at distinct sites commuting. -/
structure PauliSites (R : Type*) [Ring R] [StarRing R] where
  /-- The `X` symmetry at each site. -/
  x : ℕ → R
  /-- The `Z` symmetry at each site. -/
  z : ℕ → R
  /-- `xₖ² = 1`. -/
  x_mul_self : ∀ k, x k * x k = 1
  /-- `zₖ² = 1`. -/
  z_mul_self : ∀ k, z k * z k = 1
  /-- `xₖ` and `zₖ` anticommute. -/
  z_mul_x : ∀ k, z k * x k = -(x k * z k)
  /-- `xₖ` is self-adjoint. -/
  star_x : ∀ k, star (x k) = x k
  /-- `zₖ` is self-adjoint. -/
  star_z : ∀ k, star (z k) = z k
  /-- The `X` symmetries at distinct sites commute. -/
  commute_x_x : ∀ k l, k ≠ l → Commute (x k) (x l)
  /-- The `X` and `Z` symmetries at distinct sites commute. -/
  commute_x_z : ∀ k l, k ≠ l → Commute (x k) (z l)
  /-- The `Z` symmetries at distinct sites commute. -/
  commute_z_z : ∀ k l, k ≠ l → Commute (z k) (z l)

namespace PauliSites

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] (S : PauliSites R)

/-- The projection `pₖ = (1 + zₖ)/2`. -/
noncomputable def proj (k : ℕ) : R := (2⁻¹ : ℂ) • (1 + S.z k)

/-- The power `xₖᵃ`, for a bit `a`. -/
def xpow (k : ℕ) (a : Fin 2) : R := if a = 0 then 1 else S.x k

/-- **The single-site matrix units** `xₖᵃ pₖ xₖᵇ`. -/
noncomputable def unit (k : ℕ) (a b : Fin 2) : R := S.xpow k a * S.proj k * S.xpow k b

omit [StarModule ℂ R] in
/-- `pₖ` is idempotent. -/
theorem proj_mul_self (k : ℕ) : S.proj k * S.proj k = S.proj k := by
  simp only [proj, smul_mul_smul, add_mul, mul_add, one_mul, mul_one, S.z_mul_self]
  module

/-- `pₖ` is self-adjoint. -/
theorem star_proj (k : ℕ) : star (S.proj k) = S.proj k := by
  simp [proj, star_add, S.star_z]

omit [StarModule ℂ R] in
/-- Conjugating by `xₖ` exchanges `pₖ` and `1 - pₖ`. -/
theorem x_mul_proj_mul_x (k : ℕ) : S.x k * S.proj k * S.x k = 1 - S.proj k := by
  have hxzx : S.x k * S.z k * S.x k = -S.z k := by
    rw [mul_assoc, S.z_mul_x, mul_neg, ← mul_assoc, S.x_mul_self, one_mul]
  simp only [proj, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, S.x_mul_self, hxzx]
  module

omit [StarModule ℂ R] in
/-- `pₖ xₖ pₖ = 0`. -/
theorem proj_mul_x_mul_proj (k : ℕ) : S.proj k * S.x k * S.proj k = 0 := by
  calc S.proj k * S.x k * S.proj k = S.x k * (S.x k * S.proj k * S.x k) * S.proj k := by
        simp only [← mul_assoc, S.x_mul_self, one_mul]
    _ = 0 := by
        rw [x_mul_proj_mul_x, mul_assoc, sub_mul, one_mul, S.proj_mul_self, sub_self, mul_zero]

omit [Algebra ℂ R] [StarModule ℂ R] in
/-- `(xₖᵃ)² = 1`. -/
theorem xpow_mul_self (k : ℕ) (a : Fin 2) : S.xpow k a * S.xpow k a = 1 := by
  unfold xpow; split_ifs <;> simp [S.x_mul_self]

omit [Algebra ℂ R] [StarModule ℂ R] in
/-- `xₖᵃ xₖᵇ = xₖ` for distinct bits. -/
theorem xpow_mul_xpow_of_ne (k : ℕ) {a b : Fin 2} (h : a ≠ b) :
    S.xpow k a * S.xpow k b = S.x k := by
  unfold xpow
  split_ifs with ha hb hb
  · exact absurd (ha.trans hb.symm) h
  · simp
  · simp
  · exfalso; omega

omit [Algebra ℂ R] [StarModule ℂ R] in
/-- `xₖᵃ` is self-adjoint. -/
theorem star_xpow (k : ℕ) (a : Fin 2) : star (S.xpow k a) = S.xpow k a := by
  unfold xpow; split_ifs <;> simp [S.star_x]

omit [StarModule ℂ R] in
/-- The multiplication rule of the single-site units. -/
theorem unit_mul (k : ℕ) (a b c d : Fin 2) :
    S.unit k a b * S.unit k c d = if b = c then S.unit k a d else 0 := by
  unfold unit
  have e : S.xpow k a * S.proj k * S.xpow k b * (S.xpow k c * S.proj k * S.xpow k d) =
      S.xpow k a * (S.proj k * (S.xpow k b * S.xpow k c) * S.proj k) * S.xpow k d := by
    simp only [mul_assoc]
  rw [e]
  split_ifs with h
  · subst h; rw [xpow_mul_self, mul_one, proj_mul_self]
  · rw [xpow_mul_xpow_of_ne _ _ h, proj_mul_x_mul_proj, mul_zero, zero_mul]

/-- The adjoint rule of the single-site units. -/
theorem star_unit (k : ℕ) (a b : Fin 2) : star (S.unit k a b) = S.unit k b a := by
  simp [unit, star_mul, star_xpow, star_proj, mul_assoc]

omit [StarModule ℂ R] in
/-- The single-site units are unital: `pₖ + xₖ pₖ xₖ = 1`. -/
theorem sum_unit_diag (k : ℕ) : ∑ a, S.unit k a a = 1 := by
  have h0 : S.unit k 0 0 = S.proj k := by simp [unit, xpow]
  have h1 : S.unit k 1 1 = S.x k * S.proj k * S.x k := by simp [unit, xpow]
  rw [Fin.sum_univ_two, h0, h1, x_mul_proj_mul_x, add_sub_cancel]

/-- **The single-site units are unital `2 × 2` matrix units.** -/
theorem isMatUnits_unit (k : ℕ) : IsMatUnits (S.unit k) :=
  ⟨S.unit_mul k, S.star_unit k, S.sum_unit_diag k⟩

omit [StarModule ℂ R] in
/-- `xₖ` commutes with the projection at another site. -/
theorem commute_x_proj {k l : ℕ} (h : k ≠ l) : Commute (S.x k) (S.proj l) :=
  ((Commute.one_right _).add_right (S.commute_x_z k l h)).smul_right _

omit [StarModule ℂ R] in
/-- `zₖ` commutes with the projection at another site. -/
theorem commute_z_proj {k l : ℕ} (h : k ≠ l) : Commute (S.z k) (S.proj l) :=
  ((Commute.one_right _).add_right (S.commute_z_z k l h)).smul_right _

omit [StarModule ℂ R] in
/-- The projections at distinct sites commute. -/
theorem commute_proj_proj {k l : ℕ} (h : k ≠ l) : Commute (S.proj k) (S.proj l) :=
  ((Commute.one_left _).add_left (S.commute_z_proj h)).smul_left _

omit [Algebra ℂ R] [StarModule ℂ R] in
/-- The powers of `x` at distinct sites commute. -/
theorem commute_xpow_xpow {k l : ℕ} (h : k ≠ l) (a b : Fin 2) :
    Commute (S.xpow k a) (S.xpow l b) := by
  unfold xpow; split_ifs
  · exact Commute.one_left _
  · exact Commute.one_left _
  · exact Commute.one_right _
  · exact S.commute_x_x k l h

omit [StarModule ℂ R] in
/-- A power of `xₖ` commutes with the projection at another site. -/
theorem commute_xpow_proj {k l : ℕ} (h : k ≠ l) (a : Fin 2) :
    Commute (S.xpow k a) (S.proj l) := by
  unfold xpow; split_ifs
  · exact Commute.one_left _
  · exact S.commute_x_proj h

omit [StarModule ℂ R] in
/-- The single-site units at distinct sites commute. -/
theorem commute_unit {k l : ℕ} (h : k ≠ l) (a b c d : Fin 2) :
    Commute (S.unit k a b) (S.unit l c d) := by
  have h1 : ∀ u, Commute u (S.xpow l c) → Commute u (S.proj l) → Commute u (S.xpow l d) →
      Commute u (S.unit l c d) := fun u h1 h2 h3 => (h1.mul_right h2).mul_right h3
  refine ((h1 _ ?_ ?_ ?_).mul_left (h1 _ ?_ ?_ ?_)).mul_left (h1 _ ?_ ?_ ?_)
  all_goals first
    | exact S.commute_xpow_xpow h _ _
    | exact S.commute_xpow_proj h _
    | exact (S.commute_xpow_proj (Ne.symm h) _).symm
    | exact S.commute_proj_proj h

/-- **The `2ⁿ × 2ⁿ` matrix units** on the sites `0, …, n - 1`: `e_{ij} = ∏ₖ unit k (iₖ) (jₖ)`, the
bit at index `0` read at site `n - 1`. -/
noncomputable def units : (n : ℕ) → (Fin n → Fin 2) → (Fin n → Fin 2) → R
  | 0, _, _ => 1
  | n + 1, i, j => S.unit n (i 0) (j 0) * units n (Fin.tail i) (Fin.tail j)

omit [StarModule ℂ R] in
/-- A single-site unit at site `m` commutes with the units on the sites below `n ≤ m`. -/
theorem commute_unit_units : ∀ n m, n ≤ m → ∀ (a b : Fin 2) (i j : Fin n → Fin 2),
    Commute (S.unit m a b) (S.units n i j)
  | 0, _, _, _, _, _, _ => Commute.one_right _
  | n + 1, m, hm, a, b, i, j =>
    (S.commute_unit (by omega) _ _ _ _).mul_right (commute_unit_units n m (by omega) a b _ _)

private theorem fin_tuple_eq_iff {n : ℕ} (j k : Fin (n + 1) → Fin 2) :
    j = k ↔ j 0 = k 0 ∧ Fin.tail j = Fin.tail k := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, ht⟩
    rw [← Fin.cons_self_tail j, ← Fin.cons_self_tail k, h0, ht]

omit [StarModule ℂ R] in
/-- The multiplication rule of the `2ⁿ × 2ⁿ` units. -/
theorem units_mul : ∀ (n : ℕ) (i j k l : Fin n → Fin 2),
    S.units n i j * S.units n k l = if j = k then S.units n i l else 0
  | 0, i, j, k, l => by simp [units, Subsingleton.elim j k]
  | n + 1, i, j, k, l => by
    have hc : S.units n (Fin.tail i) (Fin.tail j) * S.unit n (k 0) (l 0) =
        S.unit n (k 0) (l 0) * S.units n (Fin.tail i) (Fin.tail j) :=
      (S.commute_unit_units n n le_rfl _ _ _ _).eq.symm
    calc S.units (n + 1) i j * S.units (n + 1) k l
        = S.unit n (i 0) (j 0) * (S.units n (Fin.tail i) (Fin.tail j) * S.unit n (k 0) (l 0)) *
            S.units n (Fin.tail k) (Fin.tail l) := by simp only [units, mul_assoc]
      _ = (S.unit n (i 0) (j 0) * S.unit n (k 0) (l 0)) *
            (S.units n (Fin.tail i) (Fin.tail j) * S.units n (Fin.tail k) (Fin.tail l)) := by
          rw [hc]; simp only [mul_assoc]
      _ = _ := by
          rw [S.unit_mul, units_mul n]
          by_cases h0 : j 0 = k 0 <;> by_cases ht : Fin.tail j = Fin.tail k <;>
            simp [h0, ht, units, fin_tuple_eq_iff j k]

/-- The adjoint rule of the `2ⁿ × 2ⁿ` units. -/
theorem star_units : ∀ (n : ℕ) (i j : Fin n → Fin 2), star (S.units n i j) = S.units n j i
  | 0, _, _ => by simp [units]
  | n + 1, i, j => by
    simp only [units, star_mul, star_units n, S.star_unit]
    exact (S.commute_unit_units n n le_rfl _ _ _ _).eq.symm

omit [StarModule ℂ R] in
/-- The `2ⁿ × 2ⁿ` units are unital. -/
theorem sum_units_diag : ∀ n : ℕ, ∑ i, S.units n i i = 1
  | 0 => by simp [units]
  | n + 1 => by
    have ht : ∀ (a : Fin 2) (t : Fin n → Fin 2),
        Fin.tail ((Fin.consEquiv fun _ => Fin 2) (a, t)) = t := fun _ _ => rfl
    rw [← (Fin.consEquiv fun _ => Fin 2).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, units, Fin.cons_zero, ht]
    rw [← Finset.sum_mul_sum, S.sum_unit_diag, sum_units_diag n, one_mul]

/-- **The `2ⁿ × 2ⁿ` units of Pauli sites are unital matrix units.** -/
theorem isMatUnits_units (n : ℕ) : IsMatUnits (S.units n) :=
  ⟨S.units_mul n, S.star_units n, S.sum_units_diag n⟩

include S in
/-- **A `⋆`-algebra with Pauli sites has unital dyadic matrix units** (`lem:pauli-sites-units`). -/
theorem hasDyadicUnits : HasDyadicUnits R := fun n => ⟨S.units n, S.isMatUnits_units n⟩

end PauliSites

end MIPRE

end
