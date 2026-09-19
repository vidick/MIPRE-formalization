/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Sign
import MIPRE.Foundations.LowDegree.Anticomm
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Generalized Pauli operators over a field of characteristic two

The paper's `sec:generalized-pauli`: for `a ∈ F_q^n` the `X`-type operator shifts the
computational basis of `(C^q)^{⊗ n}` by `a`, the `Z`-type operator is diagonal with the phase
`ω^{tr(a · b)}`, and the two families *twisted-commute*,
`τ^X(a) τ^Z(b) = ω^{-tr(a · b)} τ^Z(b) τ^X(a)`.

This is the missing half of the Pauli basis test's infrastructure. `MIPRE/LCS/Pauli.lean` is the
`2 × 2` Pauli matrices for the Magic Square; what the appendix's expansion stage and its swap
isometry both run on is the `F_q` Weyl system, and that is this file.

## Two deliberate restrictions

**Characteristic two.** The paper states the construction over `F_p` with `ω = e^{2πi/p}` and
then specializes. This file is only the `p = 2` case, where `ω = -1` and every phase is the real
sign `MIPRE.sgn` of `MIPRE/Foundations/Sign.lean`. That is not a loss for this project: the
Pauli basis test's parameters are *admissible* (`def:admissible`), which means `q = 2^k`, and no
consumer instantiates it elsewhere. What it buys is large — there are no roots of unity, the
operators are self-adjoint involutions rather than order-`p` unitaries, so they are genuine
`±1`-observables, and `(τ^W(a))² = 1` is where the paper needs `(σ^W(a))^p = I`.

**One matrix, not an iterated Kronecker product.** `(C^q)^{⊗ n}` is presented as
`Matrix (n → F) (n → F) C`: the basis of the `n`-fold tensor power is indexed by the functions
`n → F`, which *is* `F_q^n`. So `τ^W(a)` is a single matrix and the `n`-register statements are
the one-register statements with no associativity bookkeeping. The index type `n` is an arbitrary
finite type rather than `Fin n`, which is what lets the Pauli basis test use it at
`n = (Fin m → Bool)`, the indexing `MIPRE.LowDegree` already uses for `F_q^M` with `M = 2^m`.

## What is here

`wX`, `wZ`, the group laws, self-adjointness, involutivity, unitarity, and the twisted
commutation `wX_mul_wZ`. Then the `Z`-eigenbasis projectors, the expansion of `wZ` in them, and
the Fourier inversion that recovers a projector from an average of operators --- the identity the
expansion stage's `E_r (-1)^{tr(ar)} Ŵ^r(u)` is an instance of. The `X` side and the maximally
entangled state come next; they go through the Fourier transform conjugating one family into the
other.
-/

noncomputable section

namespace MIPRE.Weyl

open Finset Matrix

/-! ## Characteristic two

`Algebra (ZMod 2) F` is the whole of the hypothesis: the algebra map from a field is injective,
so `F` has characteristic two, and every element is its own additive inverse. -/

section CharTwo

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*}

theorem two_eq_zero : (2 : F) = 0 := by
  have h : ((2 : ℕ) : F) = 0 := by
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    calc ((2 : ℕ) : F) = algebraMap (ZMod 2) F ((2 : ℕ) : ZMod 2) := (map_natCast _ 2).symm
      _ = 0 := by rw [h2, map_zero]
  simpa using h

theorem add_self (x : F) : x + x = 0 := by
  rw [← two_mul, two_eq_zero, zero_mul]

theorem add_add_cancel (x y : F) : x + y + y = x := by
  rw [add_assoc, add_self, add_zero]

theorem add_self_vec (a : n → F) : a + a = 0 := by
  funext l; exact add_self (a l)

theorem add_add_cancel_vec (a b : n → F) : a + b + b = a := by
  funext l; exact add_add_cancel (a l) (b l)

/-- In characteristic two a sum vanishes exactly when the two summands agree. -/
theorem add_eq_zero_iff (x y : F) : x + y = 0 ↔ x = y := by
  refine ⟨fun h => ?_, fun h => by rw [h, add_self]⟩
  calc x = x + y + y := (add_add_cancel x y).symm
    _ = y := by rw [h, zero_add]

theorem add_eq_zero_iff_vec (a b : n → F) : a + b = 0 ↔ a = b := by
  refine ⟨fun h => funext fun l => (add_eq_zero_iff (a l) (b l)).mp (congrFun h l),
    fun h => by rw [h, add_self_vec]⟩

end CharTwo

/-! ## The bilinear form

`trDot a b = tr_{q → 2}(a · b)`, the `F_2`-valued form the phases are built from. It is the
symmetric bilinear form that decides commutation, and `trDotL` is it as a linear functional,
which is the shape `card_filter_ker_mul'` consumes. -/

section Form

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*} [Fintype n]

/-- `tr_{q → 2}(a · b)` for `a, b ∈ F_q^n`. -/
def trDot (a b : n → F) : ZMod 2 := Algebra.trace (ZMod 2) F (∑ l, a l * b l)

theorem trDot_comm (a b : n → F) : trDot a b = trDot b a := by
  rw [trDot, trDot, Finset.sum_congr rfl fun l _ => mul_comm (a l) (b l)]

@[simp] theorem trDot_zero_left (b : n → F) : trDot (0 : n → F) b = 0 := by
  simp [trDot]

@[simp] theorem trDot_zero_right (a : n → F) : trDot a (0 : n → F) = 0 := by
  simp [trDot]

theorem trDot_add_left (a a' b : n → F) : trDot (a + a') b = trDot a b + trDot a' b := by
  rw [trDot, trDot, trDot, ← map_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by simp [add_mul]

theorem trDot_add_right (a b b' : n → F) : trDot a (b + b') = trDot a b + trDot a b' := by
  rw [trDot_comm, trDot_add_left, trDot_comm b a, trDot_comm b' a]

/-- The form against a fixed `b`, as an `F_2`-linear functional. -/
def trDotL (b : n → F) : (n → F) →ₗ[ZMod 2] ZMod 2 where
  toFun a := trDot a b
  map_add' a a' := trDot_add_left a a' b
  map_smul' c a := by
    rcases (show c = 0 ∨ c = 1 from by revert c; decide) with rfl | rfl
    · simp
    · simp

@[simp] theorem trDotL_apply (b a : n → F) : trDotL b a = trDot a b := rfl

end Form

section Operators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The operators

The section's variables are what `Matrix (n → F) (n → F) ℂ` needs in order to exist at all ---
`DecidableEq (n → F)` for the diagonal and the identity, `Fintype (n → F)` for a matrix product ---
so the `rfl`-level lemmas below do not each use all of them. The linter is silenced for the
section rather than `omit`-ed a dozen times. -/

set_option linter.unusedSectionVars false

/-- **The `X`-type Weyl operator**: the shift of the computational basis by `a`. -/
def wX (a : n → F) : Matrix (n → F) (n → F) ℂ :=
  Matrix.of fun j i => if j = i + a then 1 else 0

/-- **The `Z`-type Weyl operator**: diagonal, with the sign `(-1)^{tr(b · i)}`. -/
def wZ (b : n → F) : Matrix (n → F) (n → F) ℂ :=
  Matrix.diagonal fun i => sgn (trDot b i)

@[simp] theorem wX_apply (a : n → F) (j i : n → F) :
    wX a j i = if j = i + a then 1 else 0 := rfl

@[simp] theorem wZ_apply (b : n → F) (j i : n → F) :
    wZ b j i = if j = i then sgn (trDot b i) else 0 := by
  rw [wZ, Matrix.diagonal_apply]
  split_ifs with h
  · rw [h]
  · rfl

/-! ### The group laws -/

@[simp] theorem wX_zero : wX (0 : n → F) = 1 := by
  ext j i
  rw [wX_apply, add_zero, Matrix.one_apply]

@[simp] theorem wZ_zero : wZ (0 : n → F) = 1 := by
  ext j i
  rw [wZ_apply, trDot_zero_left, sgn_zero, Matrix.one_apply]

theorem wX_mul_wX (a a' : n → F) : wX a * wX a' = wX (a + a') := by
  ext j i
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (i + a') (fun k _ hk => by
      rw [show wX a' k i = 0 from by rw [wX_apply, if_neg hk], mul_zero])
    fun h => absurd (Finset.mem_univ _) h]
  rw [wX_apply, wX_apply, if_pos rfl, mul_one, wX_apply]
  congr 1
  rw [add_comm a a', add_assoc]

theorem wZ_mul_wZ (b b' : n → F) : wZ b * wZ b' = wZ (b + b') := by
  rw [wZ, wZ, wZ, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [trDot_add_left, sgn_add]

@[simp] theorem wX_mul_self (a : n → F) : wX a * wX a = 1 := by
  rw [wX_mul_wX, add_self_vec, wX_zero]

@[simp] theorem wZ_mul_self (b : n → F) : wZ b * wZ b = 1 := by
  rw [wZ_mul_wZ, add_self_vec, wZ_zero]

/-! ### Self-adjointness and unitarity -/

@[simp] theorem wX_conjTranspose (a : n → F) : (wX a)ᴴ = wX a := by
  ext j i
  rw [Matrix.conjTranspose_apply, wX_apply, wX_apply]
  by_cases h : j = i + a
  · rw [if_pos h, if_pos (by rw [h, add_add_cancel_vec]), star_one]
  · rw [if_neg h, if_neg (fun hh : i = j + a => h (by rw [hh, add_add_cancel_vec])), star_zero]

@[simp] theorem wZ_conjTranspose (b : n → F) : (wZ b)ᴴ = wZ b := by
  ext j i
  rw [Matrix.conjTranspose_apply, wZ_apply, wZ_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, h, star_sgn]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem wX_isUnitary (a : n → F) : (wX a)ᴴ * wX a = 1 := by
  rw [wX_conjTranspose, wX_mul_self]

theorem wZ_isUnitary (b : n → F) : (wZ b)ᴴ * wZ b = 1 := by
  rw [wZ_conjTranspose, wZ_mul_self]

/-! ### Within a family the operators commute -/

theorem wX_comm (a a' : n → F) : wX a * wX a' = wX a' * wX a := by
  rw [wX_mul_wX, wX_mul_wX, add_comm]

theorem wZ_comm (b b' : n → F) : wZ b * wZ b' = wZ b' * wZ b := by
  rw [wZ_mul_wZ, wZ_mul_wZ, add_comm]

/-! ### The twisted commutation relation

The paper's `eq:twisted-fq`. In characteristic two the phase `ω^{-tr(a·b)}` is `(-1)^{tr(a·b)}`
and there is no sign to track on the exponent. -/

/-- **`τ^X(a) τ^Z(b) = (-1)^{tr(a · b)} τ^Z(b) τ^X(a)`.** -/
theorem wX_mul_wZ (a b : n → F) :
    wX a * wZ b = sgn (trDot a b) • (wZ b * wX a) := by
  ext j i
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.mul_apply]
  -- the left product picks out `k = i`, the right one `k = j`
  rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [show wZ b k i = 0 from by rw [wZ_apply, if_neg hk], mul_zero])
    fun h => absurd (Finset.mem_univ _) h]
  rw [Finset.sum_eq_single j (fun k _ hk => by
      rw [show wZ b j k = 0 from by rw [wZ_apply, if_neg (Ne.symm hk)], zero_mul])
    fun h => absurd (Finset.mem_univ _) h]
  rw [wZ_apply, if_pos rfl, wZ_apply, if_pos rfl, smul_eq_mul, wX_apply]
  by_cases h : j = i + a
  · rw [if_pos h, one_mul, mul_one, h, trDot_add_right, sgn_add, trDot_comm a b,
      mul_comm (sgn (trDot b i)) (sgn (trDot b a)), ← mul_assoc, sgn_mul_self, one_mul]
  · rw [if_neg h, zero_mul, mul_zero, mul_zero]

/-- The anticommuting case: when the form is nonzero the two operators anticommute. -/
theorem wX_mul_wZ_of_ne (a b : n → F) (h : trDot a b = 1) :
    wX a * wZ b = -(wZ b * wX a) := by
  rw [wX_mul_wZ, h, sgn_one, neg_one_smul]

/-- The commuting case. -/
theorem wX_mul_wZ_of_eq (a b : n → F) (h : trDot a b = 0) :
    wX a * wZ b = wZ b * wX a := by
  rw [wX_mul_wZ, h, sgn_zero, one_smul]

/-! ## The cancellation lemma

The paper's `lem:cancellation` (Fact 3.2 of `NW19`) in the case that matters here: the character
`a ↦ (-1)^{tr(a · c)}` of `F_q^n` is trivial exactly when `c = 0`, and a nontrivial character sums
to zero. Its `\cnote` warns that the ambient space must be a subspace over the *base* field; here
it is the whole of `F_q^n` over `F_2`, so the hypothesis is met with nothing to check.

The count comes from `card_filter_ker_mul'`, which says the kernel of a nonzero `F_2`-functional
has index two --- exactly half the vectors give each sign, so they cancel. -/

theorem trDotL_ne_zero {c : n → F} (hc : c ≠ 0) : trDotL c ≠ 0 := by
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hc
  -- the trace is surjective, so some `x` has `tr(x) = 1`; put it in coordinate `l`, scaled
  obtain ⟨x, hx⟩ := Algebra.trace_surjective (ZMod 2) F 1
  intro h
  have : trDot (Pi.single l (x / c l)) c = 0 := by
    rw [← trDotL_apply c, h, LinearMap.zero_apply]
  rw [trDot, Finset.sum_eq_single l (fun k _ hk => by
      rw [Pi.single_eq_of_ne hk, zero_mul]) fun hmem => absurd (Finset.mem_univ l) hmem,
    Pi.single_eq_same, div_mul_cancel₀ _ hl, hx] at this
  exact one_ne_zero this

/-- **A nontrivial sign character sums to zero.** -/
theorem sum_sgn_trDot {c : n → F} (hc : c ≠ 0) :
    ∑ a : n → F, sgn (trDot a c) = 0 := by
  classical
  have hker := MIPRE.LowDegree.card_filter_ker_mul' (trDotL c) (trDotL_ne_zero hc)
  rw [ZMod.card] at hker
  have heq : #{r ∈ (univ : Finset (n → F)) | trDotL c r = 0}
      = #{a ∈ (univ : Finset (n → F)) | trDot a c = 0} := by congr 1
  rw [heq] at hker
  have hsplit : #{a ∈ (univ : Finset (n → F)) | trDot a c = 0}
      + #{a ∈ (univ : Finset (n → F)) | ¬ trDot a c = 0} = Fintype.card (n → F) := by
    rw [← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hcompl : #{a ∈ (univ : Finset (n → F)) | ¬ trDot a c = 0}
      = #{a ∈ (univ : Finset (n → F)) | trDot a c = 0} := by omega
  have hone : ∀ x : ZMod 2, ¬ x = 0 → x = 1 := by decide
  have h0 : ∑ a ∈ {a ∈ (univ : Finset (n → F)) | trDot a c = 0}, sgn (trDot a c)
      = (#{a ∈ (univ : Finset (n → F)) | trDot a c = 0} : ℂ) := by
    rw [Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2, sgn_zero],
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : ∑ a ∈ {a ∈ (univ : Finset (n → F)) | ¬ trDot a c = 0}, sgn (trDot a c)
      = -(#{a ∈ (univ : Finset (n → F)) | trDot a c = 0} : ℂ) := by
    rw [Finset.sum_congr rfl fun a ha => by
        rw [hone _ (Finset.mem_filter.mp ha).2, sgn_one],
      Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one, hcompl]
  rw [← Finset.sum_filter_add_sum_filter_not (univ : Finset (n → F)) fun a => trDot a c = 0,
    h0, h1]
  ring

/-- The trivial character sums to the dimension of the space. -/
theorem sum_sgn_trDot_zero :
    ∑ b : n → F, sgn (trDot b (0 : n → F)) = (Fintype.card (n → F) : ℂ) := by
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => by rw [trDot_zero_right, sgn_zero],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-! ## The `Z`-eigenbasis projectors, and the Fourier inversion

`zProj c` projects onto the computational basis vector `c`, and `wZ` expands in them with the
sign coefficients (`eq:pauli-obs-proj`). The inversion `eq:pauli-inversion-0` recovers a
projector from an average of operators; it is the identity `E_r (-1)^{tr(ar)} Ŵ^r(u)` of the
expansion stage, with the average over a *line* `r ↦ r · v` rather than over the whole space. -/

/-- The rank-one projector onto the computational basis vector `c`. -/
def zProj (c : n → F) : Matrix (n → F) (n → F) ℂ :=
  Matrix.diagonal fun i => if i = c then 1 else 0

@[simp] theorem zProj_apply (c j i : n → F) :
    zProj c j i = if j = i then (if i = c then 1 else 0) else 0 := by
  by_cases h : j = i
  · subst h
    rw [zProj, Matrix.diagonal_apply_eq, if_pos rfl]
  · rw [zProj, Matrix.diagonal_apply_ne _ h, if_neg h]

theorem sum_zProj : ∑ c : n → F, zProj (F := F) (n := n) c = 1 := by
  ext j i
  rw [Matrix.sum_apply, Matrix.one_apply]
  by_cases h : j = i
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single j (fun c _ hc => by
        rw [zProj_apply, if_pos rfl, if_neg fun hh : j = c => hc hh.symm])
      fun hmem => absurd (Finset.mem_univ j) hmem,
      zProj_apply, if_pos rfl, if_pos rfl]
  · rw [if_neg h, Finset.sum_eq_zero fun c _ => by rw [zProj_apply, if_neg h]]

/-- **`wZ` expands in the computational-basis projectors** with the sign coefficients: the
paper's `eq:pauli-obs-proj`. -/
theorem wZ_eq_sum_zProj (b : n → F) :
    wZ b = ∑ c : n → F, sgn (trDot b c) • zProj c := by
  ext j i
  rw [wZ_apply, Matrix.sum_apply]
  by_cases h : j = i
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single j (fun c _ hc => by
        rw [Matrix.smul_apply, zProj_apply, if_pos rfl,
          if_neg fun hh : j = c => hc hh.symm, smul_zero])
      fun hmem => absurd (Finset.mem_univ j) hmem,
      Matrix.smul_apply, zProj_apply, if_pos rfl, if_pos rfl, smul_eq_mul, mul_one]
  · rw [if_neg h, Finset.sum_eq_zero fun c _ => by
      rw [Matrix.smul_apply, zProj_apply, if_neg h, smul_zero]]

/-- **The Fourier inversion**, the paper's `eq:pauli-inversion-0`: averaging `wZ` against the
conjugate character recovers the projector onto a single computational basis vector. -/
theorem sum_sgn_smul_wZ (c : n → F) :
    (Fintype.card (n → F) : ℂ)⁻¹ • ∑ b : n → F, sgn (trDot b c) • wZ b = zProj c := by
  classical
  have hcard : (Fintype.card (n → F) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card (n → F) := Fintype.card_pos
    exact_mod_cast this.ne'
  -- expand each `wZ b` and exchange the two sums
  have hexp : ∑ b : n → F, sgn (trDot b c) • wZ b
      = ∑ c' : n → F, (∑ b : n → F, sgn (trDot b (c + c'))) • zProj c' := by
    rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => by
      rw [wZ_eq_sum_zProj b, Finset.smul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => by
      rw [smul_smul, ← sgn_add, ← trDot_add_right], ← Finset.sum_smul]
  rw [hexp]
  -- every term but `c' = c` cancels
  rw [Finset.sum_eq_single c (fun c' _ hc' => by
      rw [sum_sgn_trDot (c := c + c')
        fun h => hc' (((add_eq_zero_iff_vec c c').mp h).symm), zero_smul])
    fun hmem => absurd (Finset.mem_univ c) hmem]
  rw [add_self_vec, sum_sgn_trDot_zero, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-! ## The spectral projectors, once for both families

Everything the appendix does with the eigenbasis projectors of one family uses only three facts
about it: it represents the additive group of `F_q^n`, its operators are self-adjoint, and the
identity sits at `0`. `IsWeylFamily` is those three, `proj` is the Fourier average that builds the
projectors out of them, and the spectral statements are then proved once. `wZ` is one instance and
`wX` the other, so the paper's Fourier transform conjugating one family into the other is not
needed to reach the `X`-side projectors --- worth avoiding, since that transform carries a
`q^{-1/2}` and would put a square root into matrix entries. -/

/-- A family of self-adjoint operators indexed by `F_q^n` representing its additive group. The
two Weyl families are the instances, and the spectral theory needs nothing else. -/
structure IsWeylFamily (w : (n → F) → Matrix (n → F) (n → F) ℂ) : Prop where
  /-- The family is a homomorphism from the additive group. -/
  map_add : ∀ a a', w (a + a') = w a * w a'
  /-- The identity sits at `0`. -/
  map_zero : w 0 = 1
  /-- Every operator is self-adjoint. -/
  selfAdjoint : ∀ a, (w a)ᴴ = w a

theorem isWeylFamily_wZ : IsWeylFamily (wZ (F := F) (n := n)) where
  map_add a a' := (wZ_mul_wZ a a').symm
  map_zero := wZ_zero
  selfAdjoint := wZ_conjTranspose

theorem isWeylFamily_wX : IsWeylFamily (wX (F := F) (n := n)) where
  map_add a a' := (wX_mul_wX a a').symm
  map_zero := wX_zero
  selfAdjoint := wX_conjTranspose

theorem card_ne_zero : (Fintype.card (n → F) : ℂ) ≠ 0 := by
  have : 0 < Fintype.card (n → F) := Fintype.card_pos
  exact_mod_cast this.ne'

/-- **The spectral projector** of a Weyl family at the eigenvalue pattern `e`: the Fourier average
of the family against the character of `e`. For `wZ` it is `zProj e` (`proj_wZ`); for `wX` it is
the projector onto the `X`-eigenbasis vector the paper writes `|e_X⟩`. -/
def proj (w : (n → F) → Matrix (n → F) (n → F) ℂ) (e : n → F) :
    Matrix (n → F) (n → F) ℂ :=
  (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • w a

/-- The defining Fourier average, as a rewrite. -/
theorem proj_def (w : (n → F) → Matrix (n → F) (n → F) ℂ) (e : n → F) :
    proj w e = (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • w a := rfl

/-- The `Z`-family's spectral projectors are the computational-basis ones. -/
theorem proj_wZ (c : n → F) : proj (wZ (F := F) (n := n)) c = zProj c :=
  sum_sgn_smul_wZ c

variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}

/-- **A projector absorbs its own family's operators**, up to the sign: one reindexing. -/
theorem proj_mul (hw : IsWeylFamily w) (e a : n → F) :
    proj w e * w a = sgn (trDot a e) • proj w e := by
  classical
  rw [proj_def w e, Matrix.smul_mul, Finset.sum_mul,
    Finset.sum_congr rfl fun b (_ : b ∈ univ) => by rw [Matrix.smul_mul, ← hw.map_add],
    Fintype.sum_equiv (Equiv.addRight a) _ (fun c => sgn (trDot (c + a) e) • w c) fun b => by
      rw [Equiv.coe_addRight, add_add_cancel_vec],
    Finset.sum_congr rfl fun c (_ : c ∈ univ) => by
      rw [trDot_add_left, sgn_add, mul_comm, ← smul_smul],
    ← Finset.smul_sum, smul_comm, ← proj_def w e]

/-- **The projectors are mutually orthogonal idempotents.** -/
theorem proj_mul_proj (hw : IsWeylFamily w) (e e' : n → F) :
    proj w e * proj w e' = if e = e' then proj w e else 0 := by
  classical
  rw [proj_def w e', Matrix.mul_smul, Finset.mul_sum,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [Matrix.mul_smul, proj_mul hw e a, smul_smul, ← sgn_add, ← trDot_add_right],
    ← Finset.sum_smul]
  by_cases h : e = e'
  · subst h
    rw [if_pos rfl, add_self_vec,
      Finset.sum_congr rfl fun a (_ : a ∈ univ) => by rw [trDot_zero_right, sgn_zero],
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_smul,
      inv_mul_cancel₀ card_ne_zero, one_smul]
  · rw [if_neg h, sum_sgn_trDot (c := e' + e) fun hh =>
      h (((add_eq_zero_iff_vec e' e).mp hh).symm), zero_smul, smul_zero]

/-- **The projectors of a Weyl family sum to the identity.** -/
theorem sum_proj (hw : IsWeylFamily w) : ∑ e : n → F, proj w e = 1 := by
  classical
  simp only [proj_def]
  rw [← Finset.smul_sum, Finset.sum_comm,
    Finset.sum_eq_single (0 : n → F) (fun a _ ha => by
      rw [← Finset.sum_smul, Finset.sum_congr rfl fun e (_ : e ∈ univ) => by
        rw [trDot_comm a e], sum_sgn_trDot ha, zero_smul])
      fun hmem => absurd (Finset.mem_univ (0 : n → F)) hmem,
    hw.map_zero, ← Finset.sum_smul,
    Finset.sum_congr rfl fun e (_ : e ∈ univ) => by rw [trDot_zero_left, sgn_zero],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_smul,
    inv_mul_cancel₀ card_ne_zero, one_smul]

/-- **A Weyl operator expands in its own projectors** with the sign coefficients: the paper's
`eq:pauli-obs-proj` for either family.

The group law is *not* used: this is pure Fourier inversion on the index group, and holds for any
family at all. What the group law buys is that the projectors are then mutually orthogonal
(`proj_mul_proj`), which is what makes them a measurement. -/
theorem eq_sum_proj (a : n → F) :
    w a = ∑ e : n → F, sgn (trDot a e) • proj w e := by
  classical
  simp only [proj_def]
  rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => by
      rw [smul_comm, Finset.smul_sum,
        Finset.sum_congr rfl fun b (_ : b ∈ univ) => by
          rw [smul_smul, ← sgn_add, ← trDot_add_left]],
    ← Finset.smul_sum, Finset.sum_comm,
    Finset.sum_eq_single a (fun b _ hb => by
      rw [← Finset.sum_smul,
        Finset.sum_congr rfl fun e (_ : e ∈ univ) => by rw [trDot_comm (a + b) e],
        sum_sgn_trDot (c := a + b) fun hh => hb (((add_eq_zero_iff_vec a b).mp hh).symm),
        zero_smul])
      fun hmem => absurd (Finset.mem_univ a) hmem,
    add_self_vec, ← Finset.sum_smul,
    Finset.sum_congr rfl fun e (_ : e ∈ univ) => by rw [trDot_zero_left, sgn_zero],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_smul,
    inv_mul_cancel₀ card_ne_zero, one_smul]

/-- The projectors are self-adjoint. -/
theorem proj_conjTranspose (hw : IsWeylFamily w) (e : n → F) : (proj w e)ᴴ = proj w e := by
  classical
  rw [proj_def w e, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [Matrix.conjTranspose_smul, hw.selfAdjoint a, star_sgn]]
  congr 1
  simp

/-- **The `X`-side projectors**, the paper's `|e_X⟩⟨e_X|`. -/
def xProj (e : n → F) : Matrix (n → F) (n → F) ℂ := proj (wX (F := F) (n := n)) e

theorem sum_xProj : ∑ e : n → F, xProj (F := F) e = 1 := sum_proj isWeylFamily_wX

theorem wX_eq_sum_xProj (a : n → F) :
    wX a = ∑ e : n → F, sgn (trDot a e) • xProj (F := F) e :=
  eq_sum_proj a

theorem xProj_mul_xProj (e e' : n → F) :
    xProj (F := F) e * xProj e' = if e = e' then xProj e else 0 :=
  proj_mul_proj isWeylFamily_wX e e'

theorem xProj_conjTranspose (e : n → F) : (xProj (F := F) e)ᴴ = xProj e :=
  proj_conjTranspose isWeylFamily_wX e

/-! ## The syndrome projectors

The expansion stage does not average the Weyl family over the whole of `F_q^n`: it averages over
the *line* `r ↦ r · v` for a fixed `v ∈ F_q^n`, against the character of a field element `a`. What
comes out is the projector onto the eigenvectors whose `F_q`-valued pairing with `v` is `a` --- the
paper's `τ^{W,u}_a = τ^W_{[g_·(u) = a]}` of `eq:qld-point-obs-def`, at `v = ind_m(u)`. -/

/-- The `F_q`-valued pairing, before the trace. -/
def dotF (a b : n → F) : F := ∑ l, a l * b l

theorem dotF_comm (a b : n → F) : dotF a b = dotF b a :=
  Finset.sum_congr rfl fun l _ => mul_comm (a l) (b l)

theorem trDot_eq_trace_dotF (a b : n → F) :
    trDot a b = Algebra.trace (ZMod 2) F (dotF a b) := rfl

/-- Scaling one argument of the pairing pulls the scalar out. -/
theorem trDot_smul (r : F) (v e : n → F) :
    trDot (r • v) e = Algebra.trace (ZMod 2) F (r * dotF v e) := by
  rw [trDot, dotF, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The trace against a fixed field element, as an `F_2`-linear functional on `F_q`. -/
def trMulL (x : F) : F →ₗ[ZMod 2] ZMod 2 where
  toFun r := Algebra.trace (ZMod 2) F (r * x)
  map_add' r r' := by rw [add_mul, map_add]
  map_smul' c r := by
    rcases (show c = 0 ∨ c = 1 from by revert c; decide) with rfl | rfl
    · simp
    · simp

theorem trMulL_ne_zero {x : F} (hx : x ≠ 0) : trMulL x ≠ 0 := by
  obtain ⟨y, hy⟩ := Algebra.trace_surjective (ZMod 2) F 1
  intro h
  have h0 : Algebra.trace (ZMod 2) F ((y / x) * x) = 0 := by
    have := congrFun (congrArg (fun t : F →ₗ[ZMod 2] ZMod 2 => t.toFun) h) (y / x)
    simpa [trMulL] using this
  rw [div_mul_cancel₀ _ hx, hy] at h0
  exact one_ne_zero h0

/-- **A nonzero sign character of a finite `F_2`-space sums to zero.** `sum_sgn_trDot` and
`sum_sgn_trMul` are its two instances; the content is the index-two kernel of
`card_filter_ker_mul'`. -/
theorem sum_sgn_linear {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [DecidableEq V] (τ : V →ₗ[ZMod 2] ZMod 2) (hτ : τ ≠ 0) : ∑ v : V, sgn (τ v) = 0 := by
  classical
  have hker := MIPRE.LowDegree.card_filter_ker_mul' τ hτ
  rw [ZMod.card] at hker
  have hsplit : #{v ∈ (univ : Finset V) | τ v = 0} + #{v ∈ (univ : Finset V) | ¬ τ v = 0}
      = Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hcompl : #{v ∈ (univ : Finset V) | ¬ τ v = 0} = #{v ∈ (univ : Finset V) | τ v = 0} := by
    omega
  have hone : ∀ x : ZMod 2, ¬ x = 0 → x = 1 := by decide
  have h0 : ∑ v ∈ {v ∈ (univ : Finset V) | τ v = 0}, sgn (τ v)
      = (#{v ∈ (univ : Finset V) | τ v = 0} : ℂ) := by
    rw [Finset.sum_congr rfl fun v hv => by rw [(Finset.mem_filter.mp hv).2, sgn_zero],
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : ∑ v ∈ {v ∈ (univ : Finset V) | ¬ τ v = 0}, sgn (τ v)
      = -(#{v ∈ (univ : Finset V) | τ v = 0} : ℂ) := by
    rw [Finset.sum_congr rfl fun v hv => by rw [hone _ (Finset.mem_filter.mp hv).2, sgn_one],
      Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one, hcompl]
  rw [← Finset.sum_filter_add_sum_filter_not (univ : Finset V) fun v => τ v = 0, h0, h1]
  ring

/-- The one-field cancellation: the `r`-average of the sign of `tr(r x)` vanishes unless `x = 0`. -/
theorem sum_sgn_trMul {x : F} (hx : x ≠ 0) :
    ∑ r : F, sgn (Algebra.trace (ZMod 2) F (r * x)) = 0 :=
  sum_sgn_linear (trMulL x) (trMulL_ne_zero hx)

theorem sum_sgn_trMul_zero :
    ∑ r : F, sgn (Algebra.trace (ZMod 2) F (r * (0 : F))) = (Fintype.card F : ℂ) := by
  rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by rw [mul_zero, map_zero, sgn_zero],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **The syndrome projector**: onto the eigenvectors whose pairing with `v` is `a`. The paper's
`eq:qld-point-obs-def`. -/
def syn (w : (n → F) → Matrix (n → F) (n → F) ℂ) (v : n → F) (a : F) :
    Matrix (n → F) (n → F) ℂ :=
  ∑ e ∈ univ.filter fun e => dotF e v = a, proj w e

/-- **The identity the expansion stage calls.** Averaging the family along the line `r ↦ r · v`
against the character of `a` gives the syndrome projector: the paper's
`E_r (-1)^{tr(ar)} \qp^W(r \cdot v) = \qp^W_{[\cdot v = a]}`. As with `eq_sum_proj`, the group law
is not used. -/
theorem sum_sgn_smul_line (v : n → F) (a : F) :
    (Fintype.card F : ℂ)⁻¹ • ∑ r : F, sgn (Algebra.trace (ZMod 2) F (a * r)) • w (r • v)
      = syn w v a := by
  classical
  have hcardF : (Fintype.card F : ℂ) ≠ 0 := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this.ne'
  -- expand each operator on the line in the projectors, then exchange the two sums
  rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by
      rw [eq_sum_proj (w := w) (r • v), Finset.smul_sum,
        Finset.sum_congr rfl fun e (_ : e ∈ univ) => by
          rw [smul_smul, ← sgn_add, trDot_smul, ← map_add, mul_comm a r, ← mul_add,
            dotF_comm v e]],
    Finset.sum_comm, Finset.smul_sum]
  -- each `e` contributes only when its syndrome is `a`
  rw [syn, ← Finset.sum_filter_add_sum_filter_not (univ : Finset (n → F))
    fun e => dotF e v = a]
  rw [show ∑ e ∈ {e ∈ (univ : Finset (n → F)) | ¬ dotF e v = a},
        (Fintype.card F : ℂ)⁻¹ • ∑ r : F, sgn (Algebra.trace (ZMod 2) F (r * (a + dotF e v)))
          • proj w e = 0 from
      Finset.sum_eq_zero fun e he => by
        rw [← Finset.sum_smul, sum_sgn_trMul (x := a + dotF e v) fun hh =>
          (Finset.mem_filter.mp he).2 (((add_eq_zero_iff a (dotF e v)).mp hh).symm),
          zero_smul, smul_zero], add_zero]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [show a + dotF e v = 0 from by
      rw [(Finset.mem_filter.mp he).2, add_self],
    ← Finset.sum_smul, sum_sgn_trMul_zero, smul_smul, inv_mul_cancel₀ hcardF, one_smul]

end Operators

end MIPRE.Weyl

end
