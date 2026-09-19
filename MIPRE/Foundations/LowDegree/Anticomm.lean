/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.LowDegree.SchwartzZippel
import MIPRE.Foundations.LowDegree.Encoding
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic

/-!
# When is a Pauli-test question tuple anticommuting?

The Pauli basis test samples `ω = (u_X, u_Z, r_X, r_Z)` and the two Pauli operators it asks
about commute or anticommute according to whether

`γ(ω) = tr_{q → 2} \bigl( (r_X · ind_m(u_X)) · (r_Z · ind_m(u_Z)) \bigr)`

vanishes. The paper's `fact:omega-anticomm-prob` says each case has probability at least
`(1 - 3md/q)/2`; this file is that fact.

`ind_m(x) ∈ 𝔽_q^{2^m}` is the vector of the subcube indicator polynomials of
`MIPRE/Foundations/LowDegree/Encoding.lean` evaluated at an *arbitrary* point `x`, and the
dot product of two of them is one low-degree encoding evaluated at the other point
(`indPair_eq_eval`). So the fact is Schwartz--Zippel --- the encoding is a nonzero polynomial,
because `ind_m(x)` is never the zero vector (`sum_indVec`, whose value is `1`) --- together with
the count of `r` in the kernel of a nonzero `𝔽`-linear functional (`card_filter_ker_mul`).

Two departures from the paper, both recorded in the blueprint's comments on the fact:

* **the wasteful factor is dropped.** The paper states
  `(1 - q^{-m})(1 - q^{-1})(1 - md/q)/2`, whose first factor came from a case distinction on
  `u_X = 0` that its own `\cnote` then removes as vacuous. The bound proved here is
  `(1 - (m+1)/q)/2`, which is sharper than the paper's final `(1 - 3md/q)/2` and needs no such
  factor.
* **individual degree, not total degree.** The low-degree encoding is multilinear, so the
  Schwartz--Zippel step costs `m/q` rather than the `md/q` the paper spends. The paper's form is
  recovered in `prob_anticommuting_ge` for `1 ≤ d`.
-/

noncomputable section

namespace MIPRE.LowDegree

open Finset MvPolynomial

/-! ## The indicator vector at an arbitrary point -/

section IndVec

variable {K : Type*} [CommRing K] {m : ℕ}

/-- `ind_m(x)`, the vector of the subcube indicator polynomials evaluated at `x`. For a subcube
point this is the standard basis vector at that point (`eval_ind`); the definition is what the
Pauli basis test uses at a general `x ∈ 𝔽_q^m`. -/
def indVec (x : Fin m → K) : (Fin m → Bool) → K := fun y => eval x (ind y)

theorem indVec_apply (x : Fin m → K) (y : Fin m → Bool) :
    indVec x y = ∏ i, if y i then x i else 1 - x i := by
  rw [indVec, ind, map_prod]
  exact Finset.prod_congr rfl fun i _ => by cases y i <;> simp

/-- **`ind_m(x)` has coordinate sum `1`**, hence is never the zero vector: the sum telescopes to
`∏_i (x_i + (1 - x_i)) = 1`. This is the observation the paper's `\cnote` adds, and it is what
makes the case distinction on `u_X = 0` unnecessary. -/
theorem sum_indVec (x : Fin m → K) : ∑ y, indVec x y = 1 := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin m => (univ : Finset Bool))
    (fun (i : Fin m) (b : Bool) => if b then x i else 1 - x i)
  rw [Fintype.piFinset_univ] at h
  have hone : ∀ i : Fin m, (∑ b : Bool, if b then x i else 1 - x i) = 1 := fun _ => by simp
  rw [Finset.prod_congr rfl fun i (_ : i ∈ univ) => hone i, Finset.prod_const_one] at h
  rw [Finset.sum_congr rfl fun y (_ : y ∈ univ) => indVec_apply x y]
  exact h.symm

theorem indVec_ne_zero [Nontrivial K] (x : Fin m → K) : indVec x ≠ 0 := by
  intro h
  have := sum_indVec x
  rw [h] at this
  simp at this

/-- The dot product `ind_m(x) · ind_m(z)`, which is the `γ` of the Pauli basis test up to the
scalars `r_X r_Z` and the trace. -/
def indPair (x z : Fin m → K) : K := ∑ y, indVec x y * indVec z y

/-- **The pairing is one low-degree encoding evaluated at the other point.** This is the
identity the paper's proof opens with, and it is what puts Schwartz--Zippel in reach. -/
theorem indPair_eq_eval (x z : Fin m → K) : indPair x z = eval z (ldEnc (indVec x)) := by
  rw [indPair, ldEnc, map_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [map_mul, eval_C]; rfl

theorem ldEnc_indVec_ne_zero [Nontrivial K] (x : Fin m → K) : ldEnc (indVec x) ≠ 0 := by
  intro h
  refine indVec_ne_zero x (funext fun y => ?_)
  have := eval_ldEnc (indVec x) y
  rw [h] at this
  simpa using this.symm

end IndVec

/-! ## The kernel of a nonzero linear functional -/

section Ker

/-! The kernel-index count is about a finite `𝔽`-vector space, not about a field extension: the
proof uses only the module structure and a vector off the kernel. It is stated that way because
the Weyl operators of `MIPRE/Foundations/Weyl.lean` need it on `n → 𝔽`, where the phase
`(-1)^{tr(a · b)}` is summed over a whole register rather than over a single field element. The
field-extension form below is the instance `V = K`. -/

section Module

variable {F V : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup V] [Module F V]
  [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **A nonzero `𝔽`-linear functional on a finite `𝔽`-vector space has kernel of index `|𝔽|`.**
Every fibre is a translate of the kernel, and there are `|𝔽|` of them. -/
theorem card_filter_ker_mul' (τ : V →ₗ[F] F) (hτ : τ ≠ 0) :
    #{r ∈ (univ : Finset V) | τ r = 0} * Fintype.card F = Fintype.card V := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : V, τ v ≠ 0 := by
    by_contra h
    exact hτ (LinearMap.ext fun r => not_ne_iff.mp (fun hr => h ⟨r, hr⟩))
  -- every fibre has the same cardinality as the kernel
  have hfib : ∀ a : F, #{r ∈ (univ : Finset V) | τ r = a} = #{r ∈ (univ : Finset V) | τ r = 0} := by
    intro a
    refine Finset.card_bij' (fun r _ => r - (a / τ v) • v) (fun r _ => r + (a / τ v) • v)
      ?_ ?_ ?_ ?_ <;> intro r hr <;> simp only [Finset.mem_filter, Finset.mem_univ,
        true_and, map_sub, map_add, map_smul] at hr ⊢
    · rw [hr, smul_eq_mul, div_mul_cancel₀ _ hv, sub_self]
    · rw [hr, smul_eq_mul, div_mul_cancel₀ _ hv, zero_add]
    · rw [sub_add_cancel]
    · rw [add_sub_cancel_right]
  have hcard : Fintype.card V = ∑ a : F, #{r ∈ (univ : Finset V) | τ r = a} := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun r _ => Finset.mem_univ (τ r)
  rw [hcard, Finset.sum_congr rfl fun a (_ : a ∈ univ) => hfib a, Finset.sum_const,
    Finset.card_univ, mul_comm, smul_eq_mul]

end Module

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Fintype K]
  [DecidableEq K] [Algebra F K]

omit [DecidableEq K] in
/-- **A nonzero `𝔽`-linear functional has kernel of index `|𝔽|`.** Every fibre is a translate of
the kernel, and there are `|𝔽|` of them. -/
theorem card_filter_ker_mul (τ : K →ₗ[F] F) (hτ : τ ≠ 0) :
    #{r ∈ (univ : Finset K) | τ r = 0} * Fintype.card F = Fintype.card K := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : K, τ v ≠ 0 := by
    by_contra h
    exact hτ (LinearMap.ext fun r => not_ne_iff.mp (fun hr => h ⟨r, hr⟩))
  -- every fibre has the same cardinality as the kernel
  have hfib : ∀ a : F, #{r ∈ (univ : Finset K) | τ r = a} = #{r ∈ (univ : Finset K) | τ r = 0} := by
    intro a
    refine Finset.card_bij' (fun r _ => r - (a / τ v) • v) (fun r _ => r + (a / τ v) • v)
      ?_ ?_ ?_ ?_ <;> intro r hr <;> simp only [Finset.mem_filter, Finset.mem_univ,
        true_and, map_sub, map_add, map_smul] at hr ⊢
    · rw [hr, smul_eq_mul, div_mul_cancel₀ _ hv, sub_self]
    · rw [hr, smul_eq_mul, div_mul_cancel₀ _ hv, zero_add]
    · rw [sub_add_cancel]
    · rw [add_sub_cancel_right]
  have hcard : Fintype.card K = ∑ a : F, #{r ∈ (univ : Finset K) | τ r = a} := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun r _ => Finset.mem_univ (τ r)
  rw [hcard, Finset.sum_congr rfl fun a (_ : a ∈ univ) => hfib a, Finset.sum_const,
    Finset.card_univ, mul_comm, smul_eq_mul]

variable [FiniteDimensional F K] [Algebra.IsSeparable F K]

omit [DecidableEq K] in
/-- The trace against a fixed nonzero element is a nonzero functional, so its kernel is again
of index `|𝔽|`. -/
theorem card_filter_trace_mul (c : K) (hc : c ≠ 0) :
    #{r ∈ (univ : Finset K) | Algebra.trace F K (c * r) = 0} * Fintype.card F = Fintype.card K := by
  classical
  set τ : K →ₗ[F] F := (Algebra.trace F K).comp (LinearMap.mulLeft F c) with hτdef
  have hτ : τ ≠ 0 := by
    obtain ⟨x, hx⟩ := Algebra.trace_surjective F K 1
    intro h
    have : τ (c⁻¹ * x) = 0 := by rw [h]; rfl
    rw [hτdef] at this
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at this
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, hx] at this
    exact one_ne_zero this
  rw [← card_filter_ker_mul τ hτ]
  congr 1

end Ker

/-! ## The fact -/

section Fact

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Fintype K]
  [DecidableEq K] [Algebra F K] [FiniteDimensional F K] [Algebra.IsSeparable F K] {m d : ℕ}

omit [DecidableEq K] in
/-- Over `𝔽₂`, exactly half the field is off the kernel. -/
theorem two_mul_card_filter_trace_ne (hF : Fintype.card F = 2) (c : K) (hc : c ≠ 0) :
    2 * #{r ∈ (univ : Finset K) | Algebra.trace F K (c * r) ≠ 0} = Fintype.card K := by
  classical
  have h := card_filter_trace_mul (F := F) c hc
  rw [hF] at h
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset K)) (p := fun r => Algebra.trace F K (c * r) = 0)
  rw [Finset.card_univ] at hsplit
  simp only [ne_eq]
  omega

/-- `γ(ω)`, the quantity of the Pauli basis test whose vanishing says that the two Pauli
operators of the tuple `ω = (u_X, u_Z, r_X, r_Z)` commute: the trace of the dot product of
`r_X · ind_m(u_X)` with `r_Z · ind_m(u_Z)`. -/
def acGamma (F : Type*) [Field F] [Algebra F K] (uX uZ : Fin m → K) (rX rZ : K) : F :=
  Algebra.trace F K (rX * rZ * indPair uX uZ)

/-- **The anticommuting tuples**, as a `Finset` of the sample space. -/
def acTuples (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra F K] (m : ℕ) :
    Finset ((Fin m → K) × (Fin m → K) × K × K) :=
  {ω ∈ univ | acGamma F ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 ≠ 0}

/-- **The commuting tuples.** -/
def cTuples (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra F K] (m : ℕ) :
    Finset ((Fin m → K) × (Fin m → K) × K × K) :=
  {ω ∈ univ | acGamma F ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = 0}

/-- At a nonzero pairing value, half the `(r_X, r_Z)` with `r_X ≠ 0` are anticommuting. -/
theorem two_mul_card_pair (hF : Fintype.card F = 2) (uX uZ : Fin m → K)
    (hp : indPair uX uZ ≠ 0) :
    2 * #{c ∈ (univ : Finset (K × K)) | acGamma F uX uZ c.1 c.2 ≠ 0}
      = (Fintype.card K - 1) * Fintype.card K := by
  classical
  have hstep : ∀ rX : K, 2 * #{rZ ∈ (univ : Finset K) | acGamma F uX uZ rX rZ ≠ 0}
      = if rX = 0 then 0 else Fintype.card K := by
    intro rX
    by_cases h0 : rX = 0
    · have hz : ∀ rZ : K, acGamma F uX uZ (0 : K) rZ = 0 := by
        intro rZ; rw [acGamma]; simp
      simp [h0, hz]
    · rw [if_neg h0]
      have hc : rX * indPair uX uZ ≠ 0 := mul_ne_zero h0 hp
      have := two_mul_card_filter_trace_ne (F := F) hF (rX * indPair uX uZ) hc
      rw [← this]
      congr 2
      refine Finset.filter_congr fun rZ _ => ?_
      rw [acGamma, mul_right_comm]
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.mul_sum]
  have h1 : ∀ rX : K, 2 * ∑ rZ : K, (if acGamma F uX uZ rX rZ ≠ 0 then 1 else 0)
      = if rX = 0 then 0 else Fintype.card K := by
    intro rX
    rw [← Finset.card_filter]
    exact hstep rX
  rw [Finset.sum_congr rfl fun rX (_ : rX ∈ univ) => h1 rX]
  have hswap : ∀ rX : K, (if rX = 0 then 0 else Fintype.card K)
      = if rX ≠ 0 then Fintype.card K else 0 := fun rX => (ite_not _ _ _).symm
  rw [Finset.sum_congr rfl fun rX (_ : rX ∈ univ) => hswap rX, ← Finset.sum_filter,
    Finset.sum_const, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
    Finset.card_univ, smul_eq_mul]

omit [DecidableEq K] [FiniteDimensional F K] [Algebra.IsSeparable F K] in
/-- The anticommuting count, one question pair at a time. -/
theorem card_acTuples_eq :
    (acTuples (K := K) F m).card
      = ∑ uX : Fin m → K, ∑ uZ : Fin m → K,
          #{c ∈ (univ : Finset (K × K)) | acGamma F uX uZ c.1 c.2 ≠ 0} := by
  classical
  rw [acTuples, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun uX _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun uZ _ => (Finset.card_filter _ _).symm

/-! ### The Schwartz--Zippel step -/

omit [FiniteDimensional F K] [Algebra.IsSeparable F K] in
/-- **The pairing vanishes at few `u_Z`.** `ind_m(u_X)` is a nonzero vector, so its low-degree
encoding is a nonzero *multilinear* polynomial and Schwartz--Zippel costs `m/q`, not `md/q`. -/
theorem card_indPair_eq_zero_mul_le (uX : Fin m → K) :
    (#{uZ ∈ (univ : Finset (Fin m → K)) | indPair uX uZ = 0} : ℝ) * Fintype.card K
      ≤ (m : ℝ) * (Fintype.card K : ℝ) ^ m := by
  classical
  have hQ : (0 : ℝ) < Fintype.card K := by
    exact_mod_cast Fintype.card_pos
  have hfilter : #{uZ ∈ (univ : Finset (Fin m → K)) | indPair uX uZ = 0}
      = (agree (ldEnc (indVec uX)) 0).card := by
    congr 1
    refine Finset.filter_congr fun uZ _ => ?_
    rw [indPair_eq_eval]
    simp
  have hsz := prob_agree_le_individualDegree (f := ldEnc (indVec uX)) (g := 0)
    (ldEnc_indVec_ne_zero uX) (d := 1) (degreeOf_ldEnc_le _) (fun i => by simp)
  rw [← hfilter] at hsz
  rw [div_le_div_iff₀ (by positivity) hQ] at hsz
  push_cast at hsz
  calc (#{uZ ∈ (univ : Finset (Fin m → K)) | indPair uX uZ = 0} : ℝ) * Fintype.card K
      ≤ (m : ℝ) * 1 * (Fintype.card K : ℝ) ^ m := hsz
    _ = (m : ℝ) * (Fintype.card K : ℝ) ^ m := by ring

/-! ### The two counts -/

omit [DecidableEq K] [FiniteDimensional F K] [Algebra.IsSeparable F K] in
/-- The anticommuting pairs `(r_X, r_Z)` are at least half of those with `r_X ≠ 0`, and the
pairing is nonzero for all but a `m/q` fraction of the `u_Z`. -/
theorem le_two_mul_card_acTuples (hF : Fintype.card F = 2) :
    ((Fintype.card K : ℝ) - 1) * ((Fintype.card K : ℝ) - m) * (Fintype.card K : ℝ) ^ (2 * m)
      ≤ 2 * ((acTuples (K := K) F m).card : ℝ) := by
  classical
  set Q : ℕ := Fintype.card K with hQdef
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hQ : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hQ1
  -- the natural-number count, one `u_X` at a time
  have hrow : ∀ uX : Fin m → K, (Q - 1) * Q * #{uZ ∈ (univ : Finset (Fin m → K)) |
      indPair uX uZ ≠ 0}
      ≤ ∑ uZ : Fin m → K, 2 * #{c ∈ (univ : Finset (K × K)) | acGamma F uX uZ c.1 c.2 ≠ 0} := by
    intro uX
    have hsub : ∑ uZ ∈ {uZ ∈ (univ : Finset (Fin m → K)) | indPair uX uZ ≠ 0},
        2 * #{c ∈ (univ : Finset (K × K)) | acGamma F uX uZ c.1 c.2 ≠ 0}
        ≤ ∑ uZ : Fin m → K,
            2 * #{c ∈ (univ : Finset (K × K)) | acGamma F uX uZ c.1 c.2 ≠ 0} :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    refine le_trans (le_of_eq ?_) hsub
    rw [Finset.sum_congr rfl fun uZ huZ => two_mul_card_pair hF uX uZ
      (by simpa using (Finset.mem_filter.mp huZ).2), Finset.sum_const, smul_eq_mul, mul_comm]
  -- sum over `u_X`, in the reals
  have hnat : (Q - 1) * Q * (∑ uX : Fin m → K, #{uZ ∈ (univ : Finset (Fin m → K)) |
      indPair uX uZ ≠ 0}) ≤ 2 * (acTuples (K := K) F m).card := by
    rw [card_acTuples_eq, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun uX _ =>
      (hrow uX).trans (le_of_eq (Finset.mul_sum _ _ _).symm)
  -- each row: `Q · N ≥ Q^{m+1} − m Q^m`
  have hrowR : ∀ uX : Fin m → K, (Q : ℝ) ^ (m + 1) - (m : ℝ) * (Q : ℝ) ^ m
      ≤ (Q : ℝ) * (#{uZ ∈ (univ : Finset (Fin m → K)) | indPair uX uZ ≠ 0} : ℝ) := by
    intro uX
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin m → K))) (p := fun uZ => indPair uX uZ = 0)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hsplit
    have hZ := card_indPair_eq_zero_mul_le uX
    have hcast : (#{uZ ∈ (univ : Finset (Fin m → K)) | indPair uX uZ = 0} : ℝ)
        + (#{uZ ∈ (univ : Finset (Fin m → K)) | indPair uX uZ ≠ 0} : ℝ) = (Q : ℝ) ^ m := by
      simp only [ne_eq]
      exact_mod_cast hsplit
    rw [pow_succ]
    nlinarith [hZ, hcast]
  have hsum : (Q : ℝ) ^ m * ((Q : ℝ) ^ (m + 1) - (m : ℝ) * (Q : ℝ) ^ m)
      ≤ (Q : ℝ) * (∑ uX : Fin m → K, (#{uZ ∈ (univ : Finset (Fin m → K)) |
          indPair uX uZ ≠ 0} : ℝ)) := by
    rw [Finset.mul_sum]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun uX _ => hrowR uX)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    norm_cast
  -- assemble
  have hnatR : ((Q : ℝ) - 1) * (Q : ℝ) * (∑ uX : Fin m → K,
      (#{uZ ∈ (univ : Finset (Fin m → K)) | indPair uX uZ ≠ 0} : ℝ))
      ≤ 2 * ((acTuples (K := K) F m).card : ℝ) := by
    have h := hnat
    have hc : ((Q - 1 : ℕ) : ℝ) = (Q : ℝ) - 1 := by
      have : (1 : ℕ) ≤ Q := le_of_lt hQ1
      push_cast [this]
      ring
    calc ((Q : ℝ) - 1) * (Q : ℝ) * (∑ uX : Fin m → K,
        (#{uZ ∈ (univ : Finset (Fin m → K)) | indPair uX uZ ≠ 0} : ℝ))
        = (((Q - 1) * Q * (∑ uX : Fin m → K, #{uZ ∈ (univ : Finset (Fin m → K)) |
            indPair uX uZ ≠ 0}) : ℕ) : ℝ) := by push_cast [hc]; ring
      _ ≤ ((2 * (acTuples (K := K) F m).card : ℕ) : ℝ) := by exact_mod_cast h
      _ = 2 * ((acTuples (K := K) F m).card : ℝ) := by push_cast; ring
  have hQ1R : (0 : ℝ) ≤ (Q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast le_of_lt hQ1
    linarith
  refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul_of_nonneg_left hsum hQ1R) ?_)
  · rw [two_mul, pow_add]
    ring
  · refine le_trans (le_of_eq ?_) hnatR
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun uX _ => by ring

omit [DecidableEq K] in
/-- Over `𝔽₂`, exactly half the field is in the kernel. -/
theorem two_mul_card_filter_trace_eq (hF : Fintype.card F = 2) (c : K) (hc : c ≠ 0) :
    2 * #{r ∈ (univ : Finset K) | Algebra.trace F K (c * r) = 0} = Fintype.card K := by
  have h := card_filter_trace_mul (F := F) c hc
  rw [hF] at h
  omega

/-- The same lower bound for the commuting pairs, and this time at *every* `(u_X, u_Z)`: when
the pairing vanishes every pair is commuting, and otherwise the `r_X ≠ 0` pairs already supply
half of `(q-1) q`. -/
theorem le_two_mul_card_pair_c (hF : Fintype.card F = 2) (uX uZ : Fin m → K) :
    (Fintype.card K - 1) * Fintype.card K
      ≤ 2 * #{c ∈ (univ : Finset (K × K)) | acGamma F uX uZ c.1 c.2 = 0} := by
  classical
  have hstep : ∀ rX : K, (if rX = 0 then 0 else Fintype.card K)
      ≤ 2 * #{rZ ∈ (univ : Finset K) | acGamma F uX uZ rX rZ = 0} := by
    intro rX
    by_cases h0 : rX = 0
    · simp [h0]
    · rw [if_neg h0]
      by_cases hp : indPair uX uZ = 0
      · have hz : ∀ rZ : K, acGamma F uX uZ rX rZ = 0 := by
          intro rZ; rw [acGamma, hp]; simp
        have hall : {rZ ∈ (univ : Finset K) | acGamma F uX uZ rX rZ = 0} = univ :=
          Finset.filter_eq_self.mpr fun rZ _ => hz rZ
        rw [hall, Finset.card_univ]
        have h1 : 1 ≤ Fintype.card K := Nat.one_le_of_lt Fintype.one_lt_card
        omega
      · have hc : rX * indPair uX uZ ≠ 0 := mul_ne_zero h0 hp
        have := two_mul_card_filter_trace_eq (F := F) hF (rX * indPair uX uZ) hc
        rw [← this]
        refine le_of_eq ?_
        congr 2
        refine Finset.filter_congr fun rZ _ => ?_
        rw [acGamma, mul_right_comm]
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.mul_sum]
  have h1 : ∀ rX : K, (if rX = 0 then 0 else Fintype.card K)
      ≤ 2 * ∑ rZ : K, (if acGamma F uX uZ rX rZ = 0 then 1 else 0) := by
    intro rX
    rw [← Finset.card_filter]
    exact hstep rX
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun rX (_ : rX ∈ univ) => h1 rX)
  have hswap : ∀ rX : K, (if rX = 0 then 0 else Fintype.card K)
      = if rX ≠ 0 then Fintype.card K else 0 := fun rX => (ite_not _ _ _).symm
  rw [Finset.sum_congr rfl fun rX (_ : rX ∈ univ) => hswap rX, ← Finset.sum_filter,
    Finset.sum_const, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
    Finset.card_univ, smul_eq_mul, mul_comm]

omit [DecidableEq K] [FiniteDimensional F K] [Algebra.IsSeparable F K] in
theorem card_cTuples_eq :
    (cTuples (K := K) F m).card
      = ∑ uX : Fin m → K, ∑ uZ : Fin m → K,
          #{c ∈ (univ : Finset (K × K)) | acGamma F uX uZ c.1 c.2 = 0} := by
  classical
  rw [cTuples, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun uX _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun uZ _ => (Finset.card_filter _ _).symm

omit [DecidableEq K] [FiniteDimensional F K] [Algebra.IsSeparable F K] in
theorem le_two_mul_card_cTuples (hF : Fintype.card F = 2) :
    ((Fintype.card K : ℝ) - 1) * (Fintype.card K : ℝ) ^ (2 * m + 1)
      ≤ 2 * ((cTuples (K := K) F m).card : ℝ) := by
  classical
  set Q : ℕ := Fintype.card K with hQdef
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hnat : (Q - 1) * Q * Q ^ m * Q ^ m ≤ 2 * (cTuples (K := K) F m).card := by
    rw [card_cTuples_eq, Finset.mul_sum]
    have hrow : ∀ uX : Fin m → K, (Q - 1) * Q * Q ^ m
        ≤ ∑ uZ : Fin m → K, 2 * #{c ∈ (univ : Finset (K × K)) |
            acGamma F uX uZ c.1 c.2 = 0} := by
      intro uX
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun uZ _ => le_two_mul_card_pair_c hF uX uZ)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul,
        mul_comm]
    calc (Q - 1) * Q * Q ^ m * Q ^ m
        = ∑ _uX : Fin m → K, (Q - 1) * Q * Q ^ m := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            smul_eq_mul, mul_comm]
      _ ≤ ∑ uX : Fin m → K, 2 * ∑ uZ : Fin m → K,
            #{c ∈ (univ : Finset (K × K)) | acGamma F uX uZ c.1 c.2 = 0} :=
          Finset.sum_le_sum fun uX _ =>
            (hrow uX).trans (le_of_eq (Finset.mul_sum _ _ _).symm)
  have hc : ((Q - 1 : ℕ) : ℝ) = (Q : ℝ) - 1 := by
    have : (1 : ℕ) ≤ Q := le_of_lt hQ1
    push_cast [this]
    ring
  calc ((Q : ℝ) - 1) * (Q : ℝ) ^ (2 * m + 1)
      = (((Q - 1) * Q * Q ^ m * Q ^ m : ℕ) : ℝ) := by
        push_cast [hc]
        rw [two_mul, pow_succ, pow_add]
        ring
    _ ≤ ((2 * (cTuples (K := K) F m).card : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = 2 * ((cTuples (K := K) F m).card : ℝ) := by push_cast; ring

omit [DecidableEq K] [FiniteDimensional F K] [Algebra.IsSeparable F K] in
/-- **The two cases partition the sample space.** This is what makes the pair of bounds below
informative rather than merely true: they add to at least `1 - (m+2)/q`, so neither set can be
much more than half, and in particular neither is everything. -/
theorem card_acTuples_add_card_cTuples :
    (acTuples (K := K) F m).card + (cTuples (K := K) F m).card
      = Fintype.card K ^ (2 * m + 2) := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset ((Fin m → K) × (Fin m → K) × K × K)))
    (p := fun ω => acGamma F ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = 0)
  rw [Finset.card_univ] at h
  have hcard : Fintype.card ((Fin m → K) × (Fin m → K) × K × K)
      = Fintype.card K ^ (2 * m + 2) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    rw [two_mul, pow_succ, pow_succ, pow_add]
    ring
  rw [hcard] at h
  rw [acTuples, cTuples]
  simp only [ne_eq]
  omega

/-! ### The fact -/

omit [DecidableEq K] [FiniteDimensional F K] [Algebra.IsSeparable F K] in
/-- **`fact:omega-anticomm-prob`, sharp form**: an anticommuting tuple has probability at least
`(1 - (m+1)/q)/2`. -/
theorem prob_anticommuting_ge_sharp (hF : Fintype.card F = 2) :
    (1 - ((m : ℝ) + 1) / Fintype.card K) / 2
      ≤ ((acTuples (K := K) F m).card : ℝ) / (Fintype.card K : ℝ) ^ (2 * m + 2) := by
  set Q : ℕ := Fintype.card K with hQdef
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hQ : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hQ1
  have hpow : (0 : ℝ) < (Q : ℝ) ^ (2 * m + 2) := by positivity
  have hmain := le_two_mul_card_acTuples (F := F) (K := K) (m := m) hF
  rw [div_le_div_iff₀ (by norm_num) hpow]
  have hexp : (Q : ℝ) ^ (2 * m + 2) = (Q : ℝ) ^ (2 * m) * (Q : ℝ) * (Q : ℝ) := by
    rw [pow_succ, pow_succ]
  have h2m : (0 : ℝ) ≤ (Q : ℝ) ^ (2 * m) := by positivity
  have hfield : (1 - ((m : ℝ) + 1) / (Q : ℝ)) * (Q : ℝ) ^ (2 * m + 2)
      = (Q : ℝ) ^ (2 * m) * ((Q : ℝ) * (Q : ℝ) - ((m : ℝ) + 1) * (Q : ℝ)) := by
    rw [hexp]
    field_simp
  rw [hfield]
  nlinarith [hmain, h2m, Nat.cast_nonneg (α := ℝ) m]

omit [DecidableEq K] [FiniteDimensional F K] [Algebra.IsSeparable F K] in
/-- **`fact:omega-anticomm-prob`, commuting case**: a commuting tuple has probability at least
`(1 - 1/q)/2`, with no `m` at all. -/
theorem prob_commuting_ge_sharp (hF : Fintype.card F = 2) :
    (1 - 1 / (Fintype.card K : ℝ)) / 2
      ≤ ((cTuples (K := K) F m).card : ℝ) / (Fintype.card K : ℝ) ^ (2 * m + 2) := by
  set Q : ℕ := Fintype.card K with hQdef
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hQ : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hQ1
  have hpow : (0 : ℝ) < (Q : ℝ) ^ (2 * m + 2) := by positivity
  have hmain := le_two_mul_card_cTuples (F := F) (K := K) (m := m) hF
  rw [div_le_div_iff₀ (by norm_num) hpow]
  have hfield : (1 - 1 / (Q : ℝ)) * (Q : ℝ) ^ (2 * m + 2)
      = ((Q : ℝ) - 1) * (Q : ℝ) ^ (2 * m + 1) := by
    rw [pow_succ]
    field_simp
  rw [hfield]
  linarith [hmain]

omit [DecidableEq K] [FiniteDimensional F K] [Algebra.IsSeparable F K] in
/-- **`fact:omega-anticomm-prob`** in the paper's shape: both cases have probability at least
`(1 - 3md/q)/2`. The hypotheses `1 ≤ m` and `1 ≤ d` are what makes `m + 1 ≤ 3md`; the sharp
forms above need neither. -/
theorem prob_anticommuting_ge (hF : Fintype.card F = 2) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    (1 - 3 * (m : ℝ) * d / Fintype.card K) / 2
      ≤ ((acTuples (K := K) F m).card : ℝ) / (Fintype.card K : ℝ) ^ (2 * m + 2) := by
  have hQ : (0 : ℝ) < (Fintype.card K : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt (Fintype.one_lt_card (α := K))
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hstep : (m : ℝ) + 1 ≤ 3 * (m : ℝ) * d := by nlinarith
  have hdiv : ((m : ℝ) + 1) / (Fintype.card K : ℝ)
      ≤ 3 * (m : ℝ) * d / (Fintype.card K : ℝ) := by
    rw [div_le_div_iff₀ hQ hQ]
    exact mul_le_mul_of_nonneg_right hstep hQ.le
  refine le_trans ?_ (prob_anticommuting_ge_sharp (F := F) (K := K) (m := m) hF)
  linarith

omit [DecidableEq K] [FiniteDimensional F K] [Algebra.IsSeparable F K] in
/-- The commuting case in the paper's shape. -/
theorem prob_commuting_ge (hF : Fintype.card F = 2) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    (1 - 3 * (m : ℝ) * d / Fintype.card K) / 2
      ≤ ((cTuples (K := K) F m).card : ℝ) / (Fintype.card K : ℝ) ^ (2 * m + 2) := by
  have hQ : (0 : ℝ) < (Fintype.card K : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt (Fintype.one_lt_card (α := K))
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hstep : (1 : ℝ) ≤ 3 * (m : ℝ) * d := by nlinarith
  have hdiv : (1 : ℝ) / (Fintype.card K : ℝ)
      ≤ 3 * (m : ℝ) * d / (Fintype.card K : ℝ) := by
    rw [div_le_div_iff₀ hQ hQ]
    exact mul_le_mul_of_nonneg_right hstep hQ.le
  refine le_trans ?_ (prob_commuting_ge_sharp (F := F) (K := K) (m := m) hF)
  linarith

end Fact

end MIPRE.LowDegree

end
