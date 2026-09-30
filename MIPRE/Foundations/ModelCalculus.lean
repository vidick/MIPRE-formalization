/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.LocalIsometry
public import MIPRE.Foundations.Parseval
public import MIPRE.Foundations.Sandwich

@[expose] public section

/-!
# The state calculus of the Pauli basis test's last stages, in a model

The soundness analysis of the Pauli basis test (`MIPRE/Background/QLD/`) proves a handful of
estimates about a single state vector on the way, each stated for matrices on `ℂ^N` and a vector
`v : N → ℂ`. New in Phase 5 of `planning/mipco-track.md`, where that analysis is stated in a
bipartite model: their forms in a state model (`MIPRE/Foundations/StateModel.lean`), with the
operators in the represented algebra `𝒞` and the state the model's, and for a bipartite model
(`MIPRE/Foundations/BipartiteModel.lean`) where a player's family is meant. A matrix statement is
the model statement in `StateModel.mat v` or `BipartiteModel.tensor ψ`.

* **Orthogonal outcomes have no cross terms** (`StateModel.snorm_sq_sum_orthogonal`, and
  `StateModel.snorm_sq_sum_orthogonal'` with a different tail on each outcome): both are
  `StateModel.snorm_sq_sum_proj_mul` of `MIPRE/Foundations/Commutation.lean` for a projective
  measurement.
* **A chain of `n` deviations costs a factor `n`** (`StateModel.sum_snorm_sq_chain_le`), not the
  `2ⁿ` of iterating the triangle inequality `StateModel.sum_snorm_sq_triangle`.
* **Weighting by coefficients of modulus at most one costs the size of the outcome set**
  (`StateModel.snorm_sq_obs_sub_le`), the state-norm form of `lem:qld-povm-to-obs`.
* **Moving a quadratic form to a nearby state** costs twice the operator bound times the distance
  (`StateModel.abs_qform_sub_qform_le`, on two vectors of the model's space through
  `StateModel.withState`; `Op.abs_qform_sub_qform_le` on the operators).
* **Two families of total squared norm at most one are at total squared distance at most four**
  (`BipartiteModel.sum_stateSqNorm_sub_le_four_of_le`), so in particular two projective
  measurements on a unit vector (`BipartiteModel.sum_stateSqNorm_sub_le_four`): the trivial bound
  of the second item of `thm:qld`.
* **Parseval for a coarse-graining by a linear form**, in any complex inner product space
  (`sum_avg_norm_fibreSum_sq`), from Parseval for an orthogonal family of characters
  (`sum_norm_charSum_sq`) over one copy of the field and over two (`sum_norm_trSum_sq`,
  `sum_norm_trSum2_sq`). It is the vector statement `sum_avg_norm_fibre_sq` of
  `MIPRE/Foundations/Parseval.lean` with the vectors in any Hilbert space. In a state model it is
  `StateModel.sum_avg_snorm_sq_fibre_eq`, a family of the model's algebra summing to zero; for a
  player's family `BipartiteModel.sum_avg_stateSqNorm_fibre_eq` (the second player's through
  `M.swap`), and for a cross-party deviation of two families summing to one,
  `BipartiteModel.sum_avg_xSqNorm_fibre_eq`.

The matrix lemmas these are the model forms of: `snorm_sq_sum_orthogonal` (`QLD/Pulling.lean`),
`snorm_sq_sum_orthogonal'`, `sum_snorm_sq_chain_le` (`QLD/Chain.lean`), `snorm_sq_obs_sub_le`
(`QLD/SelfCons.lean`), `abs_qform_sub_qform_le` (`QLD/SwapMeasure.lean`), and for Parseval
`sum_avg_normSq_stateVecB_fibre_eq` (`QLD/Products.lean`) and `sum_avg_xSqNorm_fibre_eq`
(`QLD/Combined.lean`). The trivial bound replaces `sum_snorm_sq_registerState_alice_le_two` and
`_bob_le_two` (`QLD/Soundness.lean`), with the constant `4` that `le_qldErr` allows in place of
their `2`. The model form of the triangle inequality `sum_snorm_sq_triangle'` was already
`StateModel.sum_snorm_sq_triangle`.
-/

noncomputable section

namespace MIPRE

open Finset
open scoped InnerProductSpace

/-! ## Moving a quadratic form to a nearby vector -/

namespace Op

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Moving a quadratic form to a nearby vector costs twice the bound times the distance.** The
difference splits into two terms, each with the deviation on one side, and each is bounded by
Cauchy--Schwarz against a vector of norm at most one. -/
theorem abs_qform_sub_qform_le (v w : H) {T : H →L[ℂ] H} {K : ℝ} (hK : 0 ≤ K) (hT : Bnd T K)
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) : |qform v T - qform w T| ≤ 2 * K * ‖v - w‖ := by
  have hsplit : ⟪v, T v⟫_ℂ - ⟪w, T w⟫_ℂ = ⟪v - w, T v⟫_ℂ + ⟪w, T (v - w)⟫_ℂ := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  have h1 : ‖⟪v - w, T v⟫_ℂ‖ ≤ K * ‖v - w‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    calc ‖v - w‖ * ‖T v‖ ≤ ‖v - w‖ * (K * ‖v‖) :=
          mul_le_mul_of_nonneg_left (hT v) (norm_nonneg _)
      _ ≤ ‖v - w‖ * (K * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hK) (norm_nonneg _)
      _ = K * ‖v - w‖ := by ring
  have h2 : ‖⟪w, T (v - w)⟫_ℂ‖ ≤ K * ‖v - w‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    calc ‖w‖ * ‖T (v - w)‖ ≤ 1 * ‖T (v - w)‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ ≤ K * ‖v - w‖ := by rw [one_mul]; exact hT (v - w)
  have hre : qform v T - qform w T = (⟪v, T v⟫_ℂ - ⟪w, T w⟫_ℂ).re := by
    rw [qform, qform, Complex.sub_re]
  rw [hre, hsplit]
  refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
  linarith

end Op

/-! ## The state calculus in a state model -/

namespace StateModel

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (M : StateModel 𝒞)

/-- **A sum of orthogonal blocks has no cross terms.** If `S` is a projective measurement then,
for any `R`, the squared state norm of `(∑ g ∈ s, S g) R` is the sum of those of the `S g R`.
The model form of the matrix `snorm_sq_sum_orthogonal` of `QLD/Pulling.lean`. -/
theorem snorm_sq_sum_orthogonal {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {S : Λ → 𝒞}
    (hS : IsPVMIn S) (R : 𝒞) (s : Finset Λ) :
    M.snorm ((∑ g ∈ s, S g) * R) ^ 2 = ∑ g ∈ s, M.snorm (S g * R) ^ 2 := by
  rw [Finset.sum_mul]
  exact M.snorm_sq_sum_proj_mul hS.star_eq (fun _ _ h => hS.orthogonal h) (fun _ => R) s

/-- **A sum of orthogonal blocks has no cross terms, even with a different tail on each.** The
model form of the matrix `snorm_sq_sum_orthogonal'` of `QLD/Chain.lean`. -/
theorem snorm_sq_sum_orthogonal' {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {S : Λ → 𝒞}
    (hS : IsPVMIn S) (R : Λ → 𝒞) (s : Finset Λ) :
    M.snorm (∑ g ∈ s, S g * R g) ^ 2 = ∑ g ∈ s, M.snorm (S g * R g) ^ 2 :=
  M.snorm_sq_sum_proj_mul hS.star_eq (fun _ _ h => hS.orthogonal h) R s

/-- **The triangle inequality along a chain of deviations.** A chain of `n` steps costs a factor
`n`, not `2ⁿ`: the total deviation telescopes into the sum of the steps', and Cauchy--Schwarz
against the constant one turns the squared norm of a sum of `n` terms into `n` times the sum of
their squares. The model form of the matrix `sum_snorm_sq_chain_le` of `QLD/Chain.lean`, over any
finite set of indices (the matrix one is `s = univ`). -/
theorem sum_snorm_sq_chain_le {ι : Type*} (s : Finset ι) (n : ℕ) (T : ℕ → ι → 𝒞) :
    ∑ i ∈ s, M.snorm (T 0 i - T n i) ^ 2
      ≤ n * ∑ k ∈ Finset.range n, ∑ i ∈ s, M.snorm (T k i - T (k + 1) i) ^ 2 := by
  have hpt : ∀ i, M.snorm (T 0 i - T n i) ^ 2
      ≤ (n : ℝ) * ∑ k ∈ Finset.range n, M.snorm (T k i - T (k + 1) i) ^ 2 := by
    intro i
    have htel : T 0 i - T n i = ∑ k ∈ Finset.range n, (T k i - T (k + 1) i) :=
      (Finset.sum_range_sub' (fun k => T k i) n).symm
    have hle : M.snorm (T 0 i - T n i) ≤ ∑ k ∈ Finset.range n, M.snorm (T k i - T (k + 1) i) := by
      rw [htel]
      exact M.snorm_sum_le _ _
    have hcs := sq_sum_le_card_mul_sum_sq (fun k : Fin n => M.snorm (T k i - T (k + 1) i))
      fun _ => M.snorm_nonneg _
    rw [Fintype.card_fin, Fin.sum_univ_eq_sum_range (fun k => M.snorm (T k i - T (k + 1) i)) n,
      Fin.sum_univ_eq_sum_range (fun k => M.snorm (T k i - T (k + 1) i) ^ 2) n] at hcs
    exact (pow_le_pow_left₀ (M.snorm_nonneg _) hle 2).trans hcs
  refine le_trans (Finset.sum_le_sum fun i _ => hpt i) (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_comm]

/-- **From measurement elements to weighted sums of them**: weighting both families by
coefficients of modulus at most one costs a factor the size of the outcome set, by the triangle
inequality over the outcomes and then Cauchy--Schwarz against the constant one. The model form of
the matrix `snorm_sq_obs_sub_le` of `QLD/SelfCons.lean` (`lem:qld-povm-to-obs`). -/
theorem snorm_sq_obs_sub_le {Λ : Type*} [Fintype Λ] (α : Λ → ℂ) (hα : ∀ a, ‖α a‖ ≤ 1)
    (A B : Λ → 𝒞) :
    M.snorm ((∑ a, α a • A a) - ∑ a, α a • B a) ^ 2
      ≤ (Fintype.card Λ : ℝ) * ∑ a, M.snorm (A a - B a) ^ 2 := by
  have hsub : (∑ a, α a • A a) - ∑ a, α a • B a = ∑ a, α a • (A a - B a) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => (smul_sub _ _ _).symm
  have htri : M.snorm ((∑ a, α a • A a) - ∑ a, α a • B a) ≤ ∑ a, M.snorm (A a - B a) := by
    rw [hsub]
    refine (M.snorm_sum_le univ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [M.snorm_smul]
    exact mul_le_of_le_one_left (M.snorm_nonneg _) (hα a)
  calc M.snorm ((∑ a, α a • A a) - ∑ a, α a • B a) ^ 2
      ≤ (∑ a, M.snorm (A a - B a)) ^ 2 := pow_le_pow_left₀ (M.snorm_nonneg _) htri 2
    _ ≤ (Fintype.card Λ : ℝ) * ∑ a, M.snorm (A a - B a) ^ 2 :=
        sq_sum_le_card_mul_sum_sq _ fun a => M.snorm_nonneg _

/-- **Moving a quadratic form to a nearby state costs twice the bound times the distance**, for
two vectors `v`, `w` of norm at most one of the model's space, each read as the state
(`StateModel.withState`). The model form of the matrix `abs_qform_sub_qform_le` of
`QLD/SwapMeasure.lean`. -/
theorem abs_qform_sub_qform_le (v w : M.H) {X : 𝒞} {K : ℝ} (hK : 0 ≤ K) (hX : M.Bnd X K)
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |(M.withState v).qform X - (M.withState w).qform X| ≤ 2 * K * ‖v - w‖ :=
  Op.abs_qform_sub_qform_le v w hK hX hv hw

/-- `abs_qform_sub_qform_le` against the model's own state. -/
theorem abs_qform_withState_sub_qform_le (v : M.H) {X : 𝒞} {K : ℝ} (hK : 0 ≤ K)
    (hX : M.Bnd X K) (hv : ‖v‖ ≤ 1) (hψ : ‖M.ψ‖ ≤ 1) :
    |(M.withState v).qform X - M.qform X| ≤ 2 * K * ‖v - M.ψ‖ :=
  Op.abs_qform_sub_qform_le v M.ψ hK hX hv hψ

end StateModel

/-! ## The trivial bound on a summed distance -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)

/-- **The summed squared distance of two families is at most twice the sum of their summed
squared norms**: the triangle inequality through `0`. -/
theorem sum_stateSqNorm_sub_le {Λ : Type*} (s : Finset Λ) (A B : Λ → 𝒜) :
    ∑ h ∈ s, M.stateSqNorm (A h - B h)
      ≤ 2 * ∑ h ∈ s, M.stateSqNorm (A h) + 2 * ∑ h ∈ s, M.stateSqNorm (B h) := by
  have h := M.sum_snorm_sq_triangle s (fun h => M.πA (A h)) (fun _ => 0) (fun h => M.πA (B h))
  simpa only [stateSqNorm, stateNorm, map_sub, sub_zero, zero_sub, M.snorm_neg] using h

/-- **Two families each of summed squared norm at most one are at summed squared distance at most
four.** This covers two POVMs on a unit vector (`sum_stateSqNorm_le_one`), sub-POVMs, and the
images of projective measurements under a non-unital `⋆`-homomorphism. -/
theorem sum_stateSqNorm_sub_le_four_of_le {Λ : Type*} [Fintype Λ] {A B : Λ → 𝒜}
    (hA : ∑ h, M.stateSqNorm (A h) ≤ 1) (hB : ∑ h, M.stateSqNorm (B h) ≤ 1) :
    ∑ h, M.stateSqNorm (A h - B h) ≤ 4 := by
  have h := M.sum_stateSqNorm_sub_le univ A B
  linarith

/-- **Two projective measurements on a unit vector are at summed squared distance at most
four**: the trivial bound of the second item of `thm:qld`, in place of the matrix
`sum_snorm_sq_registerState_alice_le_two` and `_bob_le_two` of `QLD/Soundness.lean` (the second
player's is this in `M.swap`). The matrix bound `2` uses that on the register state the honest
projector on one party is the same projector on the other; `4` needs nothing, and is what
`le_qldErr` asks for. -/
theorem sum_stateSqNorm_sub_le_four (hψ : ‖M.ψ‖ = 1) {Λ : Type*} [Fintype Λ] {A B : Λ → 𝒜}
    (hA : IsPVMIn A) (hB : IsPVMIn B) : ∑ h, M.stateSqNorm (A h - B h) ≤ 4 :=
  M.sum_stateSqNorm_sub_le_four_of_le (M.sum_stateSqNorm_of_isPVMIn hψ hA).le
    (M.sum_stateSqNorm_of_isPVMIn hψ hB).le

end BipartiteModel

/-! ## Parseval in a complex inner product space

`MIPRE/Foundations/Parseval.lean` proves the character Parsevals for vectors of `ℂ^N`; the same
statements hold, with the same proof, in any complex inner product space, and that is the form a
state model needs: the vectors are `π(T) ψ` in the model's Hilbert space. -/

section Parseval

open MIPRE.Weyl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Parseval for an orthogonal family of characters**, in any complex inner product space: if
the characters `χ r` satisfy `∑_r conj(χ r a) χ r b = c δ_{ab}`, then the transform
`r ↦ ∑_a χ r a • T a` has total squared norm `c` times the family's. -/
theorem sum_norm_charSum_sq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (χ : κ → ι → ℂ) {c : ℝ}
    (hχ : ∀ a b, ∑ r, star (χ r a) * χ r b = if a = b then (c : ℂ) else 0) (T : ι → E) :
    ∑ r, ‖∑ a, χ r a • T a‖ ^ 2 = c * ∑ a, ‖T a‖ ^ 2 := by
  have hexp : ∀ r, ⟪∑ a, χ r a • T a, ∑ b, χ r b • T b⟫_ℂ
      = ∑ a, ∑ b, star (χ r a) * χ r b * ⟪T a, T b⟫_ℂ := by
    intro r
    rw [sum_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [inner_smul_left, inner_smul_right, ← RCLike.star_def, mul_assoc]
  have hsum : ∑ r, ⟪∑ a, χ r a • T a, ∑ b, χ r b • T b⟫_ℂ = (c : ℂ) * ∑ a, ⟪T a, T a⟫_ℂ := by
    simp_rw [hexp]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hχ]
    simp
  have h := congrArg Complex.re hsum
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at h
  simpa only [← RCLike.re_to_complex, inner_self_eq_norm_sq] using h

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]

/-- The one-field character sum, as an `if`. -/
theorem sum_sgn_trMul_eq_ite (x : F) :
    ∑ r : F, sgn (Algebra.trace (ZMod 2) F (r * x))
      = if x = 0 then (Fintype.card F : ℂ) else 0 := by
  split_ifs with hx
  · subst hx
    exact sum_sgn_trMul_zero
  · exact sum_sgn_trMul hx

/-- **The characters `c ↦ (-1)^{tr(c r)}` are orthogonal**, with norm `q`. -/
theorem sum_star_sgn_trMul (a b : F) :
    ∑ r : F, star (sgn (Algebra.trace (ZMod 2) F (a * r)))
        * sgn (Algebra.trace (ZMod 2) F (b * r))
      = if a = b then ((Fintype.card F : ℝ) : ℂ) else 0 := by
  have hterm : ∀ r : F, star (sgn (Algebra.trace (ZMod 2) F (a * r)))
      * sgn (Algebra.trace (ZMod 2) F (b * r)) = sgn (Algebra.trace (ZMod 2) F (r * (a + b))) := by
    intro r
    rw [star_sgn, ← sgn_add, ← map_add, ← add_mul, mul_comm]
  rw [Finset.sum_congr rfl fun r _ => hterm r, sum_sgn_trMul_eq_ite, Complex.ofReal_natCast]
  simp only [Weyl.add_eq_zero_iff]

/-- **The characters `p ↦ (-1)^{tr(q₁ p₁) + tr(q₂ p₂)}` of `F_q × F_q` are orthogonal**, with norm
`q²`. -/
theorem sum_star_sgn_trMul2 (a b : F × F) :
    ∑ q : F × F, star (sgn (Algebra.trace (ZMod 2) F (q.1 * a.1)
        + Algebra.trace (ZMod 2) F (q.2 * a.2)))
        * sgn (Algebra.trace (ZMod 2) F (q.1 * b.1) + Algebra.trace (ZMod 2) F (q.2 * b.2))
      = if a = b then (((Fintype.card F : ℝ) * (Fintype.card F : ℝ) : ℝ) : ℂ) else 0 := by
  have hterm : ∀ q : F × F, star (sgn (Algebra.trace (ZMod 2) F (q.1 * a.1)
        + Algebra.trace (ZMod 2) F (q.2 * a.2)))
        * sgn (Algebra.trace (ZMod 2) F (q.1 * b.1) + Algebra.trace (ZMod 2) F (q.2 * b.2))
      = sgn (Algebra.trace (ZMod 2) F (q.1 * (a.1 + b.1)))
        * sgn (Algebra.trace (ZMod 2) F (q.2 * (a.2 + b.2))) := by
    intro q
    rw [star_sgn, ← sgn_add, ← sgn_add, mul_add, mul_add, map_add, map_add]
    congr 1
    abel
  rw [Finset.sum_congr rfl fun q _ => hterm q]
  simp only [Fintype.sum_prod_type]
  rw [← Finset.sum_mul_sum, sum_sgn_trMul_eq_ite, sum_sgn_trMul_eq_ite]
  simp only [Weyl.add_eq_zero_iff]
  by_cases h1 : a.1 = b.1 <;> by_cases h2 : a.2 = b.2 <;> simp [h1, h2, Prod.ext_iff]

/-- **Parseval over one copy of the field**, in any complex inner product space: the matrix
`sum_norm_trVecRaw_sq` of `MIPRE/Foundations/Parseval.lean` with the vectors in `E`. -/
theorem sum_norm_trSum_sq (T : F → E) :
    ∑ r : F, ‖∑ c : F, sgn (Algebra.trace (ZMod 2) F (c * r)) • T c‖ ^ 2
      = (Fintype.card F : ℝ) * ∑ c : F, ‖T c‖ ^ 2 :=
  sum_norm_charSum_sq (ι := F) (κ := F) (c := (Fintype.card F : ℝ))
    (fun (r c : F) => sgn (Algebra.trace (ZMod 2) F (c * r))) sum_star_sgn_trMul T

/-- **Parseval over two copies of the field**, in any complex inner product space: the matrix
`sum_norm_char_two_sq` of `MIPRE/Foundations/Parseval.lean` with the vectors in `E`. -/
theorem sum_norm_trSum2_sq (T : F × F → E) :
    ∑ q : F × F, ‖∑ p : F × F,
        sgn (Algebra.trace (ZMod 2) F (q.1 * p.1)
          + Algebra.trace (ZMod 2) F (q.2 * p.2)) • T p‖ ^ 2
      = ((Fintype.card F : ℝ) * (Fintype.card F : ℝ)) * ∑ p : F × F, ‖T p‖ ^ 2 :=
  sum_norm_charSum_sq (ι := F × F) (κ := F × F)
    (c := (Fintype.card F : ℝ) * (Fintype.card F : ℝ))
    (fun (q p : F × F) => sgn (Algebra.trace (ZMod 2) F (q.1 * p.1)
      + Algebra.trace (ZMod 2) F (q.2 * p.2))) sum_star_sgn_trMul2 T

/-- **Parseval for a coarse-graining by a linear form**, in any complex inner product space. A
family of vectors indexed by `F_q × F_q` that *sums to zero* has, on average over `(α, β)`
uniform, fibre sums under `(a, b) ↦ α a + β b` whose total squared norm is `1 - 1/q` times the
family's own; a per-fibre triangle inequality would cost the factor `q` the fibres have. The
matrix `sum_avg_norm_fibre_sq` of `MIPRE/Foundations/Parseval.lean` with the vectors in `E`, by
the same proof; the zero-sum hypothesis kills the `r = 0` character. -/
theorem sum_avg_norm_fibreSum_sq (U : F × F → E) (hU : ∑ p : F × F, U p = 0) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ c : F, ‖∑ p ∈ univ.filter fun p : F × F =>
          ab.1 * p.1 + ab.2 * p.2 = c, U p‖ ^ 2
      = (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, ‖U p‖ ^ 2 := by
  classical
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set G : F × F → E := fun st => ∑ p : F × F,
    sgn (Algebra.trace (ZMod 2) F (st.1 * p.1)
      + Algebra.trace (ZMod 2) F (st.2 * p.2)) • U p with hG
  set S : ℝ := ∑ p : F × F, ‖U p‖ ^ 2 with hS
  -- **step 1**: the fibre sums are a character average, for each fixed `(α, β)`
  have hstep1 : ∀ ab : F × F,
      (∑ c : F, ‖∑ p ∈ univ.filter fun p : F × F =>
          ab.1 * p.1 + ab.2 * p.2 = c, U p‖ ^ 2)
        = (Fintype.card F : ℝ)⁻¹ * ∑ r : F, ‖G (r * ab.1, r * ab.2)‖ ^ 2 := by
    intro ab
    have hraw : ∀ r : F,
        (∑ c : F, sgn (Algebra.trace (ZMod 2) F (c * r)) • ∑ p ∈ univ.filter fun p : F × F =>
            ab.1 * p.1 + ab.2 * p.2 = c, U p)
          = G (r * ab.1, r * ab.2) := by
      intro r
      rw [hG]
      refine (Finset.sum_congr rfl fun c (_ : c ∈ univ) => ?_).trans
        (Finset.sum_fiberwise (univ : Finset (F × F))
          (fun p : F × F => ab.1 * p.1 + ab.2 * p.2)
          (fun p : F × F => sgn (Algebra.trace (ZMod 2) F ((r * ab.1) * p.1)
            + Algebra.trace (ZMod 2) F ((r * ab.2) * p.2)) • U p))
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← (Finset.mem_filter.mp hp).2,
        show Algebra.trace (ZMod 2) F ((r * ab.1) * p.1)
            + Algebra.trace (ZMod 2) F ((r * ab.2) * p.2)
          = Algebra.trace (ZMod 2) F ((ab.1 * p.1 + ab.2 * p.2) * r) from by
          rw [← map_add]
          congr 1
          ring]
    have hT := sum_norm_trSum_sq (fun c : F => ∑ p ∈ univ.filter fun p : F × F =>
        ab.1 * p.1 + ab.2 * p.2 = c, U p)
    rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by rw [hraw r]] at hT
    rw [hT]
    field_simp
  rw [Finset.sum_congr rfl fun ab (_ : ab ∈ univ) => by rw [hstep1 ab]]
  -- **step 2**: swap the two averages
  have hswap : (∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ((Fintype.card F : ℝ)⁻¹ * ∑ r : F, ‖G (r * ab.1, r * ab.2)‖ ^ 2))
      = ∑ r : F, (Fintype.card F : ℝ)⁻¹ *
          (((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
            ∑ ab : F × F, ‖G (r * ab.1, r * ab.2)‖ ^ 2) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun ab _ => by ring
  rw [hswap]
  -- **step 3**: each nonzero character contributes the family's total; the zero one nothing
  have hterm : ∀ r : F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
      (∑ ab : F × F, ‖G (r * ab.1, r * ab.2)‖ ^ 2) = if r = 0 then 0 else S := by
    intro r
    by_cases hr : r = 0
    · subst hr
      rw [ite_eq_left rfl]
      have hzero : ∀ ab : F × F, G ((0 : F) * ab.1, (0 : F) * ab.2) = 0 := by
        intro ab
        rw [hG]
        show (∑ p : F × F, sgn (Algebra.trace (ZMod 2) F ((0 : F) * ab.1 * p.1)
          + Algebra.trace (ZMod 2) F ((0 : F) * ab.2 * p.2)) • U p) = 0
        rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => by
          rw [zero_mul, zero_mul, zero_mul, zero_mul, map_zero, add_zero, sgn_zero, one_smul]]
        exact hU
      rw [Finset.sum_congr rfl fun ab (_ : ab ∈ univ) => by rw [hzero ab]]
      simp
    · rw [ite_eq_right hr]
      have hbij : (∑ ab : F × F, ‖G (r * ab.1, r * ab.2)‖ ^ 2)
          = ∑ st : F × F, ‖G (st.1, st.2)‖ ^ 2 :=
        Fintype.sum_equiv ((Equiv.mulLeft₀ r hr).prodCongr (Equiv.mulLeft₀ r hr)) _ _
          fun ab => rfl
      rw [hbij, hG]
      rw [show (∑ st : F × F, ‖(fun st : F × F => ∑ p : F × F,
            sgn (Algebra.trace (ZMod 2) F (st.1 * p.1)
              + Algebra.trace (ZMod 2) F (st.2 * p.2)) • U p) (st.1, st.2)‖ ^ 2)
          = ∑ q : F × F, ‖∑ p : F × F,
              sgn (Algebra.trace (ZMod 2) F (q.1 * p.1)
                + Algebra.trace (ZMod 2) F (q.2 * p.2)) • U p‖ ^ 2 from rfl,
        sum_norm_trSum2_sq, hS]
      field_simp
  rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by rw [hterm r], ← Finset.mul_sum]
  have h1 : (∑ _r : F, if _r = 0 then (0 : ℝ) else S) = (Fintype.card F : ℝ) * S - S := by
    have h2 : ∀ r : F, (if r = 0 then (0 : ℝ) else S) = S - (if r = 0 then S else 0) := by
      intro r
      by_cases h : r = 0 <;> simp [h]
    rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => h2 r, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp
  rw [h1]
  field_simp

end Parseval

/-! ## Parseval in a model -/

namespace StateModel

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (M : StateModel 𝒞)
  {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]

/-- **Parseval over `F_q` for the fibre sums of a family summing to zero**, in a state model: the
average over the combining coefficients of the squared state norms of the fibre sums is
`(1 - 1/q)` times the sum of the squared state norms of the members. `sum_avg_norm_fibreSum_sq`
on the vectors `π(E p) ψ`. -/
theorem sum_avg_snorm_sq_fibre_eq {E : F × F → 𝒞} (hE : ∑ p, E p = 0) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ c : F, M.snorm (∑ p ∈ univ.filter fun p : F × F =>
          ab.1 * p.1 + ab.2 * p.2 = c, E p) ^ 2
      = (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, M.snorm (E p) ^ 2 := by
  have hvec : ∀ s : Finset (F × F), M.snorm (∑ p ∈ s, E p) = ‖∑ p ∈ s, M.π (E p) M.ψ‖ := by
    intro s
    show ‖M.π (∑ p ∈ s, E p) M.ψ‖ = _
    rw [map_sum, _root_.sum_apply]
  have hU : ∑ p, M.π (E p) M.ψ = 0 := by
    rw [← _root_.sum_apply, ← map_sum, hE, map_zero, _root_.zero_apply]
  simp_rw [hvec]
  exact sum_avg_norm_fibreSum_sq (fun p => M.π (E p) M.ψ) hU

end StateModel

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)
  {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]

/-- **Parseval over `F_q` for the fibre sums of a player's family summing to zero.** For the
second player's family `E : F × F → ℬ` it is the statement in `M.swap`, whose state norm is
`‖πB(·) ψ‖`: the model form of the matrix `sum_avg_normSq_stateVecB_fibre_eq` of
`QLD/Products.lean`, whose fibre sum `ptComb E α β c` is the one here. -/
theorem sum_avg_stateSqNorm_fibre_eq {E : F × F → 𝒜} (hE : ∑ p, E p = 0) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ c : F, M.stateSqNorm (∑ p ∈ univ.filter fun p : F × F =>
          ab.1 * p.1 + ab.2 * p.2 = c, E p)
      = (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, M.stateSqNorm (E p) := by
  have h := M.toStateModel.sum_avg_snorm_sq_fibre_eq (E := fun p => M.πA (E p))
    (by rw [← map_sum, hE, map_zero])
  simpa only [stateSqNorm, stateNorm, map_sum] using h

/-- **Parseval over `F_q` for the fibre sums of a cross-party deviation**: two families, one for
each player, each summing to one, coarse-grained by `(a, b) ↦ α a + β b`. The model form of the
matrix `sum_avg_xSqNorm_fibre_eq` of `QLD/Combined.lean`. -/
theorem sum_avg_xSqNorm_fibre_eq {Q : F × F → 𝒜} {B : F × F → ℬ} (hQ : ∑ p, Q p = 1)
    (hB : ∑ p, B p = 1) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ v : F, M.xSqNorm
          (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, Q p)
          (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, B p)
      = (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, M.xSqNorm (Q p) (B p) := by
  have h := M.toStateModel.sum_avg_snorm_sq_fibre_eq (E := fun p => M.πA (Q p) - M.πB (B p))
    (by rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, hQ, hB, map_one, map_one, sub_self])
  simpa only [xSqNorm, xNorm, map_sum, Finset.sum_sub_distrib] using h

end BipartiteModel

end MIPRE

end

end
