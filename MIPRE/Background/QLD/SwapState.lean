/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.SwapUnitary

/-!
# The swap isometry's state estimate (`lem:qld-swap`, item 1)

`MIPRE/Background/QLD/SwapUnitary.lean` proves the two halves of item 1 separately: the algebra
(`swapU_conj_wTilde_X`, `swapU_conj_wTilde_Z`: conjugation by the swap map carries the exact Pauli
observables to bare generalized Paulis, with no error at all), the identity the estimate rests on
(`twirl_mul_twirl`: the product of the two Weyl twirls is the maximally entangled projector), and
the arithmetic that turns two near-invariances into a closeness
(`norm_sub_sq_le_of_re_inner_ge`, `re_inner_ge_of_two_close`, `norm_sub_normalize_sq_le`). What it
does not do is put them together on a state, because `twirl_mul_twirl` lives on the two ancilla
halves alone and the state lives on all four registers.

This file is that assembly. On the space `R x (T x T)` --- the two parties' non-ancilla registers
as one index `R`, their two ancilla halves adjacent as `T x T` --- the twirls act through `bOp`,
their product is `bOp eprProj` by `twirl_mul_twirl`, and the range of `bOp eprProj` is exactly the
vectors of the form `aux (x) EPR` (`bOp_eprProj_mulVec`). So a state that is nearly invariant under
both twirls is close to a product `aux (x) EPR`, which is item 1.

The self-consistency that supplies the two near-invariances --- `W~^e(u-tilde)` on one party agrees
with `W~^e(u-tilde)` on the other, on average over a *uniform* `u-tilde` --- is the paper's second
item of `lem:qld-construct-the-paulis` and is a hypothesis here, not a conclusion. It is the piece
of stage 5 that remains.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The twirl is a self-adjoint contraction -/

section Twirl

variable {N : Type*} [Fintype N]

/-- The state norm of a sum is at most the sum of the state norms. -/
theorem snorm_sum_le {ι : Type*} (v : N → ℂ) (s : Finset ι) (f : ι → Matrix N N ℂ) :
    snorm v (∑ i ∈ s, f i) ≤ ∑ i ∈ s, snorm v (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, snorm, Matrix.zero_mulVec, evec_zero,
        norm_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (snorm_add_le v _ _) (by linarith)

end Twirl

section TwirlWeyl

/-- Each term of the twirl is a unitary, being the square of a self-adjoint involution. -/
theorem kron_self_isometry {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w)
    (u : n → F) : (w u ⊗ₖ w u)ᴴ * (w u ⊗ₖ w u) = 1 := by
  rw [Matrix.conjTranspose_kronecker, hw.selfAdjoint, ← Matrix.mul_kronecker_mul,
    show w u * w u = 1 from by rw [← hw.map_add, add_self_vec, hw.map_zero],
    Matrix.one_kronecker_one]

omit [Algebra (ZMod 2) F] in
/-- **The twirl is self-adjoint.** -/
theorem twirl_conjTranspose {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w) :
    (twirl w)ᴴ = twirl w := by
  have hsa : (∑ u : n → F, w u ⊗ₖ w u)ᴴ = ∑ u : n → F, w u ⊗ₖ w u := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun u _ => by
      rw [Matrix.conjTranspose_kronecker, hw.selfAdjoint]
  have hc : star ((Fintype.card (n → F) : ℂ))⁻¹ = ((Fintype.card (n → F) : ℂ))⁻¹ := by
    rw [RCLike.star_def, map_inv₀, Complex.conj_natCast]
  ext i j
  simp only [twirl, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul]
  rw [star_mul', hc, ← Matrix.conjTranspose_apply, hsa]

/-- **The twirl is a contraction**: an average of `q^n` unitaries. -/
theorem snorm_twirl_le {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w)
    (v : (n → F) × (n → F) → ℂ) : snorm v (twirl w) ≤ ‖evec v‖ := by
  have hcard : (0 : ℝ) < (Fintype.card (n → F) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hterm : ∀ u : n → F, snorm v (w u ⊗ₖ w u) = ‖evec v‖ := fun u =>
    norm_evec_mulVec_of_isometry (kron_self_isometry hw u) v
  rw [twirl, snorm_smul]
  have hsum : snorm v (∑ u : n → F, w u ⊗ₖ w u) ≤ (Fintype.card (n → F) : ℝ) * ‖evec v‖ := by
    refine le_trans (snorm_sum_le v univ _) ?_
    rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => hterm u, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hnorm : ‖((Fintype.card (n → F) : ℂ))⁻¹‖ = ((Fintype.card (n → F) : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hnorm]
  calc ((Fintype.card (n → F) : ℝ))⁻¹ * snorm v (∑ u : n → F, w u ⊗ₖ w u)
      ≤ ((Fintype.card (n → F) : ℝ))⁻¹ * ((Fintype.card (n → F) : ℝ) * ‖evec v‖) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖evec v‖ := by field_simp

/-- **The twirl is a projection.** The Weyl family is a homomorphism, so the double average
collapses: for each `s` there are exactly `q^n` pairs `(u, v)` with `u + v = s`. -/
theorem twirl_mul_self {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w) :
    twirl w * twirl w = twirl w := by
  have hinner : ∀ u : n → F,
      (∑ v : n → F, (w u ⊗ₖ w u) * (w v ⊗ₖ w v)) = ∑ s : n → F, w s ⊗ₖ w s := by
    intro u
    rw [Finset.sum_congr rfl fun v (_ : v ∈ univ) => by
      rw [← Matrix.mul_kronecker_mul, ← hw.map_add]]
    exact Equiv.sum_comp (Equiv.addLeft u) fun s => w s ⊗ₖ w s
  have hcard : (Fintype.card (n → F) : ℂ) ≠ 0 := card_ne_zero
  rw [twirl, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.sum_mul,
    Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [Finset.mul_sum, hinner u],
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  field_simp

end TwirlWeyl

/-! ## The maximally entangled projector -/

section EprProj

omit [Field F] [Algebra (ZMod 2) F] in
/-- The maximally entangled vector is real, so it is its own conjugate. -/
theorem conj_epr (p : (n → F) × (n → F)) :
    (starRingEnd ℂ) (epr (F := F) (n := n) p) = epr p := by
  rw [epr]
  by_cases h : p.1 = p.2
  · rw [if_pos h, Complex.conj_ofReal]
  · rw [if_neg h, map_zero]

omit [Field F] [Algebra (ZMod 2) F] in
theorem star_epr : star (epr (F := F) (n := n)) = epr :=
  funext fun p => conj_epr p

omit [Field F] [Algebra (ZMod 2) F] in
theorem eprProj_conjTranspose : (eprProj (F := F) (n := n))ᴴ = eprProj := by
  ext i j
  simp only [Matrix.conjTranspose_apply, eprProj, Matrix.vecMulVec_apply, RCLike.star_def]
  rw [map_mul, conj_epr, conj_epr, mul_comm]

theorem epr_dotProduct : epr (F := F) (n := n) ⬝ᵥ epr = 1 := by
  rw [← epr_unit (F := F) (n := n), star_epr]

/-- The maximally entangled projector is idempotent, because the state is a unit vector. -/
theorem eprProj_mul_self : eprProj (F := F) (n := n) * eprProj = eprProj := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [eprProj, Matrix.vecMulVec_apply]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) =>
      show epr (F := F) (n := n) i * epr k * (epr k * epr j)
        = (epr i * epr j) * (epr k * epr k) from by ring,
    ← Finset.mul_sum]
  rw [show (∑ k : (n → F) × (n → F), epr (F := F) (n := n) k * epr k) = 1 from epr_dotProduct,
    mul_one]

end EprProj

/-! ## Item 1 of `lem:qld-swap` -/

section Item1

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- The state the swap isometry lands on: an auxiliary vector on the two parties' non-ancilla
registers, tensored with the maximally entangled pair. -/
def auxVec (aux : R → ℂ) : R × ((n → F) × (n → F)) → ℂ := fun p => aux p.1 * epr p.2

omit [Field F] [Algebra (ZMod 2) F] in
/-- **Applying `1 (x) |EPR><EPR|` produces a product vector**, which is where item 1's auxiliary
state comes from: the second factor is the maximally entangled state and the first is the partial
overlap with it. -/
theorem bOp_eprProj_mulVec (θ : R × ((n → F) × (n → F)) → ℂ) (r : R) (t : (n → F) × (n → F)) :
    ((bOp (eprProj (F := F) (n := n)) :
        Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ) (r, t)
      = (∑ s, epr (F := F) (n := n) s * θ (r, s)) * epr t := by
  classical
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.sum_eq_single r (fun r' _ hr' => Finset.sum_eq_zero fun t' _ => by
        rw [bOp, Matrix.kronecker_apply, Matrix.one_apply_ne (Ne.symm hr'), zero_mul, zero_mul])
      fun hmem => absurd (mem_univ r) hmem,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun t' _ => ?_
  rw [bOp, Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul, eprProj, Matrix.vecMulVec_apply]
  ring

/-- **The state estimate of `lem:qld-swap`, item 1.**

A unit state that is nearly invariant under both Weyl twirls on its two ancilla halves is close to
a product `aux (x) EPR`. The two hypotheses are what the self-consistency of the exact Pauli
observables supplies after conjugation by the swap map (`swapU_conj_wTilde_X`,
`swapU_conj_wTilde_Z` carry `W~^e(u-tilde)` to `1 (x) tau^W(e u-tilde)` with no error), and they
are hypotheses here rather than conclusions: that self-consistency, at a *uniform* `u-tilde`, is
the paper's second item of `lem:qld-construct-the-paulis` and is what remains of stage 5.

The estimate itself is the appendix's, in the repaired form: `2 - 2 sqrt(1 - eta)` with
`eta = 2 sqrt(delta) + 2 delta`, which is `O(sqrt(delta))`. -/
theorem exists_auxVec_close (θ : R × ((n → F) × (n → F)) → ℂ) (hθ : star θ ⬝ᵥ θ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hlt : 2 * Real.sqrt δ + 2 * δ < 1)
    (hX : 1 - δ / 2
      ≤ (star θ ⬝ᵥ ((bOp (twirl (wX (F := F) (n := n))) :
          Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)).re)
    (hZ : 1 - δ / 2
      ≤ (star θ ⬝ᵥ ((bOp (twirl (wZ (F := F) (n := n))) :
          Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)).re) :
    ∃ aux : R → ℂ, ‖evec (auxVec (F := F) (n := n) aux)‖ = 1 ∧
      ‖evec θ - evec (auxVec (F := F) (n := n) aux)‖ ^ 2
        ≤ 2 - 2 * Real.sqrt (1 - (2 * Real.sqrt δ + 2 * δ)) := by
  classical
  have hθn : ‖evec θ‖ = 1 := by
    have h : ‖evec θ‖ ^ 2 = 1 := by rw [norm_evec_sq, hθ, Complex.one_re]
    nlinarith [norm_nonneg (evec θ)]
  -- the two lifted twirls are projections
  have hsa : ∀ {w : (n → F) → Matrix (n → F) (n → F) ℂ}, IsWeylFamily w →
      (bOp (twirl w) : Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ)ᴴ
        = bOp (twirl w) := fun hw => by rw [bOp_conjTranspose, twirl_conjTranspose hw]
  have hid : ∀ {w : (n → F) → Matrix (n → F) (n → F) ℂ}, IsWeylFamily w →
      (bOp (twirl w) : Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ)
        * bOp (twirl w) = bOp (twirl w) := fun hw => by rw [← bOp_mul, twirl_mul_self hw]
  have hXd : ‖evec θ - evec ((bOp (twirl (wX (F := F) (n := n))) :
      Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)‖ ^ 2 ≤ δ :=
    norm_sub_sq_le_of_re_inner_ge hθn
      (snorm_le_one_of_proj hθn (hsa isWeylFamily_wX) (hid isWeylFamily_wX))
      (by rw [inner_evec]; exact hX)
  have hZd : ‖evec θ - evec ((bOp (twirl (wZ (F := F) (n := n))) :
      Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)‖ ^ 2 ≤ δ :=
    norm_sub_sq_le_of_re_inner_ge hθn
      (snorm_le_one_of_proj hθn (hsa isWeylFamily_wZ) (hid isWeylFamily_wZ))
      (by rw [inner_evec]; exact hZ)
  have hin := re_inner_ge_of_two_close hδ hθn hXd hZd
  -- the overlap of the two twirled states is the weight on the entangled projector
  have hQ : (inner ℂ (evec ((bOp (twirl (wX (F := F) (n := n))) :
        Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ))
        (evec ((bOp (twirl (wZ (F := F) (n := n))) :
        Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)) : ℂ)
      = star θ ⬝ᵥ ((bOp (eprProj (F := F) (n := n)) :
        Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ) := by
    rw [inner_evec, star_mulVec_dotProduct, hsa isWeylFamily_wX, ← bOp_mul, twirl_mul_twirl]
  obtain ⟨x, hxdef⟩ : ∃ x, x = (bOp (eprProj (F := F) (n := n)) :
      Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ := ⟨_, rfl⟩
  have hQsa : (bOp (eprProj (F := F) (n := n)) :
      Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ)ᴴ = bOp eprProj := by
    rw [bOp_conjTranspose, eprProj_conjTranspose]
  have hQid : (bOp (eprProj (F := F) (n := n)) :
      Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) * bOp eprProj
      = bOp eprProj := by rw [← bOp_mul, eprProj_mul_self]
  have hxsq : ‖evec x‖ ^ 2 = (inner ℂ (evec θ) (evec x) : ℂ).re := by
    rw [inner_evec, norm_evec_sq, hxdef, star_mulVec_dotProduct, hQsa, hQid]
  have hlow : 1 - (2 * Real.sqrt δ + 2 * δ) ≤ (inner ℂ (evec θ) (evec x) : ℂ).re := by
    rw [inner_evec, hxdef, ← hQ]
    linarith
  have hmain := norm_sub_normalize_sq_le hθn hxsq hlt hlow
  have hxpos : 0 < ‖evec x‖ := by
    have h2 : 0 < ‖evec x‖ ^ 2 := by rw [hxsq]; linarith
    nlinarith [norm_nonneg (evec x)]
  refine ⟨fun r => ((‖evec x‖⁻¹ : ℝ) : ℂ) * ∑ s, epr (F := F) (n := n) s * θ (r, s), ?_, ?_⟩
  all_goals {
    have heq : (auxVec (F := F) (n := n)
        fun r => ((‖evec x‖⁻¹ : ℝ) : ℂ) * ∑ s, epr (F := F) (n := n) s * θ (r, s))
        = ((‖evec x‖⁻¹ : ℝ) : ℂ) • x := by
      funext p
      obtain ⟨r, t⟩ := p
      show (((‖evec x‖⁻¹ : ℝ) : ℂ) * ∑ s, epr (F := F) (n := n) s * θ (r, s)) * epr t
        = ((‖evec x‖⁻¹ : ℝ) : ℂ) * x (r, t)
      rw [hxdef, bOp_eprProj_mulVec]
      ring
    rw [heq, evec_smul]
    first
      | (rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖evec x‖⁻¹), inv_mul_cancel₀ hxpos.ne'])
      | exact hmain
  }

end Item1

end MIPRE.QLD

end
