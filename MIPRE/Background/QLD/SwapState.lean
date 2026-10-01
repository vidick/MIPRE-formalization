/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.SwapUnitary
public import MIPRE.Foundations.EPRContraction
public import MIPRE.Foundations.Introspection.RegisterModel

@[expose] public section

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

This file is that assembly. On the space `(C^q)^{(x) n} (x) (C^q)^{(x) n} (x) H` --- the two
ancilla halves adjacent as one register `T x T`, and everything else, the two parties' other
registers and spaces, as one Hilbert space `H` --- the twirls act through `regAct`, their product
is `regAct eprProj` by `twirl_mul_twirl`, and the range of `regAct eprProj` is exactly the vectors
of the form `EPR (x) aux` (`bOp_eprProj_mulVec`). So a state that is nearly invariant under both
twirls is close to a product `EPR (x) aux`, which is item 1.

## In a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The state of item 1 is a vector
`θ` of the `ℓ²` sum `Ampl (T x T) H` of an arbitrary complex Hilbert space `H` --- in use, a vector
of the register model `N.reg T` of a bipartite model, whose space is `Ampl (T x T) N.H` --- and a
matrix `P` of scalars on the two halves acts on it as `regAct P`
(`MIPRE/Foundations/EPRContraction.lean`), which in a register model is the product of the two
players' register operators (`BipartiteModel.expand_π_smulKron_one_mul`). The product state is
`auxVec aux = EPR (x) aux`, with `aux` a vector of `H`, and at `aux = N.ψ` it is the register
model's own state (`reg_ψ_eq_auxVec`). The contraction `∑_s EPR_s θ_s` is a finite sum of vectors of
`H`, so nothing needs `H` to be finite-dimensional; the matrix statement on `R x (T x T) → ℂ` is the
case `H = ℂ^R`, up to the order of the factors. The finite-register lemmas --- the twirl as a
self-adjoint idempotent, the entangled projector, `syn_mul_syn` --- are unchanged.

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

open scoped InnerProductSpace
open OperatorMatrix

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The state the swap isometry lands on: the maximally entangled pair on the two ancilla halves,
tensored with an auxiliary vector of everything else. -/
def auxVec (aux : H) : Ampl ((n → F) × (n → F)) H :=
  WithLp.toLp 2 fun t => epr (F := F) (n := n) t • aux

omit [CompleteSpace H] in
/-- The product state has the norm of its auxiliary vector, the entangled pair being a unit
vector. -/
theorem norm_auxVec (aux : H) : ‖auxVec (F := F) (n := n) aux‖ = ‖aux‖ := by
  rw [auxVec, norm_toLp_smul, ← Introspection.registerEPR_eq_weyl,
    Introspection.registerEPR_norm, one_mul]

omit [Field F] [Algebra (ZMod 2) F] [CompleteSpace H] in
theorem auxVec_smul (c : ℂ) (aux : H) :
    auxVec (F := F) (n := n) (c • aux) = c • auxVec (F := F) (n := n) aux := by
  ext t
  rw [auxVec, auxVec, PiLp.toLp_apply, PiLp.smul_apply, PiLp.toLp_apply, smul_comm]

omit [Field F] [Algebra (ZMod 2) F] in
/-- **The product state of a register model is its own state**: `N.reg T` is `N` with the
entangled pair adjoined. -/
theorem reg_ψ_eq_auxVec {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜]
    [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
    (N : BipartiteModel 𝒞 𝒜 ℬ) : (N.reg (n → F)).ψ = auxVec (F := F) (n := n) N.ψ :=
  rfl

omit [Field F] [Algebra (ZMod 2) F] in
/-- The twirl acts on the register as the average of the products of the two halves' Weyl
operators. -/
theorem regAct_twirl (w : (n → F) → Matrix (n → F) (n → F) ℂ) :
    regAct (H := H) (twirl w)
      = (Fintype.card (n → F) : ℂ)⁻¹ • ∑ u : n → F, regAct (w u ⊗ₖ w u) := by
  rw [twirl, regAct_smul, regAct_sum]

omit [Field F] [Algebra (ZMod 2) F] in
/-- **Applying `|EPR><EPR| (x) 1` produces a product vector**, which is where item 1's auxiliary
state comes from: the first factor is the maximally entangled state and the second is the partial
overlap with it. -/
theorem bOp_eprProj_mulVec (θ : Ampl ((n → F) × (n → F)) H) :
    regAct (eprProj (F := F) (n := n)) θ
      = auxVec (F := F) (n := n) (∑ s, epr (F := F) (n := n) s • θ s) := by
  rw [eprProj, regAct_vecMulVec]
  rfl

/-- **The state estimate of `lem:qld-swap`, item 1.**

A unit state that is nearly invariant under both Weyl twirls on its two ancilla halves is close to
a product `EPR (x) aux`. The two hypotheses are what the self-consistency of the exact Pauli
observables supplies after conjugation by the swap map (`swapU_conj_wTilde_X`,
`swapU_conj_wTilde_Z` carry `W~^e(u-tilde)` to `1 (x) tau^W(e u-tilde)` with no error), and they
are hypotheses here rather than conclusions: that self-consistency, at a *uniform* `u-tilde`, is
the paper's second item of `lem:qld-construct-the-paulis`.

The estimate itself is the appendix's, in the repaired form: `2 - 2 sqrt(1 - eta)` with
`eta = 2 sqrt(delta) + 2 delta`, which is `O(sqrt(delta))`. The state is any unit vector of
`Ampl (T x T) H`, and `aux` is a unit vector of `H`: the normalized contraction of `θ` against the
entangled pair. -/
theorem exists_auxVec_close (θ : Ampl ((n → F) × (n → F)) H) (hθ : ‖θ‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hlt : 2 * Real.sqrt δ + 2 * δ < 1)
    (hX : 1 - δ / 2 ≤ (⟪θ, regAct (twirl (wX (F := F) (n := n))) θ⟫_ℂ).re)
    (hZ : 1 - δ / 2 ≤ (⟪θ, regAct (twirl (wZ (F := F) (n := n))) θ⟫_ℂ).re) :
    ∃ aux : H, ‖aux‖ = 1 ∧
      ‖θ - auxVec (F := F) (n := n) aux‖ ^ 2
        ≤ 2 - 2 * Real.sqrt (1 - (2 * Real.sqrt δ + 2 * δ)) := by
  -- the lifted twirls and the lifted entangled projector are orthogonal projections
  have hPX : IsStarProjection (regAct (H := H) (twirl (wX (F := F) (n := n)))) :=
    isStarProjection_regAct (twirl_conjTranspose isWeylFamily_wX)
      (twirl_mul_self isWeylFamily_wX)
  have hPZ : IsStarProjection (regAct (H := H) (twirl (wZ (F := F) (n := n)))) :=
    isStarProjection_regAct (twirl_conjTranspose isWeylFamily_wZ)
      (twirl_mul_self isWeylFamily_wZ)
  have hPE : IsStarProjection (regAct (H := H) (eprProj (F := F) (n := n))) :=
    isStarProjection_regAct eprProj_conjTranspose eprProj_mul_self
  -- an orthogonal projection is a contraction, and its weight is the squared norm of the image
  have hle : ∀ {P : Ampl ((n → F) × (n → F)) H →L[ℂ] Ampl ((n → F) × (n → F)) H},
      IsStarProjection P → ‖P θ‖ ≤ 1 := fun hP => by
    have h := Op.bnd_one_of_isStarProjection hP θ
    rwa [hθ, mul_one] at h
  have hsq : ∀ {P : Ampl ((n → F) × (n → F)) H →L[ℂ] Ampl ((n → F) × (n → F)) H},
      IsStarProjection P → ‖P θ‖ ^ 2 = (⟪θ, P θ⟫_ℂ).re := fun {P} hP => by
    have h := Op.snorm_sq_eq_qform θ P
    rw [hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq] at h
    exact h
  have hXd := norm_sub_sq_le_of_re_inner_ge hθ (hle hPX) hX
  have hZd := norm_sub_sq_le_of_re_inner_ge hθ (hle hPZ) hZ
  have hin := re_inner_ge_of_two_close hδ hθ hXd hZd
  -- the overlap of the two twirled states is the weight on the entangled projector
  have hQ : ⟪regAct (H := H) (twirl (wX (F := F) (n := n))) θ,
        regAct (H := H) (twirl (wZ (F := F) (n := n))) θ⟫_ℂ
      = ⟪θ, regAct (H := H) (eprProj (F := F) (n := n)) θ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      hPX.isSelfAdjoint.star_eq, ← mul_apply_eq_comp, ← regAct_mul, twirl_mul_twirl]
  obtain ⟨x, hxdef⟩ : ∃ x, x = regAct (H := H) (eprProj (F := F) (n := n)) θ := ⟨_, rfl⟩
  have hxsq : ‖x‖ ^ 2 = (⟪θ, x⟫_ℂ).re := by
    rw [hxdef]
    exact hsq hPE
  have hlow : 1 - (2 * Real.sqrt δ + 2 * δ) ≤ (⟪θ, x⟫_ℂ).re := by
    rw [hxdef, ← hQ]
    linarith
  have hmain := norm_sub_normalize_sq_le hθ hxsq hlt hlow
  have hxpos : 0 < ‖x‖ := by
    have h2 : 0 < ‖x‖ ^ 2 := by rw [hxsq]; linarith
    nlinarith [norm_nonneg x]
  -- the projection is a product with the entangled pair, so its normalization is an `auxVec`
  have hx : x = auxVec (F := F) (n := n) (∑ s, epr (F := F) (n := n) s • θ s) := by
    rw [hxdef, bOp_eprProj_mulVec]
  refine ⟨((‖x‖⁻¹ : ℝ) : ℂ) • ∑ s, epr (F := F) (n := n) s • θ s, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      ← norm_auxVec (F := F) (n := n) (∑ s, epr (F := F) (n := n) s • θ s), ← hx,
      inv_mul_cancel₀ hxpos.ne']
  · rw [auxVec_smul, ← hx]
    exact hmain

end Item1

/-! ## The combinatorial core of the self-consistency chain

`lem:qld-pauli-selfcons` --- the paper's second item of `lem:qld-construct-the-paulis`, and the
hypothesis of `exists_auxVec_close` above --- turns on one algebraic identity, the justification of
its display `eq:qld-pulling-2b`: the syndrome projector at the probe `u-tilde` and the syndrome
projector at the probe `ind_m(u)` multiply to the projector onto the outcomes satisfying both
conditions. That identity is here; the approximation steps around it are not. -/

section Joint

/-- **Two syndrome projectors of the same Weyl family, at different probes, multiply to the joint
one.** Off the diagonal the spectral projectors annihilate each other, so only the eigenvalue
patterns lying in both level sets survive. -/
theorem syn_mul_syn {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w)
    (v v' : n → F) (a a' : F) :
    syn w v a * syn w v' a'
      = ∑ e ∈ univ.filter fun e => dotF e v = a ∧ dotF e v' = a', proj w e := by
  classical
  rw [syn, syn, Finset.sum_mul]
  have hterm : ∀ e ∈ univ.filter fun e : n → F => dotF e v = a,
      (proj w e * ∑ e' ∈ univ.filter fun e' : n → F => dotF e' v' = a', proj w e')
        = if dotF e v' = a' then proj w e else 0 := by
    intro e _
    rw [Finset.mul_sum]
    by_cases hs : dotF e v' = a'
    · rw [if_pos hs,
        Finset.sum_eq_single e
          (fun e' _ he' => by rw [proj_mul_proj hw, if_neg fun hh => he' hh.symm])
          fun hmem => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ e, hs⟩) hmem,
        proj_mul_proj hw, if_pos rfl]
    · rw [if_neg hs]
      refine Finset.sum_eq_zero fun e' he' => ?_
      refine (proj_mul_proj hw e e').trans (if_neg fun hh : e = e' => hs ?_)
      rw [hh]
      exact (Finset.mem_filter.mp he').2
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.filter_filter]

end Joint

end MIPRE.QLD

end

end
