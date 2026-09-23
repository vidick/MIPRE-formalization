/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Soundness

/-!
# `thm:qld` on the valid Pauli answers

`qld_soundness` is a statement about the **coarse** `(Pauli, W)` measurement
`C_h = ∑_{rdPauliVec a = h} M_a`, which reads every answer that is not of the form `.pauliAns h'`
as the cube vector `h = 0`. Its consumer, the introspection soundness theorem
(`TypedEstimates.quantumValue_ge_of_valid_isometric_images`), sums over the **valid** answers only,
`M_{pauliAns h}`. The paper never meets the difference: `cor:pauli-binary` and
`lem:intro-pauli-strat` index the answers to a Pauli question by `F_q^M` itself, so a malformed
answer does not exist there. This file is the bridge, and it needs no bound on the malformed mass.

The two measurements differ at one outcome. For `h ≠ 0` the fibre of `rdPauliVec` over `h` is
`{pauliAns h}`, so `C_h = M_{pauliAns h}` (`map_rdPauliVec_mats_of_ne`). At `h = 0`,
`C_0 = M_{pauliAns 0} + (every malformed answer)`. At that outcome two facts suffice.

* **The valid operator is dominated by the coarse one.** For a projective measurement,
  `M_{pauliAns h} = M_{pauliAns h} C_h` (`pauliAns_mul_map_rdPauliVec`), so the isometric image
  `X_V` of the valid operator is a contraction times the image `X_C` of the coarse one, and
  `‖X_V Δ‖ ≤ ‖X_C Δ‖` on every vector. Two triangle inequalities then give
  `‖(X_V - T) Δ‖ ≤ ‖(X_C - T) Δ‖ + 2 ‖T Δ‖` against any honest operator `T`
  (`snorm_aOp_isometricImage_sub_le`, `snorm_bOp_isometricImage_sub_le`).
* **The honest projector has weight `1/|Anc|`.** On `registerState ξ` with `ξ` a unit vector,
  `‖T Δ‖² = 1 / |Anc F m|` (`snorm_registerState_aOp_proj_sq`, `snorm_registerState_bOp_proj_sq`).
  The maximally entangled state gives an operator on one half the weight `tr / dimension`
  (`qform_epr_aOp`), and every Weyl spectral projector has trace one (`trace_proj_weylOf`), being
  the Fourier average of a family whose only operator of nonzero trace is the identity
  (`trace_wX`, `trace_wZ`).

So the malformed answers are paid for by the honest projector's own weight at the one outcome
where they can hide, and that weight is small because the honest projectors are rank one. Squaring,
`(y + 2t)² ≤ 2 y² + 8 t²`, gives the headline bounds (`sum_snorm_sq_valid_alice_le`,
`sum_snorm_sq_valid_bob_le`):

  `∑_h ‖(X_{V,h} - τ^W_h) Δ‖² ≤ 2 ∑_h ‖(X_{C,h} - τ^W_h) Δ‖² + 8 / |Anc F m|`,

and `|F| ≤ |Anc F m|` (`card_le_card_anc`) turns the additive term into `8 / q`. Both sides are
in exactly the operator form of `qld_soundness`'s item 2 on the right and of the consumer's
`hX`/`hZ` on the left, where `proj_weylOf_X` and `proj_weylOf_Z` rename the honest projectors to
the consumer's readouts. `qld_soundness_valid` is `qld_soundness` with item 2 so converted, for
strategies whose Pauli measurements are projective.

This is the converse direction to `isometric_valid_outcome_alice_error_le`, which passes from the
valid sum to the full coarse one and costs a square root; the passage from coarse to valid costs a
factor `2` and an additive `8 / |Anc|`, and no root.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl MIPRE.Introspection
open scoped Kronecker ComplexOrder MatrixOrder

section Trace

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : Type*} [Fintype n] [DecidableEq n]

omit [Algebra (ZMod 2) F] in
/-- **Only the identity among the `X`-type operators has nonzero trace**: a nonzero shift moves
every basis vector. -/
theorem trace_wX (a : n → F) :
    (wX a).trace = if a = 0 then (Fintype.card (n → F) : ℂ) else 0 := by
  simp [Matrix.trace, wX_apply]

/-- **Only the identity among the `Z`-type operators has nonzero trace**: a nontrivial sign
character sums to zero (`sum_sgn_trDot`). -/
theorem trace_wZ (b : n → F) :
    (wZ b).trace = if b = 0 then (Fintype.card (n → F) : ℂ) else 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, wZ_apply, if_true]
  split_ifs with h
  · subst h; simp [trDot_zero_left, sgn_zero]
  · simp_rw [trDot_comm b]; exact sum_sgn_trDot h

/-- **A spectral projector has trace one** as soon as the family's only operator of nonzero trace is
the identity: the Fourier average keeps the trace of `w 0` alone, divided by the dimension. -/
theorem trace_proj {w : (n → F) → Matrix (n → F) (n → F) ℂ}
    (hw : ∀ a, (w a).trace = if a = 0 then (Fintype.card (n → F) : ℂ) else 0) (e : n → F) :
    (proj w e).trace = 1 := by
  rw [proj_def, Matrix.trace_smul, Matrix.trace_sum]
  simp_rw [Matrix.trace_smul, hw, smul_eq_mul, mul_ite, mul_zero]
  simp [trDot_zero_left, sgn_zero]

/-- **The maximally entangled state weighs an operator on one half by its normalised trace.** -/
theorem qform_epr_aOp (X : Matrix (n → F) (n → F) ℂ) :
    qform (epr (F := F) (n := n)) (aOp X) = (Fintype.card (n → F) : ℝ)⁻¹ * X.trace.re := by
  have hv : (aOp X : Matrix ((n → F) × (n → F)) _ ℂ) *ᵥ epr (F := F) (n := n)
      = fun p => X p.1 p.2 * ((eprScale (F := F) (n := n) : ℝ) : ℂ) := by
    funext p
    obtain ⟨a, b⟩ := p
    rw [aOp, stateVec_entry, Finset.sum_eq_single b (fun k _ hk => by rw [epr_ne hk, mul_zero])
      (fun hmem => absurd (Finset.mem_univ b) hmem), epr_same]
  have hin : ∀ a : n → F, ∑ b : n → F, star (epr (F := F) (n := n)) (a, b)
      * (X a b * ((eprScale (F := F) (n := n) : ℝ) : ℂ))
      = ((eprScale (F := F) (n := n) ^ 2 : ℝ) : ℂ) * X a a := by
    intro a
    rw [Finset.sum_eq_single a (fun b _ hb => by
        rw [Pi.star_apply, epr_ne (Ne.symm hb), star_zero, zero_mul])
      (fun hmem => absurd (Finset.mem_univ a) hmem), Pi.star_apply, epr_same, RCLike.star_def,
      Complex.conj_ofReal]
    push_cast
    ring
  rw [qform, hv, dotProduct, Fintype.sum_prod_type]
  simp only [hin]
  rw [← Finset.mul_sum, Complex.re_ofReal_mul, eprScale_sq]
  rfl

end Trace

section Register

variable {I H K : Type*} [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]

/-- **An operator on Alice's register, on the register-first product state**, sees only the pair:
the auxiliary factor contributes its norm. -/
theorem snorm_registerState_aOp_aOp (ξ : H × K → ℂ) (X : Matrix I I ℂ) :
    snorm (registerState I ξ) (aOp (aOp X) : Matrix ((I × H) × (I × K)) _ ℂ)
      = snorm (registerEPR I) (aOp X : Matrix (I × I) _ ℂ) * ‖evec ξ‖ := by
  rw [snorm, snorm, registerState, aOp, aOp, aOp,
    show (1 : Matrix (I × K) (I × K) ℂ) = (1 : Matrix I I ℂ) ⊗ₖ (1 : Matrix K K ℂ) from
      one_kronecker_one.symm,
    mulVec_kron_kron_expVec, one_kronecker_one, one_mulVec, norm_evec_expVec]

/-- **And one on Bob's register.** -/
theorem snorm_registerState_bOp_aOp (ξ : H × K → ℂ) (X : Matrix I I ℂ) :
    snorm (registerState I ξ) (bOp (aOp X) : Matrix ((I × H) × (I × K)) _ ℂ)
      = snorm (registerEPR I) (bOp X : Matrix (I × I) _ ℂ) * ‖evec ξ‖ := by
  rw [snorm, snorm, registerState, bOp, bOp, aOp,
    show (1 : Matrix (I × H) (I × H) ℂ) = (1 : Matrix I I ℂ) ⊗ₖ (1 : Matrix H H ℂ) from
      one_kronecker_one.symm,
    mulVec_kron_kron_expVec, one_kronecker_one, one_mulVec, norm_evec_expVec]

end Register

section Readouts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}

/-- The trace of either Weyl family. -/
theorem trace_weylOf (W : Bas) (a : Anc F m) :
    (weylOf W a).trace = if a = 0 then (Fintype.card (Anc F m) : ℂ) else 0 := by
  cases W
  exacts [trace_wX a, trace_wZ a]

/-- **The honest projectors are rank one**: each has trace one. -/
theorem trace_proj_weylOf (W : Bas) (h : Anc F m) : (proj (weylOf W) h).trace = 1 :=
  trace_proj (trace_weylOf W) h

/-- The honest projector's weight on the maximally entangled pair. -/
theorem snorm_epr_aOp_proj_sq (W : Bas) (h : Anc F m) :
    snorm (epr (F := F) (n := Fin m → Bool))
        (aOp (proj (weylOf W) h) : Matrix (Anc F m × Anc F m) _ ℂ) ^ 2
      = 1 / Fintype.card (Anc F m) := by
  have hw : IsWeylFamily (weylOf (F := F) (m := m) W) := by
    cases W
    exacts [isWeylFamily_wX, isWeylFamily_wZ]
  have hP := isPVM_proj hw
  rw [snorm_sq_eq_qform, aOp_conjTranspose, ← aOp_mul, hP.isSelfAdjoint h, hP.idem h,
    qform_epr_aOp, trace_proj_weylOf, Complex.one_re, mul_one, one_div]

/-- The honest projector acts on either half of the pair alike, being symmetric. -/
theorem snorm_epr_bOp_proj (W : Bas) (h : Anc F m) :
    snorm (epr (F := F) (n := Fin m → Bool))
        (bOp (proj (weylOf W) h) : Matrix (Anc F m × Anc F m) _ ℂ)
      = snorm (epr (F := F) (n := Fin m → Bool))
        (aOp (proj (weylOf W) h) : Matrix (Anc F m × Anc F m) _ ℂ) := by
  have htr : (bOp (proj (weylOf W) h) : Matrix (Anc F m × Anc F m) _ ℂ)
      *ᵥ (epr (F := F) (n := Fin m → Bool))
        = (aOp (proj (weylOf W) h) : Matrix (Anc F m × Anc F m) _ ℂ) *ᵥ epr :=
    congrArg WithLp.ofLp (stateVec_epr_proj (fun a => by
      cases W
      exacts [wX_transpose a, wZ_transpose a]) h).symm
  rw [snorm, snorm, htr]

variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

/-- **The honest projector's weight on Alice's register is `1 / |Anc F m|`**, on the register-first
product state with a unit auxiliary factor. This is the only price of the malformed answers. -/
theorem snorm_registerState_aOp_proj_sq (ξ : HA × HB → ℂ) (hξ : ‖evec ξ‖ = 1) (W : Bas)
    (h : Anc F m) :
    snorm (registerState (Anc F m) ξ)
        (aOp (aOp (proj (weylOf W) h)) :
          Matrix ((Anc F m × HA) × (Anc F m × HB)) _ ℂ) ^ 2
      = 1 / Fintype.card (Anc F m) := by
  rw [snorm_registerState_aOp_aOp, hξ, mul_one, registerEPR_eq_weyl, snorm_epr_aOp_proj_sq]

/-- **And on Bob's.** -/
theorem snorm_registerState_bOp_proj_sq (ξ : HA × HB → ℂ) (hξ : ‖evec ξ‖ = 1) (W : Bas)
    (h : Anc F m) :
    snorm (registerState (Anc F m) ξ)
        (bOp (aOp (proj (weylOf W) h)) :
          Matrix ((Anc F m × HA) × (Anc F m × HB)) _ ℂ) ^ 2
      = 1 / Fintype.card (Anc F m) := by
  rw [snorm_registerState_bOp_aOp, hξ, mul_one, registerEPR_eq_weyl, snorm_epr_bOp_proj,
    snorm_epr_aOp_proj_sq]

omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F] in
/-- **The ancilla is at least as large as the field**: `|Anc F m| = q^{2^m}`. -/
theorem card_le_card_anc : Fintype.card F ≤ Fintype.card (Anc F m) := by
  rw [Fintype.card_fun]
  exact Nat.le_self_pow (by simp) _

omit [DecidableEq F] [Algebra (ZMod 2) F] in
/-- So a constant over the ancilla's dimension is at most the same constant over `q`. -/
theorem div_card_anc_le {c : ℝ} (hc : 0 ≤ c) :
    c / Fintype.card (Anc F m) ≤ c / Fintype.card F :=
  div_le_div_of_nonneg_left hc (by exact_mod_cast Fintype.card_pos)
    (by exact_mod_cast card_le_card_anc)

end Readouts

section Dominate

variable {R H S : Type*} [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype S] [DecidableEq S]

/-- **A sub-projection of the coarse operator is no farther from an honest operator than the coarse
one, up to twice the honest operator's weight.** If `P C = P` with `P` a projector, the isometric
image of `P` is a contraction times that of `C`, so it is dominated by it on every vector; the rest
is two triangle inequalities. -/
theorem snorm_aOp_isometricImage_sub_le (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    {P C : Matrix H H ℂ} (hPsa : Pᴴ = P) (hPidem : P * P = P) (hPC : P * C = P)
    (v : R × S → ℂ) (T : Matrix R R ℂ) :
    snorm v (aOp (isometricImage V P - T))
      ≤ snorm v (aOp (isometricImage V C - T)) + 2 * snorm v (aOp T) := by
  have hX : isometricImage V P = isometricImage V P * isometricImage V C := by
    rw [isometricImage_mul V hV, hPC]
  have hsa : (isometricImage V P)ᴴ = isometricImage V P := by
    rw [isometricImage_conjTranspose, hPsa]
  have hid : isometricImage V P * isometricImage V P = isometricImage V P := by
    rw [isometricImage_mul V hV, hPidem]
  have hbnd : Bnd (aOp (isometricImage V P) : Matrix (R × S) _ ℂ) 1 :=
    bnd_aOp (by rw [hsa, hid]; exact proj_le_one hsa hid)
  have h1 : snorm v (aOp (isometricImage V P)) ≤ snorm v (aOp (isometricImage V C)) := by
    calc snorm v (aOp (isometricImage V P))
        = snorm v (aOp (isometricImage V P) * aOp (isometricImage V C)) := by
          rw [← aOp_mul, ← hX]
      _ ≤ 1 * snorm v (aOp (isometricImage V C)) := snorm_mul_le v hbnd _
      _ = _ := one_mul _
  have h2 : snorm v (aOp (isometricImage V C))
      ≤ snorm v (aOp (isometricImage V C - T)) + snorm v (aOp T) := by
    calc snorm v (aOp (isometricImage V C))
        = snorm v (aOp (isometricImage V C - T) + aOp T) := by rw [aOp_sub, sub_add_cancel]
      _ ≤ _ := snorm_add_le v _ _
  have h3 : snorm v (aOp (isometricImage V P - T))
      ≤ snorm v (aOp (isometricImage V P)) + snorm v (aOp T) := by
    rw [aOp_sub]
    exact snorm_sub_le v _ _
  linarith

/-- **The same on Bob's side.** -/
theorem snorm_bOp_isometricImage_sub_le (V : Matrix S H ℂ) (hV : Vᴴ * V = 1)
    {P C : Matrix H H ℂ} (hPsa : Pᴴ = P) (hPidem : P * P = P) (hPC : P * C = P)
    (v : R × S → ℂ) (T : Matrix S S ℂ) :
    snorm v (bOp (isometricImage V P - T))
      ≤ snorm v (bOp (isometricImage V C - T)) + 2 * snorm v (bOp T) := by
  have hX : isometricImage V P = isometricImage V P * isometricImage V C := by
    rw [isometricImage_mul V hV, hPC]
  have hsa : (isometricImage V P)ᴴ = isometricImage V P := by
    rw [isometricImage_conjTranspose, hPsa]
  have hid : isometricImage V P * isometricImage V P = isometricImage V P := by
    rw [isometricImage_mul V hV, hPidem]
  have hbnd : Bnd (bOp (isometricImage V P) : Matrix (R × S) _ ℂ) 1 :=
    bnd_bOp (by rw [hsa, hid]; exact proj_le_one hsa hid)
  have h1 : snorm v (bOp (isometricImage V P)) ≤ snorm v (bOp (isometricImage V C)) := by
    calc snorm v (bOp (isometricImage V P))
        = snorm v (bOp (isometricImage V P) * bOp (isometricImage V C)) := by
          rw [← bOp_mul, ← hX]
      _ ≤ 1 * snorm v (bOp (isometricImage V C)) := snorm_mul_le v hbnd _
      _ = _ := one_mul _
  have h2 : snorm v (bOp (isometricImage V C))
      ≤ snorm v (bOp (isometricImage V C - T)) + snorm v (bOp T) := by
    calc snorm v (bOp (isometricImage V C))
        = snorm v (bOp (isometricImage V C - T) + bOp T) := by rw [bOp_sub, sub_add_cancel]
      _ ≤ _ := snorm_add_le v _ _
  have h3 : snorm v (bOp (isometricImage V P - T))
      ≤ snorm v (bOp (isometricImage V P)) + snorm v (bOp T) := by
    rw [bOp_sub]
    exact snorm_sub_le v _ _
  linarith

/-- The squared form of the domination, with the honest term's square known. -/
theorem sq_le_two_mul_sq_add {x y t c : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y + 2 * t)
    (ht : t ^ 2 = c) : x ^ 2 ≤ 2 * y ^ 2 + 8 * c := by
  have h1 : x ^ 2 ≤ (y + 2 * t) ^ 2 := pow_le_pow_left₀ hx hxy 2
  nlinarith [sq_nonneg (y - 2 * t)]

end Dominate

section Fibre

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}
  {D : Type*} [Fintype D] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
/-- A valid answer lies in its own fibre. -/
theorem mem_filter_rdPauliVec (h : Anc F m) :
    Answer.pauliAns (d := d) h ∈ (univ.filter fun a : Answer F m d => rdPauliVec a = h) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

/-- **Away from `0` the coarse Pauli measurement is the valid answer**: a malformed answer reads as
`0`, so the fibre over `h ≠ 0` is `{pauliAns h}`. -/
theorem map_rdPauliVec_mats_of_ne (M : POVM (Answer F m d) D) {h : Anc F m} (hh : h ≠ 0) :
    ((M.map rdPauliVec).mats h).val = (M.mats (.pauliAns h)).val := by
  rw [POVM.map_mats, Finset.sum_eq_single_of_mem (Answer.pauliAns h) (mem_filter_rdPauliVec h)]
  intro a ha hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  exfalso
  cases a <;> simp_all [rdPauliVec]

/-- **For a projective measurement, the valid answer is a sub-projection of its coarse outcome**:
it absorbs its own fibre, the other answers there being orthogonal to it. -/
theorem pauliAns_mul_map_rdPauliVec (M : POVM (Answer F m d) D)
    (hM : IsPVM fun a => (M.mats a).val) (h : Anc F m) :
    (M.mats (.pauliAns h)).val * ((M.map rdPauliVec).mats h).val
      = (M.mats (.pauliAns h)).val := by
  rw [POVM.map_mats, Finset.mul_sum,
    Finset.sum_eq_single_of_mem (Answer.pauliAns h) (mem_filter_rdPauliVec h)]
  · exact hM.idem _
  · intro b _ hb
    exact hM.orthogonal (Ne.symm hb)

end Fibre

section Valid

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

omit [Algebra (ZMod 2) F] in
/-- Summing a pointwise bound that pays `8 c` at `h = 0` only. -/
theorem sum_sq_le_of_pointwise {x y : Anc F m → ℝ} {c : ℝ}
    (hpt : ∀ h, x h ^ 2 ≤ 2 * y h ^ 2 + if h = 0 then 8 * c else 0) :
    ∑ h, x h ^ 2 ≤ 2 * ∑ h, y h ^ 2 + 8 * c := by
  calc ∑ h, x h ^ 2 ≤ ∑ h, (2 * y h ^ 2 + if h = 0 then 8 * c else 0) :=
        Finset.sum_le_sum fun h _ => hpt h
    _ = 2 * ∑ h, y h ^ 2 + 8 * c := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' univ (0 : Anc F m),
          if_pos (Finset.mem_univ _)]

/-- **Item 2 of `thm:qld`, Alice, on the valid answers.** For a projective measurement `M` and an
isometry `V` with its register first, the summed squared error of the valid answers
`M_{pauliAns h}` against the honest projectors is at most twice that of the coarse measurement plus
`8 / |Anc F m|`. The left side is the operator form of the consumer's `hX`, the coarse sum that of
`qld_soundness`'s item 2. No bound on the malformed answers is assumed. -/
theorem sum_snorm_sq_valid_alice_le {dA : Type*} [Fintype dA] [DecidableEq dA]
    (V : Matrix (Anc F m × HA) dA ℂ) (hV : Vᴴ * V = 1) (M : POVM (Answer F m d) dA)
    (hM : IsPVM fun a => (M.mats a).val) (ξ : HA × HB → ℂ) (hξ : ‖evec ξ‖ = 1) (W : Bas) :
    ∑ h : Anc F m, snorm (registerState (Anc F m) ξ)
        (aOp (isometricImage V (M.mats (.pauliAns h)).val - aOp (proj (weylOf W) h))) ^ 2
      ≤ 2 * ∑ h : Anc F m, snorm (registerState (Anc F m) ξ)
        (aOp (isometricImage V ((M.map rdPauliVec).mats h).val
          - aOp (proj (weylOf W) h))) ^ 2
        + 8 / Fintype.card (Anc F m) := by
  rw [show (8 : ℝ) / Fintype.card (Anc F m) = 8 * (1 / Fintype.card (Anc F m)) by ring]
  refine sum_sq_le_of_pointwise fun h => ?_
  by_cases h0 : h = 0
  · rw [if_pos h0]
    exact sq_le_two_mul_sq_add (snorm_nonneg _ _)
      (snorm_aOp_isometricImage_sub_le V hV (hM.isSelfAdjoint _) (hM.idem _)
        (pauliAns_mul_map_rdPauliVec M hM h) _ _)
      (snorm_registerState_aOp_proj_sq ξ hξ W h)
  · rw [if_neg h0, add_zero, map_rdPauliVec_mats_of_ne M h0]
    nlinarith [sq_nonneg (snorm (registerState (Anc F m) ξ)
      (aOp (isometricImage V (M.mats (.pauliAns h)).val - aOp (proj (weylOf W) h)) :
        Matrix ((Anc F m × HA) × (Anc F m × HB)) _ ℂ))]

/-- **Item 2 of `thm:qld`, Bob, on the valid answers**: the operator form of the consumer's `hZ`. -/
theorem sum_snorm_sq_valid_bob_le {dB : Type*} [Fintype dB] [DecidableEq dB]
    (V : Matrix (Anc F m × HB) dB ℂ) (hV : Vᴴ * V = 1) (M : POVM (Answer F m d) dB)
    (hM : IsPVM fun a => (M.mats a).val) (ξ : HA × HB → ℂ) (hξ : ‖evec ξ‖ = 1) (W : Bas) :
    ∑ h : Anc F m, snorm (registerState (Anc F m) ξ)
        (bOp (isometricImage V (M.mats (.pauliAns h)).val - aOp (proj (weylOf W) h))) ^ 2
      ≤ 2 * ∑ h : Anc F m, snorm (registerState (Anc F m) ξ)
        (bOp (isometricImage V ((M.map rdPauliVec).mats h).val
          - aOp (proj (weylOf W) h))) ^ 2
        + 8 / Fintype.card (Anc F m) := by
  rw [show (8 : ℝ) / Fintype.card (Anc F m) = 8 * (1 / Fintype.card (Anc F m)) by ring]
  refine sum_sq_le_of_pointwise fun h => ?_
  by_cases h0 : h = 0
  · rw [if_pos h0]
    exact sq_le_two_mul_sq_add (snorm_nonneg _ _)
      (snorm_bOp_isometricImage_sub_le V hV (hM.isSelfAdjoint _) (hM.idem _)
        (pauliAns_mul_map_rdPauliVec M hM h) _ _)
      (snorm_registerState_bOp_proj_sq ξ hξ W h)
  · rw [if_neg h0, add_zero, map_rdPauliVec_mats_of_ne M h0]
    nlinarith [sq_nonneg (snorm (registerState (Anc F m) ξ)
      (bOp (isometricImage V (M.mats (.pauliAns h)).val - aOp (proj (weylOf W) h)) :
        Matrix ((Anc F m × HA) × (Anc F m × HB)) _ ℂ))]

end Valid

/-! ## `thm:qld` with item 2 on the valid answers -/

/-- **`thm:qld` for projective Pauli measurements, with item 2 on the valid answers.** The
isometries, the auxiliary state and item 1 are those of `qld_soundness`; item 2 is summed over the
answers `.pauliAns h` alone, at twice the coarse bound plus `8 / q`
(`sum_snorm_sq_valid_alice_le`, `sum_snorm_sq_valid_bob_le`, `div_card_anc_le`). Only the two
Pauli questions' measurements need be projective. -/
theorem qld_soundness_valid :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
        [NeZero m] (hm : m ∣ Fintype.card F), 1 ≤ d →
      ∀ {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
        (ψ : dA × dB → ℂ), star ψ ⬝ᵥ ψ = 1 →
      ∀ (MA : Question F m → POVM (Answer F m d) dA)
        (MB : Question F m → POVM (Answer F m d) dB),
        (∀ W : Bas, IsPVM fun a => ((MA (.pauli W)).mats a).val) →
        (∀ W : Bas, IsPVM fun a => ((MB (.pauli W)).mats a).val) →
        ∀ {ε : ℝ}, 0 ≤ ε → 1 - povmValue (qldGame hm) ψ MA MB ≤ ε →
      ∃ (HA HB : Type) (_ : Fintype HA) (_ : DecidableEq HA) (_ : Fintype HB)
        (_ : DecidableEq HB) (VA : Matrix (Anc F m × HA) dA ℂ) (VB : Matrix (Anc F m × HB) dB ℂ)
        (aux : HA × HB → ℂ),
        VAᴴ * VA = 1 ∧ VBᴴ * VB = 1 ∧ ‖evec aux‖ = 1 ∧
        ‖evec (isometricState VA VB ψ - registerState (Anc F m) aux)‖
          ≤ errShape a b ε m d (Fintype.card F) ∧
        ∀ W : Bas,
          ∑ h : Anc F m, snorm (registerState (Anc F m) aux)
              (aOp (isometricImage VA ((MA (.pauli W)).mats (.pauliAns h)).val
                - aOp (proj (weylOf W) h))) ^ 2
            ≤ 2 * errShape a b ε m d (Fintype.card F) + 8 / Fintype.card F ∧
          ∑ h : Anc F m, snorm (registerState (Anc F m) aux)
              (bOp (isometricImage VB ((MB (.pauli W)).mats (.pauliAns h)).val
                - aOp (proj (weylOf W) h))) ^ 2
            ≤ 2 * errShape a b ε m d (Fintype.card F) + 8 / Fintype.card F := by
  obtain ⟨a, b, ha, hb0, hb1, H⟩ := qld_soundness
  refine ⟨a, b, ha, hb0, hb1, ?_⟩
  intro F _ _ _ _ m d _ hm hd dA dB _ _ _ _ ψ hψ MA MB hpA hpB ε hε hfail
  obtain ⟨HA, HB, i1, i2, i3, i4, VA, VB, aux, hA, hB, haux, h1, h2⟩ :=
    H hm hd ψ hψ MA MB hε hfail
  have hc : (8 : ℝ) / Fintype.card (Anc F m) ≤ 8 / Fintype.card F :=
    div_card_anc_le (by norm_num)
  refine ⟨HA, HB, i1, i2, i3, i4, VA, VB, aux, hA, hB, haux, h1, fun W => ⟨?_, ?_⟩⟩
  · have hv := sum_snorm_sq_valid_alice_le VA hA (MA (.pauli W)) (hpA W) aux haux W
    linarith [(h2 W).1]
  · have hv := sum_snorm_sq_valid_bob_le VB hB (MB (.pauli W)) (hpB W) aux haux W
    linarith [(h2 W).2]

end MIPRE.QLD

end
