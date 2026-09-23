/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.SwapMeasure

/-!
# The descent: from the projective dilation to the strategy, through agreement

`MirrorSimul.swap_isometry` (`MIPRE/Background/QLD/SwapItemTwo.lean`) ends the swap isometry
lemma on a *legal projective* strategy, with a *closeness* statement: conjugated by the swap
unitary, the total Pauli measurement `C_h` is close to the honest projector `tau^W_h` on the
state `Δ = |aux> ⊗ |EPR_q>^M`. The theorem `thm:qld` quantifies over arbitrary POVM strategies
and conjugates the *original* measurement operators by an isometry `phi`, so two passages remain
--- from `V`-conjugation to `phi`-conjugation, and from the Naimark dilation back to the POVM
--- and neither preserves a closeness statement. What each preserves is an **agreement**: a
bilinear pairing `∑_h <Γ| X_h ⊗ T_h |Γ>` of one party's family against a family on the *other*
party. Such a pairing is linear in each family separately, so a pair of local isometries carries
it verbatim, from the pushed-forward state to the original one, with each family replaced by its
compression (`bornProb_kronecker_mulVec`): the dilation's `N^† P_h N = A_h`, and `phi`'s. This
is the paper's route, in the last paragraphs of the proof of `thm:pauli-appendix`; its `\cnote`
records that the step had been silent before adversarial review, precisely because Naimark
dilation preserves consistency and not closeness.

The file is that route, as generic linear algebra over three finite types: nothing here knows
about the Pauli basis test.

## The four moves

On `Δ`, `tau^W_h` on `A''` acts as `tau^W_h` on `B''` (the EPR pair is perfectly correlated);
that is the hypothesis `hmove`, and it turns every one-party deviation `aOp C_h - aOp tau_h` into
a cross-party one `aOp C_h - bOp T_h` on `Δ` (`snorm_aOp_sub_aOp_eq_of_move`). Then:

* **closeness to agreement** (`sum_snorm_sq_aOp_sub_bOp_eq`): for `C` and `T` projective the
  summed cross-party deviation is exactly `2 - 2 ∑_h <Δ| C_h ⊗ T_h |Δ>`;
* **moving the state** (`abs_sum_bornProb_sub_le`): the pairing operator `∑_h X_h ⊗ T_h` is a
  contraction whenever `X` is a sub-POVM and `T` projective (`bnd_sum_kronecker`), so moving the
  pairing from `Δ` to the pushed-forward state `Γ` and back costs `2 ‖Γ - Δ‖` each way;
* **the hypothesis `hagree`**: on `Γ` the pairing of the strategy's own family `X` is at least
  that of `C` --- in the application the two are *equal*, by the compression identity; the
  inequality is all the argument uses;
* **agreement to closeness** (`sum_snorm_sq_aOp_sub_bOp_le`): for a sub-POVM `X` against a
  projective `T` the summed deviation is at most `2 - 2 ∑_h <Δ| X_h ⊗ T_h |Δ>`, since
  `X_h² ≤ X_h` and the diagonal terms sum to at most one.

Put together (`sum_snorm_sq_descent_aOp`): a closeness `≤ c` of `C` to `tau` on `Δ` becomes a
closeness `≤ c + 8 r` of `X` to `tau` on `Δ`, where `r` bounds `‖Γ - Δ‖`. Neither conversion
takes a root: closeness to agreement is an identity for two projective families (item 2 of
`fact:agreement`), and agreement to closeness is linear (item 1), for a sub-POVM against a
projective family. The paper budgets a square root for the conversion back and absorbs it into
`delta_qld`; the argument does not need it. The only root in the chain is the one inside `r`,
since item 1 of the swap lemma bounds the *squared* distance.

Bob's half (`sum_snorm_sq_descent_bOp`) is Alice's on the swapped state: `swapVec` exchanges the
factors of every Kronecker product and of every Born probability, and preserves norms.

`sum_snorm_sq_descent_isometry_aOp` and `..._bOp` state the descent in the form the theorem
consumes: `Γ = (U_A ⊗ U_B) ψ` for local isometries, `X_h = U A_h U^†` for a POVM `A` on the
original space, and `hagree` discharged, with equality, by the compression `U^† C_h U = A_h`.

## Why the target family need not be a POVM

The statement allows the descended family `X` to be any **sub**-POVM (`0 ≤ X_h`, `∑_h X_h ≤ 1`):
that is what conjugation by an isometry produces. `phi A_h phi^†` has total mass `phi phi^†`, a
projection, not the identity (for the paper's `phi`, it is `P = V (Id ⊗ P_EPR) V^†`). Stated for
sub-POVMs, the passage from `V`-conjugation to `phi`-conjugation needs no argument of its own: it
is the same compression identity as the dilation's, and the two can be taken in one step, with
`X_h = phi A_h phi^†` for `phi` the composite of the dilation and the paper's embedding. The
paper's separate argument through the projection `P` is not needed.

The trivial bound `sum_snorm_sq_aOp_sub_aOp_le_two` --- the summed deviation of a sub-POVM from
`tau` on `Δ` is at most `2` --- discharges the statement whenever the error bound is at least
`2`, as in the regime the paper disposes of first (`16 md > q`).
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## A Born probability through a pair of local maps -/

section Pullback

variable {H K R S : Type*} [Fintype H] [Fintype K] [Fintype R] [Fintype S]

/-- **A Born probability of a state pushed through local maps is the Born probability of the
compressed operators.** `<(U ⊗ W) ψ| X ⊗ Y |(U ⊗ W) ψ> = <ψ| U^† X U ⊗ W^† Y W |ψ>`, for
rectangular `U` and `W`. With `U` an isometry and `X` a dilated POVM element this is the Naimark
identity the descent runs on: a pairing against *any* operator on the other side is carried
verbatim from the dilation to the POVM. -/
theorem bornProb_kronecker_mulVec (U : Matrix R H ℂ) (W : Matrix S K ℂ) (ψ : H × K → ℂ)
    (X : Matrix R R ℂ) (Y : Matrix S S ℂ) :
    bornProb ((U ⊗ₖ W) *ᵥ ψ) X Y = bornProb ψ (Uᴴ * X * U) (Wᴴ * Y * W) := by
  rw [bornProb, bornProb, dotProduct_mulVec_conj, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_assoc, Matrix.mul_assoc]

variable [DecidableEq H] [DecidableEq K]

omit [Fintype K] [Fintype S] [DecidableEq K] in
/-- An isometry compresses its own conjugate back: `U^† (U A U^†) U = A`. -/
theorem conjTranspose_mul_conj_mul {U : Matrix R H ℂ} (hU : Uᴴ * U = 1) (A : Matrix H H ℂ) :
    Uᴴ * (U * A * Uᴴ) * U = A := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU,
    Matrix.mul_one]

omit [DecidableEq K] in
/-- **Alice's family conjugated by her isometry pairs on the pushed-forward state as the family
itself on the original state.** -/
theorem bornProb_kronecker_mulVec_conj_left {U : Matrix R H ℂ} (hU : Uᴴ * U = 1)
    (W : Matrix S K ℂ) (ψ : H × K → ℂ) (A : Matrix H H ℂ) (Y : Matrix S S ℂ) :
    bornProb ((U ⊗ₖ W) *ᵥ ψ) (U * A * Uᴴ) Y = bornProb ψ A (Wᴴ * Y * W) := by
  rw [bornProb_kronecker_mulVec, conjTranspose_mul_conj_mul hU]

omit [DecidableEq H] in
/-- **...and Bob's likewise.** -/
theorem bornProb_kronecker_mulVec_conj_right (U : Matrix R H ℂ) {W : Matrix S K ℂ}
    (hW : Wᴴ * W = 1) (ψ : H × K → ℂ) (Y : Matrix R R ℂ) (B : Matrix K K ℂ) :
    bornProb ((U ⊗ₖ W) *ᵥ ψ) Y (W * B * Wᴴ) = bornProb ψ (Uᴴ * Y * U) B := by
  rw [bornProb_kronecker_mulVec, conjTranspose_mul_conj_mul hW]

omit [Fintype K] [Fintype S] [DecidableEq K] in
/-- **Conjugating a POVM by an isometry gives a sub-POVM**: each element stays positive, and the
elements sum to `U U^†`, a projection, hence at most the identity. -/
theorem conj_isometry_subPOVM {Λ : Type*} [Fintype Λ] [DecidableEq R] {U : Matrix R H ℂ}
    (hU : Uᴴ * U = 1) {A : Λ → Matrix H H ℂ} (hA0 : ∀ h, 0 ≤ A h) (hA1 : ∑ h, A h = 1) :
    (∀ h, 0 ≤ U * A h * Uᴴ) ∧ ∑ h, U * A h * Uᴴ ≤ 1 := by
  refine ⟨fun h => Matrix.nonneg_iff_posSemidef.mpr
    ((Matrix.nonneg_iff_posSemidef.mp (hA0 h)).mul_mul_conjTranspose_same U), ?_⟩
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, hA1, Matrix.mul_one]
  refine proj_le_one (by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]) ?_
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]

end Pullback

/-! ## Agreement and closeness across the cut -/

section Agreement

variable {N K Λ : Type*} [Fintype N] [DecidableEq N] [Fintype K] [DecidableEq K] [Fintype Λ]

omit [Fintype N] in
/-- A sub-POVM's elements are each below the identity. -/
theorem le_one_of_sum_le_one {X : Λ → Matrix N N ℂ} (hX0 : ∀ h, 0 ≤ X h)
    (hX1 : ∑ h, X h ≤ 1) (h : Λ) : X h ≤ 1 :=
  le_trans (Finset.single_le_sum (fun i _ => hX0 i) (mem_univ h)) hX1

/-- **Agreement to closeness, for a sub-POVM against a projective measurement.** The summed
cross-party deviation is at most twice the disagreement. Expand each square: the cross terms are
the Born probabilities (the two factors commute); Bob's diagonal terms sum to exactly one
(`T` is projective); Alice's are `<v| X_h² |v> ≤ <v| X_h |v>`, which sum to at most one. -/
theorem sum_snorm_sq_aOp_sub_bOp_le {v : N × K → ℂ} (hv : ‖evec v‖ = 1)
    {X : Λ → Matrix N N ℂ} (hX0 : ∀ h, 0 ≤ X h) (hX1 : ∑ h, X h ≤ 1)
    {T : Λ → Matrix K K ℂ} (hT : IsPVM T) :
    ∑ h, snorm v ((aOp (X h) : Matrix (N × K) (N × K) ℂ) - bOp (T h)) ^ 2
      ≤ 2 - 2 * ∑ h, bornProb v (X h) (T h) := by
  have hsa : ∀ h, (X h)ᴴ = X h := fun h =>
    (Matrix.nonneg_iff_posSemidef.mp (hX0 h)).isHermitian
  have hterm : ∀ h, snorm v ((aOp (X h) : Matrix (N × K) (N × K) ℂ) - bOp (T h)) ^ 2
      = qform v (aOp (X h * X h) : Matrix (N × K) (N × K) ℂ)
        + qform v (bOp (T h) : Matrix (N × K) (N × K) ℂ) - 2 * bornProb v (X h) (T h) := by
    intro h
    rw [snorm_sq_eq_qform, Matrix.conjTranspose_sub, aOp_conjTranspose, bOp_conjTranspose, hsa h,
      hT.isSelfAdjoint h,
      show ((aOp (X h) : Matrix (N × K) (N × K) ℂ) - bOp (T h)) * (aOp (X h) - bOp (T h))
          = aOp (X h) * aOp (X h) + bOp (T h) * bOp (T h) - aOp (X h) * bOp (T h)
            - bOp (T h) * aOp (X h) from by noncomm_ring,
      ← aOp_mul, ← bOp_mul, hT.idem h, ← aOp_mul_bOp, qform_sub, qform_sub, qform_add,
      ← bornProb_eq_qform]
    ring
  have hA : ∑ h, qform v (aOp (X h * X h) : Matrix (N × K) (N × K) ℂ) ≤ 1 := by
    calc ∑ h, qform v (aOp (X h * X h) : Matrix (N × K) (N × K) ℂ)
        ≤ ∑ h, qform v (aOp (X h) : Matrix (N × K) (N × K) ℂ) :=
          Finset.sum_le_sum fun h _ => qform_le_of_le v
            (aOp_mono (mul_self_le_of_le_one (hX0 h) (le_one_of_sum_le_one hX0 hX1 h)))
      _ = qform v (aOp (∑ h, X h) : Matrix (N × K) (N × K) ℂ) := by rw [aOp_sum, qform_sum]
      _ ≤ qform v (aOp 1 : Matrix (N × K) (N × K) ℂ) := qform_le_of_le v (aOp_mono hX1)
      _ = 1 := by rw [aOp_one, qform_one v hv]
  have hB : ∑ h, qform v (bOp (T h) : Matrix (N × K) (N × K) ℂ) = 1 := by
    rw [← qform_sum, ← bOp_sum, hT.sum_eq_one, bOp_one, qform_one v hv]
  rw [Finset.sum_congr rfl fun h (_ : h ∈ univ) => hterm h, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

/-- **Closeness and agreement determine each other, for two projective measurements.** The
equality case of `sum_snorm_sq_aOp_sub_bOp_le`: both diagonal sums are exactly one. -/
theorem sum_snorm_sq_aOp_sub_bOp_eq [DecidableEq Λ] {v : N × K → ℂ} (hv : ‖evec v‖ = 1)
    {X : Λ → Matrix N N ℂ} (hX : IsPVM X) {T : Λ → Matrix K K ℂ} (hT : IsPVM T) :
    ∑ h, snorm v ((aOp (X h) : Matrix (N × K) (N × K) ℂ) - bOp (T h)) ^ 2
      = 2 - 2 * ∑ h, bornProb v (X h) (T h) := by
  rw [sum_snorm_sq_sub_eq_two_sub hv hX.aOp hT.bOp]
  simp only [bornProb_eq_qform]

/-- **The pairing operator is a contraction.** For a sub-POVM `X` on one factor and a projective
`T` on the other, `O = ∑_h X_h ⊗ T_h` satisfies `0 ≤ O ≤ ∑_h Id ⊗ T_h = Id`, hence
`O^† O = O² ≤ O ≤ Id`. -/
theorem bnd_sum_kronecker {X : Λ → Matrix N N ℂ} (hX0 : ∀ h, 0 ≤ X h) (hX1 : ∑ h, X h ≤ 1)
    {T : Λ → Matrix K K ℂ} (hT : IsPVM T) :
    Bnd (∑ h, X h ⊗ₖ T h) 1 := by
  have h0 : (0 : Matrix (N × K) (N × K) ℂ) ≤ ∑ h, X h ⊗ₖ T h :=
    Finset.sum_nonneg fun h _ => Matrix.nonneg_iff_posSemidef.mpr
      ((Matrix.nonneg_iff_posSemidef.mp (hX0 h)).kronecker (hT.posSemidef h))
  have h1 : ∑ h, X h ⊗ₖ T h ≤ (1 : Matrix (N × K) (N × K) ℂ) := by
    have hsplit : (1 : Matrix (N × K) (N × K) ℂ) - ∑ h, X h ⊗ₖ T h
        = ∑ h, (1 - X h) ⊗ₖ T h := by
      have hone : (1 : Matrix (N × K) (N × K) ℂ) = ∑ h, (1 : Matrix N N ℂ) ⊗ₖ T h := by
        rw [← bOp_one (HA := N), ← hT.sum_eq_one, bOp_sum]
        rfl
      rw [hone, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun h _ => (sub_kronecker_right _ _ _).symm
    refine sub_nonneg.mp ?_
    rw [hsplit]
    exact Finset.sum_nonneg fun h _ => Matrix.nonneg_iff_posSemidef.mpr
      ((Matrix.nonneg_iff_posSemidef.mp
        (sub_nonneg.mpr (le_one_of_sum_le_one hX0 hX1 h))).kronecker (hT.posSemidef h))
  have hsa : (∑ h, X h ⊗ₖ T h)ᴴ = ∑ h, X h ⊗ₖ T h :=
    (Matrix.nonneg_iff_posSemidef.mp h0).isHermitian
  refine bnd_one_of_conjTranspose_mul_self_le ?_
  rw [hsa]
  exact le_trans (mul_self_le_of_le_one h0 h1) h1

/-- **Moving an agreement to a nearby state costs twice the distance.** The agreement is the
quadratic form of the pairing operator, which is a contraction (`bnd_sum_kronecker`). -/
theorem abs_sum_bornProb_sub_le {v w : N × K → ℂ} (hv : ‖evec v‖ ≤ 1) (hw : ‖evec w‖ ≤ 1)
    {X : Λ → Matrix N N ℂ} (hX0 : ∀ h, 0 ≤ X h) (hX1 : ∑ h, X h ≤ 1)
    {T : Λ → Matrix K K ℂ} (hT : IsPVM T) :
    |∑ h, bornProb v (X h) (T h) - ∑ h, bornProb w (X h) (T h)| ≤ 2 * ‖evec (v - w)‖ := by
  have hq : ∀ u : N × K → ℂ, ∑ h, bornProb u (X h) (T h) = qform u (∑ h, X h ⊗ₖ T h) :=
    fun u => by rw [qform_sum]; rfl
  rw [hq v, hq w]
  have := abs_qform_sub_qform_le v w zero_le_one (bnd_sum_kronecker hX0 hX1 hT) hv hw
  rwa [mul_one] at this

end Agreement

/-! ## The descent -/

section Descent

variable {N K Λ : Type*} [Fintype N] [DecidableEq N] [Fintype K] [DecidableEq K] [Fintype Λ]

/-- **On a state where `tau_h` on Alice's side acts as `T_h` on Bob's, a one-party deviation from
`tau_h` is the cross-party deviation from `T_h`.** -/
theorem snorm_aOp_sub_aOp_eq_of_move {Δ : N × K → ℂ} {τ : Matrix N N ℂ} {T : Matrix K K ℂ}
    (hmove : (aOp τ : Matrix (N × K) (N × K) ℂ) *ᵥ Δ = bOp T *ᵥ Δ) (A : Matrix N N ℂ) :
    snorm Δ ((aOp A : Matrix (N × K) (N × K) ℂ) - aOp τ)
      = snorm Δ ((aOp A : Matrix (N × K) (N × K) ℂ) - bOp T) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, hmove]

/-- **The descent, Alice's half.** Let `Δ` be a unit state on which `tau_h` on Alice's side acts
as the projective `T_h` on Bob's (`hmove`), and on which the projective family `C` is within `c`
of `tau`. Let `Γ` be a state within `r` of `Δ` on which a sub-POVM `X` agrees with `T` at least
as well as `C` does (`hagree`). Then `X` is within `c + 8 r` of `tau` on `Δ`.

Closeness of `C` is agreement with `T` on `Δ` (exactly, both being projective); it moves to `Γ`
at cost `2 r`; `hagree` passes it to `X`; it moves back at cost `2 r`; and agreement of the
sub-POVM `X` with the projective `T` is closeness, at twice the deficit. -/
theorem sum_snorm_sq_descent_aOp [DecidableEq Λ] {Δ Γ : N × K → ℂ} (hΔ : ‖evec Δ‖ = 1)
    (hΓ : ‖evec Γ‖ ≤ 1) {r : ℝ} (hr : ‖evec (Γ - Δ)‖ ≤ r) {C X τ : Λ → Matrix N N ℂ} (hC : IsPVM C)
    (hX0 : ∀ h, 0 ≤ X h) (hX1 : ∑ h, X h ≤ 1) {T : Λ → Matrix K K ℂ} (hT : IsPVM T)
    (hmove : ∀ h, (aOp (τ h) : Matrix (N × K) (N × K) ℂ) *ᵥ Δ = bOp (T h) *ᵥ Δ)
    (hagree : ∑ h, bornProb Γ (C h) (T h) ≤ ∑ h, bornProb Γ (X h) (T h))
    {c : ℝ} (hc : ∑ h, snorm Δ ((aOp (C h) : Matrix (N × K) (N × K) ℂ) - aOp (τ h)) ^ 2 ≤ c) :
    ∑ h, snorm Δ ((aOp (X h) : Matrix (N × K) (N × K) ℂ) - aOp (τ h)) ^ 2 ≤ c + 8 * r := by
  simp only [snorm_aOp_sub_aOp_eq_of_move (hmove _)] at hc ⊢
  rw [sum_snorm_sq_aOp_sub_bOp_eq hΔ hC hT] at hc
  have hd : ‖evec (Δ - Γ)‖ ≤ r := by rwa [evec_sub, norm_sub_rev, ← evec_sub]
  have hCΓ := abs_le.mp (abs_sum_bornProb_sub_le hΔ.le hΓ hC.nonneg hC.sum_eq_one.le hT)
  have hXΓ := abs_le.mp (abs_sum_bornProb_sub_le hΔ.le hΓ hX0 hX1 hT)
  have hX := sum_snorm_sq_aOp_sub_bOp_le hΔ hX0 hX1 hT
  linarith [hCΓ.1, hCΓ.2, hXΓ.1, hXΓ.2]

/-- **The trivial bound.** On a state where `tau_h` on Alice's side acts as the projective `T_h`
on Bob's, the summed deviation of any sub-POVM from `tau` is at most `2`: it is twice the
disagreement with `T`, and agreement is nonnegative. -/
theorem sum_snorm_sq_aOp_sub_aOp_le_two {Δ : N × K → ℂ} (hΔ : ‖evec Δ‖ = 1)
    {X τ : Λ → Matrix N N ℂ} (hX0 : ∀ h, 0 ≤ X h) (hX1 : ∑ h, X h ≤ 1)
    {T : Λ → Matrix K K ℂ} (hT : IsPVM T)
    (hmove : ∀ h, (aOp (τ h) : Matrix (N × K) (N × K) ℂ) *ᵥ Δ = bOp (T h) *ᵥ Δ) :
    ∑ h, snorm Δ ((aOp (X h) : Matrix (N × K) (N × K) ℂ) - aOp (τ h)) ^ 2 ≤ 2 := by
  simp only [snorm_aOp_sub_aOp_eq_of_move (hmove _)]
  have hX := sum_snorm_sq_aOp_sub_bOp_le hΔ hX0 hX1 hT
  have hnn : 0 ≤ ∑ h, bornProb Δ (X h) (T h) := Finset.sum_nonneg fun h _ =>
    bornProb_nonneg Δ (Matrix.nonneg_iff_posSemidef.mp (hX0 h)) (hT.posSemidef h)
  linarith

/-! ### Bob's half, on the swapped state -/

omit [DecidableEq N] in
/-- Bob's one-party deviation is Alice's on the swapped state. -/
theorem snorm_swapVec_aOp_sub_aOp (Δ : K × N → ℂ) (A B : Matrix N N ℂ) :
    snorm (swapVec Δ) ((aOp A : Matrix (N × K) (N × K) ℂ) - aOp B)
      = snorm Δ ((bOp A : Matrix (K × N) (K × N) ℂ) - bOp B) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, aOp, aOp, mulVec_kronecker_swapVec,
    mulVec_kronecker_swapVec, ← swapVec_sub, norm_swapVec, bOp, bOp]

/-- **The descent, Bob's half.** `sum_snorm_sq_descent_aOp` on the swapped state: the swap
exchanges the two factors of every Kronecker product (`mulVec_kronecker_swapVec`) and of every
Born probability (`bornProb_swapVec`), and preserves norms. -/
theorem sum_snorm_sq_descent_bOp [DecidableEq Λ] {Δ Γ : K × N → ℂ} (hΔ : ‖evec Δ‖ = 1)
    (hΓ : ‖evec Γ‖ ≤ 1) {r : ℝ} (hr : ‖evec (Γ - Δ)‖ ≤ r) {C X τ : Λ → Matrix N N ℂ} (hC : IsPVM C)
    (hX0 : ∀ h, 0 ≤ X h) (hX1 : ∑ h, X h ≤ 1) {T : Λ → Matrix K K ℂ} (hT : IsPVM T)
    (hmove : ∀ h, (bOp (τ h) : Matrix (K × N) (K × N) ℂ) *ᵥ Δ = aOp (T h) *ᵥ Δ)
    (hagree : ∑ h, bornProb Γ (T h) (C h) ≤ ∑ h, bornProb Γ (T h) (X h))
    {c : ℝ} (hc : ∑ h, snorm Δ ((bOp (C h) : Matrix (K × N) (K × N) ℂ) - bOp (τ h)) ^ 2 ≤ c) :
    ∑ h, snorm Δ ((bOp (X h) : Matrix (K × N) (K × N) ℂ) - bOp (τ h)) ^ 2 ≤ c + 8 * r := by
  simp only [← snorm_swapVec_aOp_sub_aOp] at hc ⊢
  refine sum_snorm_sq_descent_aOp ((norm_swapVec Δ).trans hΔ) ((norm_swapVec Γ).trans_le hΓ)
    (by rw [← swapVec_sub, norm_swapVec]; exact hr) hC hX0 hX1 hT (fun h => ?_) ?_ hc
  · rw [aOp, bOp, mulVec_kronecker_swapVec, mulVec_kronecker_swapVec]
    exact congrArg swapVec (hmove h)
  · simpa only [bornProb_swapVec] using hagree

/-- **The trivial bound, Bob's half.** -/
theorem sum_snorm_sq_bOp_sub_bOp_le_two {Δ : K × N → ℂ} (hΔ : ‖evec Δ‖ = 1)
    {X τ : Λ → Matrix N N ℂ} (hX0 : ∀ h, 0 ≤ X h) (hX1 : ∑ h, X h ≤ 1)
    {T : Λ → Matrix K K ℂ} (hT : IsPVM T)
    (hmove : ∀ h, (bOp (τ h) : Matrix (K × N) (K × N) ℂ) *ᵥ Δ = aOp (T h) *ᵥ Δ) :
    ∑ h, snorm Δ ((bOp (X h) : Matrix (K × N) (K × N) ℂ) - bOp (τ h)) ^ 2 ≤ 2 := by
  simp only [← snorm_swapVec_aOp_sub_aOp]
  refine sum_snorm_sq_aOp_sub_aOp_le_two ((norm_swapVec Δ).trans hΔ) hX0 hX1 hT fun h => ?_
  rw [aOp, bOp, mulVec_kronecker_swapVec, mulVec_kronecker_swapVec]
  exact congrArg swapVec (hmove h)

/-! ### Through a pair of local isometries

The form the theorem consumes: the pushed-forward state is `(U_A ⊗ U_B) ψ`, the family descended
to is `U A_h U^†` for a POVM `A` on the original space, and the agreement hypothesis is the
compression identity `U^† C_h U = A_h`, under which `hagree` holds with equality
(`bornProb_kronecker_mulVec_conj_left`). -/

omit [DecidableEq N] [DecidableEq K] in
/-- A pair of local isometries preserves the norm of the state. -/
theorem norm_evec_kronecker_mulVec {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H']
    [DecidableEq H'] {UA : Matrix N H ℂ} {UB : Matrix K H' ℂ} (hUA : UAᴴ * UA = 1)
    (hUB : UBᴴ * UB = 1) (ψ : H × H' → ℂ) : ‖evec ((UA ⊗ₖ UB) *ᵥ ψ)‖ = ‖evec ψ‖ :=
  norm_evec_mulVec_eq (by rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hUA,
    hUB, Matrix.one_kronecker_one]) ψ

/-- **The descent through a pair of isometries, Alice's half.** If the projective `C` is within
`c` of `tau` on `Δ`, and compresses under Alice's isometry `U_A` to the POVM `A`, then
`U_A A U_A^†` is within `c + 8 r` of `tau` on `Δ`, where `r` bounds the distance from `Δ` to the
pushed-forward state `(U_A ⊗ U_B) ψ`. -/
theorem sum_snorm_sq_descent_isometry_aOp [DecidableEq Λ] {H H' : Type*} [Fintype H]
    [DecidableEq H] [Fintype H'] [DecidableEq H'] {UA : Matrix N H ℂ} {UB : Matrix K H' ℂ}
    (hUA : UAᴴ * UA = 1) (hUB : UBᴴ * UB = 1) {ψ : H × H' → ℂ} (hψ : ‖evec ψ‖ = 1)
    {Δ : N × K → ℂ} (hΔ : ‖evec Δ‖ = 1) {r : ℝ} (hr : ‖evec ((UA ⊗ₖ UB) *ᵥ ψ - Δ)‖ ≤ r)
    {C τ : Λ → Matrix N N ℂ} (hC : IsPVM C) {A : Λ → Matrix H H ℂ} (hA0 : ∀ h, 0 ≤ A h)
    (hA1 : ∑ h, A h = 1) (hCA : ∀ h, UAᴴ * C h * UA = A h) {T : Λ → Matrix K K ℂ}
    (hT : IsPVM T) (hmove : ∀ h, (aOp (τ h) : Matrix (N × K) (N × K) ℂ) *ᵥ Δ = bOp (T h) *ᵥ Δ)
    {c : ℝ} (hc : ∑ h, snorm Δ ((aOp (C h) : Matrix (N × K) (N × K) ℂ) - aOp (τ h)) ^ 2 ≤ c) :
    ∑ h, snorm Δ ((aOp (UA * A h * UAᴴ) : Matrix (N × K) (N × K) ℂ) - aOp (τ h)) ^ 2
      ≤ c + 8 * r := by
  obtain ⟨hX0, hX1⟩ := conj_isometry_subPOVM hUA hA0 hA1
  refine sum_snorm_sq_descent_aOp hΔ ((norm_evec_kronecker_mulVec hUA hUB ψ).trans hψ).le hr hC
    hX0 hX1 hT hmove (le_of_eq (Finset.sum_congr rfl fun h _ => ?_)) hc
  rw [bornProb_kronecker_mulVec_conj_left hUA, bornProb_kronecker_mulVec, hCA]

/-- **The descent through a pair of isometries, Bob's half.** -/
theorem sum_snorm_sq_descent_isometry_bOp [DecidableEq Λ] {H H' : Type*} [Fintype H]
    [DecidableEq H] [Fintype H'] [DecidableEq H'] {UA : Matrix K H ℂ} {UB : Matrix N H' ℂ}
    (hUA : UAᴴ * UA = 1) (hUB : UBᴴ * UB = 1) {ψ : H × H' → ℂ} (hψ : ‖evec ψ‖ = 1)
    {Δ : K × N → ℂ} (hΔ : ‖evec Δ‖ = 1) {r : ℝ} (hr : ‖evec ((UA ⊗ₖ UB) *ᵥ ψ - Δ)‖ ≤ r)
    {C τ : Λ → Matrix N N ℂ} (hC : IsPVM C) {B : Λ → Matrix H' H' ℂ} (hB0 : ∀ h, 0 ≤ B h)
    (hB1 : ∑ h, B h = 1) (hCB : ∀ h, UBᴴ * C h * UB = B h) {T : Λ → Matrix K K ℂ}
    (hT : IsPVM T) (hmove : ∀ h, (bOp (τ h) : Matrix (K × N) (K × N) ℂ) *ᵥ Δ = aOp (T h) *ᵥ Δ)
    {c : ℝ} (hc : ∑ h, snorm Δ ((bOp (C h) : Matrix (K × N) (K × N) ℂ) - bOp (τ h)) ^ 2 ≤ c) :
    ∑ h, snorm Δ ((bOp (UB * B h * UBᴴ) : Matrix (K × N) (K × N) ℂ) - bOp (τ h)) ^ 2
      ≤ c + 8 * r := by
  obtain ⟨hX0, hX1⟩ := conj_isometry_subPOVM hUB hB0 hB1
  refine sum_snorm_sq_descent_bOp hΔ ((norm_evec_kronecker_mulVec hUA hUB ψ).trans hψ).le hr hC
    hX0 hX1 hT hmove (le_of_eq (Finset.sum_congr rfl fun h _ => ?_)) hc
  rw [bornProb_kronecker_mulVec_conj_right _ hUB, bornProb_kronecker_mulVec, hCB]

end Descent

end MIPRE.QLD

end
