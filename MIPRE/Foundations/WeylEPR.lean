/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Weyl
import MIPRE.Foundations.StateDistance

/-!
# The maximally entangled state of the Weyl system

`|EPR_q⟩^{⊗ n}` on two copies of `(C^q)^{⊗ n}`, normalized, and the one property the Pauli basis
test uses it for: **the two parties' Weyl operators act identically on it.**

That property is the reason the expansion stage of the appendix works at all. Its expanded state
adjoins `|EPR_q⟩^{⊗ M}` to each player, and the sign `(-1)^γ` that the strategy's own observables
carry is cancelled against one the *ancilla* observables carry; for that the ancilla halves must
be tied together, and `stateVec_epr_wX`/`stateVec_epr_wZ` is the tie.

## The general fact, and why the Weyl case is clean

For any operator, `(M ⊗ Id)|EPR⟩ = (Id ⊗ Mᵗ)|EPR⟩` (`stateVec_epr`) --- the maximally entangled
state transports an operator to the other factor at the cost of a transpose. Generalized Paulis
over a field of characteristic two are *real symmetric* matrices, so the transpose is the
identity map on them and the cost vanishes. Over `F_p` for odd `p` it would not: `τ^Z(b)` has
entries `ω^{tr(bj)}`, whose transpose is `τ^Z(b)` but whose conjugate is `τ^Z(-b)`, and the
bookkeeping reappears. This is the second dividend of the characteristic-two restriction, after
the operators being involutions.
-/

noncomputable section

namespace MIPRE.Weyl

open Finset Matrix MIPRE
open scoped Kronecker

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]

set_option linter.unusedSectionVars false

/-! ## The state -/

/-- The normalizing scalar `1/√N` of the maximally entangled state, `N = q^n`. -/
def eprScale : ℝ := (Real.sqrt (Fintype.card (n → F)))⁻¹

/-- **The normalized maximally entangled state** on two copies of `(C^q)^{⊗ n}`. -/
def epr : (n → F) × (n → F) → ℂ :=
  fun p => if p.1 = p.2 then ((eprScale (F := F) (n := n) : ℝ) : ℂ) else 0

@[simp] theorem epr_same (a : n → F) :
    epr (a, a) = ((eprScale (F := F) (n := n) : ℝ) : ℂ) := if_pos rfl

theorem epr_ne {a b : n → F} (h : a ≠ b) : epr (F := F) (n := n) (a, b) = 0 := if_neg h

theorem eprScale_sq : (eprScale (F := F) (n := n)) ^ 2 = (Fintype.card (n → F) : ℝ)⁻¹ := by
  have hpos : (0 : ℝ) < Fintype.card (n → F) := by
    exact_mod_cast Fintype.card_pos (α := n → F)
  rw [eprScale, inv_pow, Real.sq_sqrt hpos.le]

/-- The state is a unit vector. -/
theorem epr_unit : star (epr (F := F) (n := n)) ⬝ᵥ epr = 1 := by
  classical
  have hcard : (Fintype.card (n → F) : ℂ) ≠ 0 := card_ne_zero
  rw [dotProduct]
  have hterm : ∀ p : (n → F) × (n → F),
      star (epr (F := F) (n := n)) p * epr p
        = if p.1 = p.2 then ((eprScale (F := F) (n := n) ^ 2 : ℝ) : ℂ) else 0 := by
    intro p
    rw [Pi.star_apply, epr]
    by_cases h : p.1 = p.2
    · rw [if_pos h, if_pos h, RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, sq]
    · rw [if_neg h, if_neg h, star_zero, mul_zero]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hterm p, eprScale_sq, ← Finset.sum_filter]
  have hdiag : {p ∈ (univ : Finset ((n → F) × (n → F))) | p.1 = p.2}
      = (univ : Finset (n → F)).diag := by
    ext p
    simp [Finset.mem_diag]
  rw [hdiag, Finset.sum_const, Finset.diag_card, Finset.card_univ, nsmul_eq_mul]
  push_cast
  rw [mul_inv_cancel₀ hcard]

/-! ## Transport to the other factor -/

theorem stateVec_entry (ψ : (n → F) × (n → F) → ℂ) (M : Matrix (n → F) (n → F) ℂ)
    (a b : n → F) :
    ((M ⊗ₖ (1 : Matrix (n → F) (n → F) ℂ)) *ᵥ ψ) (a, b) = ∑ k, M a k * ψ (k, b) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply,
    Finset.sum_ite_eq, mul_comm]

/-- **The maximally entangled state transports an operator to the other factor**, at the cost of
a transpose: `(M ⊗ Id)|EPR⟩ = (Id ⊗ Mᵗ)|EPR⟩`. -/
theorem stateVec_epr (M : Matrix (n → F) (n → F) ℂ) :
    stateVec (epr (F := F) (n := n)) M = stateVecB epr Mᵀ := by
  classical
  show WithLp.toLp 2 _ = WithLp.toLp 2 _
  congr 1
  funext p
  obtain ⟨a, b⟩ := p
  rw [stateVec_entry, stateVecB_entry,
    Finset.sum_eq_single b (fun k _ hk => by rw [epr_ne hk, mul_zero])
      fun hmem => absurd (Finset.mem_univ b) hmem,
    Finset.sum_eq_single a (fun l _ hl => by rw [epr_ne (Ne.symm hl), mul_zero])
      fun hmem => absurd (Finset.mem_univ a) hmem,
    Matrix.transpose_apply, epr_same, epr_same]

/-! ## The Weyl operators are symmetric

So the transpose in `stateVec_epr` costs nothing: the two parties' operators act identically on
the state. -/

@[simp] theorem wX_transpose (a : n → F) : (wX a)ᵀ = wX a := by
  ext j i
  rw [Matrix.transpose_apply, wX_apply, wX_apply]
  by_cases h : j = i + a
  · rw [if_pos h, if_pos (by rw [h, add_add_cancel_vec])]
  · rw [if_neg h, if_neg fun hh : i = j + a => h (by rw [hh, add_add_cancel_vec])]

@[simp] theorem wZ_transpose (b : n → F) : (wZ b)ᵀ = wZ b := by
  ext j i
  rw [Matrix.transpose_apply, wZ_apply, wZ_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, h]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- **The two parties' `X`-type operators act identically on the maximally entangled state.** -/
theorem stateVec_epr_wX (a : n → F) :
    stateVec (epr (F := F) (n := n)) (wX a) = stateVecB epr (wX a) := by
  rw [stateVec_epr, wX_transpose]

/-- **The two parties' `Z`-type operators act identically on the maximally entangled state.** -/
theorem stateVec_epr_wZ (b : n → F) :
    stateVec (epr (F := F) (n := n)) (wZ b) = stateVecB epr (wZ b) := by
  rw [stateVec_epr, wZ_transpose]

/-- The same for the spectral projectors of either family, which are built from the operators by
a real Fourier average and are therefore symmetric too. -/
theorem stateVec_epr_proj {w : (n → F) → Matrix (n → F) (n → F) ℂ}
    (hw : ∀ a, (w a)ᵀ = w a) (e : n → F) :
    stateVec (epr (F := F) (n := n)) (proj w e) = stateVecB epr (proj w e) := by
  rw [stateVec_epr]
  congr 1
  rw [proj_def, Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [Matrix.transpose_smul, hw a]

end MIPRE.Weyl

end
