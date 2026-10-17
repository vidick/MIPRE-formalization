/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/WeylEPR.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl

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

/-- **The maximally entangled state is symmetric under exchanging the two halves.** -/
@[simp] theorem swapVec_epr : swapVec (epr (F := F) (n := n)) = epr := by
  funext p
  obtain ⟨a, b⟩ := p
  show epr (F := F) (n := n) (b, a) = epr (a, b)
  by_cases h : a = b
  · rw [h]
  · rw [epr_ne (Ne.symm h), epr_ne h]

/-! ## Transport to the other factor -/

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

/-! ## The syndrome projectors

`syn w v a` collects the spectral projectors along a level set of the pairing. Two facts the
expansion stage needs: it is a projective measurement, and it transports across the maximally
entangled state like each projector does. -/

variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}

end MIPRE.Weyl

end
