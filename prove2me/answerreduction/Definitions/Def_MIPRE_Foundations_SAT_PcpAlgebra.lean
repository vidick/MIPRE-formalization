/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/PcpAlgebra.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis

/-!
# The algebraic tests of the classical PCP

The formula test and Boolean-cube zero test from `thm:pcp-decider`. These lemmas
concern polynomials and their evaluations. Circuit padding, the embedding of the
five answer blocks, and the verifier's ambient program are separate obligations.
-/

noncomputable section

namespace MIPRE.SAT.PcpAlgebra

open Finset MvPolynomial LowDegree

variable {F : Type*} [Field F] {m : ℕ}

/-- The constraint polynomial: a clause is violated exactly when all five factors
are nonzero on the Boolean cube and its describing formula accepts. -/
def constraint (φ : MvPolynomial (Fin m) F) (g : Fin 5 → MvPolynomial (Fin m) F)
    (sign : Fin 5 → Fin m) : MvPolynomial (Fin m) F :=
  φ * ∏ i, (g i - X (sign i))

/-- The polynomial reconstructed from the claimed zero-basis certificates. -/
def zeroCombination (c : Fin m → MvPolynomial (Fin m) F) : MvPolynomial (Fin m) F :=
  ∑ i, c i * cubeZero i

@[simp] theorem eval_zeroCombination_cube (c : Fin m → MvPolynomial (Fin m) F)
    (y : Fin m → Bool) : eval (pt y) (zeroCombination c) = 0 := by
  simp [zeroCombination]

/-- The two equalities tested by the algebraic verifier at one point. -/
def Accepts (φ : MvPolynomial (Fin m) F) (g : Fin 5 → MvPolynomial (Fin m) F)
    (sign : Fin 5 → Fin m) (c₀ : MvPolynomial (Fin m) F)
    (c : Fin m → MvPolynomial (Fin m) F) (z : Fin m → F) : Prop :=
  eval z c₀ = eval z (constraint φ g sign) ∧ eval z c₀ = eval z (zeroCombination c)

end MIPRE.SAT.PcpAlgebra

end
