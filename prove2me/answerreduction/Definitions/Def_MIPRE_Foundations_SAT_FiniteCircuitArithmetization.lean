/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/FiniteCircuitArithmetization.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables

/-!
# Circuit arithmetization on exactly the input and gate variables

The first `C.inputs` coordinates are the inputs, followed by the `C.size` gate
variables. No new variables are needed for routing repeated input reads.
-/

noncomputable section

namespace MIPRE.SAT.Circuit

open MvPolynomial LowDegree

variable {F : Type*} [Field F]

/-- Embed the exact finite coordinate set into input and gate indices. -/
def wireEmbedding (C : Circuit) : Fin (C.inputs + C.size) → ℕ ⊕ ℕ :=
  Sum.map Fin.val Fin.val ∘ finSumFinEquiv.symm

theorem wireEmbedding_injective (C : Circuit) : Function.Injective C.wireEmbedding :=
  (Fin.val_injective.sumMap Fin.val_injective).comp finSumFinEquiv.symm.injective

@[simp] theorem wireEmbedding_input (C : Circuit) (i : Fin C.inputs) :
    C.wireEmbedding (Fin.castAdd C.size i) = .inl i.val := by simp [wireEmbedding]

@[simp] theorem wireEmbedding_gate (C : Circuit) (j : Fin C.size) :
    C.wireEmbedding (Fin.natAdd C.inputs j) = .inr j.val := by simp [wireEmbedding]

/-- The routed polynomial restricted to the exact finite coordinate set. -/
def finiteArith (C : Circuit) : MvPolynomial (Fin (C.inputs + C.size)) F :=
  killCompl C.wireEmbedding_injective C.routedArith

/-- Read the finite assignment's input part, with false outside the circuit. -/
def inputPart (C : Circuit) (z : Fin (C.inputs + C.size) → Bool) (i : ℕ) : Bool :=
  if h : i < C.inputs then z (Fin.castAdd C.size ⟨i, h⟩) else false

/-- Read the finite assignment's gate part, with false outside the circuit. -/
def gatePart (C : Circuit) (z : Fin (C.inputs + C.size) → Bool) (j : ℕ) : Bool :=
  if h : j < C.size then z (Fin.natAdd C.inputs ⟨j, h⟩) else false

variable [CharP F 2]

end MIPRE.SAT.Circuit

end
