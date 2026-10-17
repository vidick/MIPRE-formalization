/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/VerifierIndexTransport.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Theorems.Thm_MIPRE_SyncStrategy_isPCC_relabel
import Theorems.Thm_MIPRE_SyncStrategy_value_relabel
import Theorems.Thm_MIPRE_quantumValue_eq_of_equiv

/-! # Verifier transport at a single index

Wrappers may change a sampler at exceptional indices. Equality of its dimension
and CL presentations at the index in question suffices to preserve both quantum
value and perfect PCC strategies; the programs need not agree elsewhere.
-/

noncomputable section
namespace MIPRE.Verifier
open CL

/-- Numbered vectors transported along an equality of their dimensions. -/
def dimensionEquiv {s t : ℕ} (h : s = t) : (Fin s → 𝔽₂) ≃ (Fin t → 𝔽₂) :=
  h ▸ Equiv.refl _

variable {ℓ : ℕ} {V W : Verifier ℓ} {n T : ℕ}

/-- Only the sampler data used at this index are compared. -/
structure SamplerAgreement (V W : Verifier ℓ) (n : ℕ) : Prop where
  dimension : V.sampler.dim n = W.sampler.dim n
  presentation : ∀ w, HEq (V.sampler.cl n w) (W.sampler.cl n w)

end MIPRE.Verifier
