/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestHidingChecks.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity

/-! # Exact recursion of the honest hiding checks

Adding one common local Z/dual outcome to two supported continuation answers
preserves the actual parsed hiding predicate. These are identities for the
source checks, including the later-answer choice of adaptive registers.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

theorem supported_zero {V : Finset ι} {y : ι → F}
    (hy : CL.proj V y = y) {i : ι} (hi : i ∉ V) : y i = 0 := by
  have hh := congrFun hy i
  simpa only [CL.proj_apply, if_neg hi] using hh.symm

/-- The common local component and the supported tail are recovered by projection. -/
theorem proj_local_add {S V : Finset ι} (z : Fin (Fintype.card S) → F)
    (y : ι → F) (hy : CL.proj (V \ S) y = y) :
    CL.proj S (coordinateInsert S z + y) = coordinateInsert S z ∧
    CL.proj Sᶜ (coordinateInsert S z + y) = y := by
  constructor <;> funext i
  · by_cases hi : i ∈ S
    · have hz := supported_zero hy (show i ∉ V \ S by simp [hi])
      simp [CL.proj_apply, coordinateInsert, hi, hz]
    · simp [CL.proj_apply, coordinateInsert, hi]
  · by_cases hi : i ∈ S
    · have hz := supported_zero hy (show i ∉ V \ S by simp [hi])
      simp [CL.proj_apply, coordinateInsert, hi, hz]
    · simp [CL.proj_apply, coordinateInsert, hi]

theorem proj_tail_local_add {S V T : Finset ι} (hT : T ⊆ V \ S)
    (z : Fin (Fintype.card S) → F) (y : ι → F) :
    CL.proj T (coordinateInsert S z + y) = CL.proj T y := by
  funext i
  by_cases hi : i ∈ T
  · have hn := (mem_sdiff.mp (hT hi)).2
    simp [CL.proj_apply, coordinateInsert, hi, hn]
  · simp [CL.proj_apply, hi]

theorem proj_union_local_add {S V T : Finset ι} (hT : T ⊆ V \ S)
    (z : Fin (Fintype.card S) → F) (y : ι → F) (hy : CL.proj (V \ S) y = y) :
    CL.proj (S ∪ T) (coordinateInsert S z + y) = coordinateInsert S z + CL.proj T y := by
  funext i
  by_cases hi : i ∈ S
  · have hn : i ∉ T := fun hh => (mem_sdiff.mp (hT hh)).2 hi
    have hz := supported_zero hy (show i ∉ V \ S by simp [hi])
    simp [CL.proj_apply, coordinateInsert, hi, hn, hz]
  · by_cases ht : i ∈ T <;> simp [CL.proj_apply, coordinateInsert, hi, ht]

theorem proj_union_compl_tail {S V T : Finset ι}
    (y : ι → F) (hy : CL.proj (V \ S) y = y) :
    CL.proj (S ∪ T)ᶜ y = CL.proj Tᶜ y := by
  funext i
  by_cases hi : i ∈ S
  · have hz := supported_zero hy (show i ∉ V \ S by simp [hi])
    simp [CL.proj_apply, hi, hz]
  · simp [CL.proj_apply, hi]

theorem factorOfPrefix_subset {P : CL.CLFun F ι ℓ} {V : Finset ι}
    (h : P.SupportedOn V) (k : ℕ) (y : ι → F) : P.factorOfPrefix k y ⊆ V := by
  induction P generalizing V k y with
  | zero => simp
  | cons S L next ih =>
      cases k with
      | zero => exact h.1
      | succ k => exact (ih _ (h.2 _) k _).trans sdiff_subset

theorem prefixRegister_local_add {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ) (k : ℕ)
    (z : Fin (Fintype.card S) → F) (y : ι → F) (hy : CL.proj (V \ S) y = y) :
    CLChecks.prefixRegister (.cons S L next) (k + 1) (coordinateInsert S z + y) =
      S ∪ CLChecks.prefixRegister (next (coordinateInsert S z)) k y := by
  simp only [CLChecks.prefixRegister, (proj_local_add z y hy).1, (proj_local_add z y hy).2]

end MIPRE.Introspection.Honest
