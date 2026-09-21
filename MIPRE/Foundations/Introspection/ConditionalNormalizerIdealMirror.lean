/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalNormalizerIdeal
import MIPRE.Foundations.Introspection.EPR

/-! # Exact EPR mirrors of the concrete honest hiding operators

Every local Weyl readout is symmetric in characteristic two. The adaptive
construction, its coordinate transports, and its coarse sums preserve that
property, even when later measurements depend on earlier outcomes.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

theorem synOf_transpose_of_symmetric
    (w : (ι → F) → Matrix (ι → F) (ι → F) ℂ) (hw : ∀ x, (w x)ᵀ = w x)
    {J : Type*} [DecidableEq J] (f : (ι → F) → J) (j : J) :
    (synOf w f j)ᵀ = synOf w f j := by
  rw [synOf, Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [proj_def, Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [Matrix.transpose_smul, hw]

theorem localRead_transpose {S : Finset ι} (L : CL.RegLinear F S)
    (a : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) :
    (localRead L a)ᵀ = localRead L a := by
  rw [localRead, Matrix.transpose_mul,
    synOf_transpose_of_symmetric _ wX_transpose, synOf_transpose_of_symmetric _ wZ_transpose]
  exact (linear_measurements_commute (coordinateLinear L) (CL.lperp (coordinateLinear L))
    (by simp only [CL.ker_lperp, CL.perp_perp]; exact le_rfl) a.1 a.2).eq.symm

theorem stopHide_transpose (P : CL.CLFun F ι ℓ) (V : Finset ι) (a : HideLabel F ι) :
    (stopHide P V a)ᵀ = stopHide P V a :=
  synOf_transpose_of_symmetric _ wX_transpose _ _

/-- Adaptive branches preserve symmetry outcome by outcome; no comparison
between operators in different branches is required. -/
theorem hideRegister_transpose (P : CL.CLFun F ι ℓ) (k : ℕ)
    (V : Finset ι) (h : P.SupportedOn V) (a : HideLabel F ι) :
    (hideRegister P k V h a)ᵀ = hideRegister P k V h a := by
  induction P generalizing V k a with
  | zero => cases k <;> exact stopHide_transpose _ _ _
  | cons S L next ih =>
    cases k with
    | zero => exact stopHide_transpose _ _ _
    | succ k =>
      simp only [hideRegister]
      change registerOp _ ((∑ q ∈ univ.filter (fun q => joinHide S q = a),
        adaptiveTensor (localRead L)
          (fun z => hideRegister (next (coordinateInsert S z.1)) k (V \ S) (h.2 _)) q)ᵀ) = _
      congr 1
      rw [Matrix.transpose_sum]
      apply Finset.sum_congr rfl
      intro q _
      change (localRead L q.1)ᵀ ⊗ₖ
        (hideRegister (next (coordinateInsert S q.1.1)) k (V \ S) (h.2 _) q.2)ᵀ = _
      rw [localRead_transpose, ih]
      rfl

theorem hideOp_transpose (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (a : HideLabel F ι) : (hideOp P k h a)ᵀ = hideOp P k h a := by
  change registerOp univRestriction (hideRegister P k univ h a)ᵀ = _
  rw [hideRegister_transpose]
  rfl

theorem hideCoarseOp_transpose (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (i : Option (HideLabel F ι)) :
    (hideCoarseOp P k h i)ᵀ = hideCoarseOp P k h i := by
  rw [hideCoarseOp, fibSum, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun a _ => hideOp_transpose P k h a

theorem hidingPrefixOp_transpose (P : CL.CLFun F ι ℓ) (k : ℕ) (y : Option (ι → F)) :
    (hidingPrefixOp P k y)ᵀ = hidingPrefixOp P k y := by
  exact Matrix.diagonal_transpose _

theorem hideCoarseOp_epr_mirror (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn univ) (i : Option (HideLabel F ι)) :
    aOp (hideCoarseOp P k h i) *ᵥ registerEPR (ι → F) =
      bOp (hideCoarseOp P k h i) *ᵥ registerEPR (ι → F) := by
  have he := stateVec_epr (hideCoarseOp P k h i)
  rw [hideCoarseOp_transpose, ← registerEPR_eq_weyl] at he
  exact congrArg WithLp.ofLp he

theorem hidingPrefixOp_epr_mirror (P : CL.CLFun F ι ℓ) (k : ℕ) (y : Option (ι → F)) :
    aOp (hidingPrefixOp P k y) *ᵥ registerEPR (ι → F) =
      bOp (hidingPrefixOp P k y) *ᵥ registerEPR (ι → F) := by
  have he := stateVec_epr (hidingPrefixOp P k y)
  rw [hidingPrefixOp_transpose, ← registerEPR_eq_weyl] at he
  exact congrArg WithLp.ofLp he

end MIPRE.Introspection.Honest
