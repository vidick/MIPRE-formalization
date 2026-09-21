/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveDualFactor
import MIPRE.Foundations.Introspection.AdaptivePrefixMixing

/-! # The honest dual marginal in the selected mixing coordinates -/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Weyl Classical Honest
open scoped Kronecker
set_option linter.unusedSectionVars false

theorem aOp_registerOp_kron {I J R H : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
    (e : I ≃ J × R) (P : Matrix J J ℂ) (N : Matrix R R ℂ) :
    (aOp (registerOp e (P ⊗ₖ N)) : Matrix (I × H) _ ℂ) =
      registerOp (registerParty e H) (P ⊗ₖ (aOp N : Matrix (R × H) _ ℂ)) := by
  ext ⟨i,h⟩ ⟨j,h'⟩
  simp only [aOp, registerOp_apply, Matrix.kroneckerMap_apply, registerParty,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodAssoc_apply]
  exact mul_assoc _ _ _

variable {ι F H : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] {ℓ : ℕ}

theorem synX_coordinateInsert {S : Finset ι}
    (L : (Fin (Fintype.card S) → F) →ₗ[F] (Fin (Fintype.card S) → F))
    (z : Fin (Fintype.card S) → F) :
    synOf wX (fun x => coordinateInsert S (L x)) (coordinateInsert S z) = synOf wX L z := by
  have he (x : Fin (Fintype.card S) → F) : coordinateInsert S (L x) = coordinateInsert S z ↔
      L x = z := by
    constructor
    · intro hx
      simpa only [coordinateRestrict_insert] using congrArg (coordinateRestrict S) hx
    · exact congrArg (coordinateInsert S)
  unfold synOf
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, he]

/-- The residual dual-X operator reads exactly the current stage's dual
linear map and acts as identity on the next continuation. -/
theorem residualDualOp_stage (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    residualDualOp P k y (coordinateInsert (P.factorOfPrefix k y) z) =
      registerOp (stageSplit P hP k y)
        (synOf wX (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) z ⊗ₖ
          (1 : Matrix (↥(stageRemaining P k y \ P.factorOfPrefix k y) → F) _ ℂ)) := by
  have hf (x : stageRemaining P k y → F) :
      CLChecks.dualReadout P k y (insertRegister (stageRemaining P k y) x) =
      coordinateInsert (P.factorOfPrefix k y)
        (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y)) (stageSplit P hP k y x).1) := by
    rw [CLChecks.dualReadout_stageLinear hP,
      restrict_insertRegister _ _ (stageFactor_subset_remaining P hP k y)]
    rfl
  unfold residualDualOp
  simp_rw [hf]
  rw [synX_split_first (stageSplit P hP k y)
    (pauliX_coordinateSplit (F := F) _ _ (stageFactor_subset_remaining P hP k y))
    (fun x => coordinateInsert (P.factorOfPrefix k y)
      (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y)) x))]
  rw [synX_coordinateInsert]

/-- The actual honest dual family, including any auxiliary factor, is exactly
the prefix-conditioned current X-dual readout consumed by adaptive mixing. -/
theorem readDualOp_stage_factor (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    (aOp (readDualOp P k hP (some (y, coordinateInsert (P.factorOfPrefix k y) z))) :
      Matrix ((ι → F) × H) _ ℂ) =
      prefixResidualOp P k y (registerReadout (stageSplit P hP k y)
        wX (CL.lperp (coordinateLinear (CLChecks.stageLinear P k y))) z) := by
  rw [readDualOp_prefix_factor P hP, aOp_registerOp_kron, residualDualOp_stage P hP]
  unfold prefixResidualOp registerReadout
  rw [← registerParty_kron_one]
  rfl

end MIPRE.Introspection
