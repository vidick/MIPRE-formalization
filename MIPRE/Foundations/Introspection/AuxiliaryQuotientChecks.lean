/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryDualDecode

/-! # Hiding tests using coordinate-independent quotient comparisons

The old exact dual comparison implies the quotient comparison, preserving
honest completeness. Conversely, quotient acceptance gives the old hiding
predicate after deterministic answer decoding. Raw prefixes and tails retain
the original checks. Neither direction assumes that a claimed prefix is
attainable; obtaining legal source queries is a separate executable obligation.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryQuotient

open Finset CLChecks AuxiliaryDual
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

abbrev RegisterHideAnswer (F ι : Type*) := (ι → F) × (ι → F) × (ι → F)

abbrev HideAnswer (F : Type*) (n : ℕ) := RegisterHideAnswer F (Fin n)

def decodeHide (P : CL.CLFun F (ι) ℓ) (a : RegisterHideAnswer F ι) : RegisterHideAnswer F ι :=
  (a.1, decodeDual P a.1 a.2.1, a.2.2)

def decodeRead {A : Type*} (P : CL.CLFun F (ι) ℓ)
    (a : (ι → F) × (ι → F) × A) : (ι → F) × (ι → F) × A :=
  (a.1, decodeDual P a.1 a.2.1, a.2.2)

/-- Replace only the new dual block's representative by its quotient class. -/
def hidingNext (P : CL.CLFun F (ι) ℓ) (k : ℕ) (u v : RegisterHideAnswer F ι) : Prop :=
  P.outputPrefix k u.1 = P.outputPrefix k v.1 ∧
  CL.proj (prefixRegister P (k + 1) v.1) u.2.1 =
    CL.proj (prefixRegister P (k + 1) v.1) v.2.1 ∧
  CL.proj (prefixRegister P (k + 2) v.1)ᶜ u.2.2 =
    CL.proj (prefixRegister P (k + 2) v.1)ᶜ v.2.2 ∧
  stageDual P (k + 1) v.1 v.2.1 = stageDual P (k + 1) v.1 u.2.2

theorem hidingNext_of_legacy {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (k : ℕ) (u v : RegisterHideAnswer F ι)
    (h : CLChecks.hidingNext P k u v) : hidingNext P k u v := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  have hs : CL.proj (P.factorOfPrefix (k + 1) v.1) v.2.1 =
      stageDual P (k + 1) v.1 u.2.2 := by
    rw [stageDual_apply hP]
    simpa only [factorOfPrefix_outputPrefix hP] using h.2.2.2
  have hd := congrArg (stageDual P (k + 1) v.1) hs
  change registerDual (stageLinear P (k + 1) v.1)
    (CL.proj (P.factorOfPrefix (k + 1) v.1) v.2.1) =
    registerDual (stageLinear P (k + 1) v.1)
      (registerDual (stageLinear P (k + 1) v.1) u.2.2) at hd
  rw [registerDual_proj_input _ (Subset.refl _), registerDual_idempotent] at hd
  exact hd

theorem hidingNext_sound {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) {k : ℕ} (hk : k + 1 < ℓ) (u v : RegisterHideAnswer F ι)
    (h : hidingNext P k u v) :
    CLChecks.hidingNext P k (decodeHide P u) (decodeHide P v) := by
  refine ⟨h.1, ?_, h.2.2.1, ?_⟩
  · exact proj_prefix_decodeDual_congr hP (by omega) h.1 h.2.1
  · change CL.proj (P.factorOfPrefix (k + 1) (P.outputPrefix (k + 1) v.1))
      (decodeDual P v.1 v.2.1) = dualReadout P (k + 1) v.1 u.2.2
    rw [factorOfPrefix_outputPrefix hP, proj_decodeDual hP _ _ hk,
      h.2.2.2, stageDual_apply hP]

/-- The first hiding edge uses the same quotient relaxation. -/
def hidingPauli (P : CL.CLFun F (ι) ℓ) (x : ι → F) (v : RegisterHideAnswer F ι) : Prop :=
  stageDual P 0 0 v.2.1 = stageDual P 0 0 x ∧
  CL.proj (P.factorOfPrefix 0 0)ᶜ x = CL.proj (P.factorOfPrefix 0 0)ᶜ v.2.2

theorem hidingPauli_of_legacy {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (x : ι → F) (v : RegisterHideAnswer F ι)
    (h : CLChecks.hidingPauli P x v) : hidingPauli P x v := by
  refine ⟨?_, h.2⟩
  have hs : CL.proj (P.factorOfPrefix 0 0) v.2.1 = stageDual P 0 0 x := by
    simpa only [stageDual_apply hP] using h.1
  have hd := congrArg (stageDual P 0 0) hs
  change registerDual (stageLinear P 0 0) (CL.proj (P.factorOfPrefix 0 0) v.2.1) =
    registerDual (stageLinear P 0 0) (registerDual (stageLinear P 0 0) x) at hd
  rw [registerDual_proj_input _ (Subset.refl _), registerDual_idempotent] at hd
  exact hd

theorem hidingPauli_sound {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (hℓ : 0 < ℓ) (x : ι → F) (v : RegisterHideAnswer F ι)
    (h : hidingPauli P x v) : CLChecks.hidingPauli P x (decodeHide P v) := by
  refine ⟨?_, h.2⟩
  have hp : P.outputPrefix 0 v.1 = P.outputPrefix 0 0 := by simp
  have hf := stageFactor_congr hP 0 hp
  have hd := stageDual_prefix_congr hP 0 hp
  change CL.proj (P.factorOfPrefix 0 0) (decodeDual P v.1 v.2.1) = dualReadout P 0 0 x
  rw [← hf, proj_decodeDual hP _ _ hℓ, hd, h.1, stageDual_apply hP]

/-- The final hiding/Read comparison survives the same decoding on both answers. -/
theorem hidingRead_sound {A : Type*} {P : CL.CLFun F (ι) ℓ} {T : Finset (ι)}
    (hP : P.SupportedOn T) (u : RegisterHideAnswer F ι) (v : (ι → F) × (ι → F) × A)
    (h : CLChecks.hidingRead P u v) :
    CLChecks.hidingRead P (decodeHide P u) (decodeRead P v) := by
  refine ⟨h.1, ?_⟩
  change decodeDual P u.1 u.2.1 = decodeDual P v.1 v.2.1
  rw [decodeDual_prefix_congr hP h.1, h.2]

end MIPRE.Introspection.AuxiliaryQuotient
end
