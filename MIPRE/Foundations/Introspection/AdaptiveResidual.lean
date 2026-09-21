/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ReadChainMaps

/-! # The actual CL continuation on the unvisited registers

The residual presentation follows a claimed output, including an off-image
one. It acts only on the complement of the registers already visited.
The next local map and register are computed from the original presentation.
-/

noncomputable section

namespace MIPRE.Introspection.CLChecks

open Finset Classical
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- Recursively compute the remaining depth, retaining definitional equations. -/
def residualDepth : ℕ → ℕ → ℕ
  | 0, ℓ => ℓ
  | _ + 1, 0 => 0
  | k + 1, ℓ + 1 => residualDepth k ℓ
termination_by structural k _ => k

theorem residualDepth_eq_sub (ℓ k : ℕ) : residualDepth k ℓ = ℓ - k := by
  induction ℓ generalizing k with
  | zero => cases k <;> simp [residualDepth]
  | succ ℓ ih => cases k <;> simp [residualDepth, ih]

/-- Continue after `k` reported components; the remaining depth is `ℓ-k`. -/
def residual : {ℓ : ℕ} → CL.CLFun F ι ℓ → (k : ℕ) → (ι → F) →
    CL.CLFun F ι (residualDepth k ℓ)
  | _, P, 0, _ => P
  | _, .zero, _ + 1, _ => .zero
  | _, .cons S _ next, k + 1, y => residual (next (CL.proj S y)) k (CL.proj Sᶜ y)

@[simp] theorem residual_zero (P : CL.CLFun F ι ℓ) (y : ι → F) : residual P 0 y = P := by
  cases P <;> rfl

/-- Every continuation acts only on the coordinates that have not been read. -/
theorem residual_supported {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    (residual P k y).SupportedOn (T \ prefixRegister P k y) := by
  induction P generalizing T k y with
  | zero => cases k <;> trivial
  | cons S L next ih =>
    cases k with
    | zero => simpa only [residual, residualDepth, prefixRegister, sdiff_empty] using hP
    | succ k =>
      have h := ih (CL.proj S y) (hP.2 _) k (CL.proj Sᶜ y)
      simpa only [residual, residualDepth, prefixRegister, sdiff_sdiff, Finset.sup_eq_union] using h

/-- Exact partitioning also survives passing to a continuation. -/
theorem residual_exactlyOn {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.ExactlyOn T) (k : ℕ) (hk : k ≤ ℓ) (y : ι → F) :
    (residual P k y).ExactlyOn (T \ prefixRegister P k y) := by
  induction P generalizing T k y with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    simpa only [residual, residualDepth, prefixRegister, sdiff_empty] using hP
  | cons S L next ih =>
    cases k with
    | zero => simpa only [residual, residualDepth, prefixRegister, sdiff_empty] using hP
    | succ k =>
      have h := ih (CL.proj S y) (hP.2 _) k (by omega) (CL.proj Sᶜ y)
      simpa only [residual, residualDepth, prefixRegister, sdiff_sdiff, Finset.sup_eq_union] using h

/-- The first register of the continuation is the original next register. -/
theorem residual_firstFactor (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    (residual P k y).factorOfPrefix 0 0 = P.factorOfPrefix k y := by
  induction P generalizing k y with
  | zero => cases k <;> rfl
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih _ k _

/-- The local linear map at a claimed prefix, with its actual finite-set support. -/
def stageLinear : {ℓ : ℕ} → (P : CL.CLFun F ι ℓ) → (k : ℕ) →
    (y : ι → F) → CL.RegLinear F (P.factorOfPrefix k y)
  | _, .zero, _, _ => 0
  | _, .cons _ L _, 0, _ => L
  | _, .cons S _ next, k + 1, y => stageLinear (next (CL.proj S y)) k (CL.proj Sᶜ y)

theorem stageLinear_toLinearMap (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    (stageLinear P k y).toLinearMap = P.mapOfPrefix k y := by
  induction P generalizing k y with
  | zero => rfl
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih _ k _

theorem factorOfPrefix_subset_support {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) : P.factorOfPrefix k y ⊆ T := by
  induction P generalizing T k y with
  | zero => simp
  | cons S L next ih =>
    cases k with
    | zero => exact hP.1
    | succ k => exact (ih _ (hP.2 _) k _).trans sdiff_subset

/-- This is the minimal residual support required by the product induction. -/
theorem stageFactor_subset_residual {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    P.factorOfPrefix k y ⊆ T \ prefixRegister P k y := by
  have h := factorOfPrefix_subset_support (residual_supported hP k y) 0 0
  rwa [residual_firstFactor] at h

/-- Passing one stage adds exactly its selected register to the prefix. -/
theorem prefixRegister_step (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    prefixRegister P (k + 1) y = prefixRegister P k y ∪ P.factorOfPrefix k y := by
  induction P generalizing k y with
  | zero => cases k <;> simp [prefixRegister]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      simp only [prefixRegister, CL.CLFun.factorOfPrefix_cons_succ, ih]
      exact (union_assoc _ _ _).symm

/-- Mixing removes precisely the current factor, giving the next residual register. -/
theorem residualRegister_step (P : CL.CLFun F ι ℓ) (T : Finset ι)
    (k : ℕ) (y : ι → F) :
    (T \ prefixRegister P k y) \ P.factorOfPrefix k y = T \ prefixRegister P (k + 1) y := by
  rw [prefixRegister_step, sdiff_sdiff]
  rfl

/-- Every next factor is determined by the already reported prefix. -/
theorem stageFactor_congr {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) {y z : ι → F}
    (h : P.outputPrefix k y = P.outputPrefix k z) :
    P.factorOfPrefix k y = P.factorOfPrefix k z := by
  rw [← factorOfPrefix_outputPrefix hP k y, ← factorOfPrefix_outputPrefix hP k z, h]

/-- Adding the selected next linear answer advances the actual sampler prefix. -/
theorem truncate_eval_step {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (x : ι → F) :
    (P.truncate (k + 1)).eval x = (P.truncate k).eval x +
      (stageLinear P k ((P.truncate k).eval x)) x := by
  rw [hP.eval_truncate_eq_sum (k + 1), sum_range_succ,
    ← hP.eval_truncate_eq_sum k]
  congr 1
  rw [← CL.RegLinear.toLinearMap_apply, stageLinear_toLinearMap, hP.mapOfPrefix_eval]

theorem coordinateRestrict_proj {U V : Finset ι} (hUV : U ⊆ V) (x : ι → F) :
    coordinateRestrict U (CL.proj V x) = coordinateRestrict U x := by
  ext j
  exact if_pos (hUV ((Fintype.equivFin U).symm j).property)

set_option backward.isDefEq.respectTransparency false in
/-- The recursive dual answer is exactly the selected coordinate linear
readout, transported back into the original register. -/
theorem dualReadout_stageLinear {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    dualReadout P k y x = coordinateInsert (P.factorOfPrefix k y)
      (CL.lperp (coordinateLinear (stageLinear P k y))
        (coordinateRestrict (P.factorOfPrefix k y) x)) := by
  induction P generalizing T k y x with
  | zero =>
    ext i
    simp [dualReadout, coordinateInsert]
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih _ (hP.2 _) k _ x

end MIPRE.Introspection.CLChecks

end
