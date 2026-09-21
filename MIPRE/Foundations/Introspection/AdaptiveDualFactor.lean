/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveDualMarginal
import MIPRE.Foundations.Introspection.AdaptiveXSplit
import MIPRE.Foundations.Introspection.HonestPauliRegister

/-! # Exact prefix/dual factorization at every adaptive CL stage -/

noncomputable section
namespace MIPRE.Introspection.Honest
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

section Diagonal
variable {I J K Y Y₁ Y₂ : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype Y] [DecidableEq Y] [Fintype Y₁] [DecidableEq Y₁]
  [Fintype Y₂] [DecidableEq Y₂]

theorem readout_split (e : I ≃ J × K) (f : I → Y) (g : J → Y₁) (r : K → Y₂)
    (y : Y) (y₁ : Y₁) (y₂ : Y₂)
    (hf : ∀ x, f x = y ↔ g (e x).1 = y₁ ∧ r (e x).2 = y₂) :
    readout f y = registerOp e (readout g y₁ ⊗ₖ readout r y₂) := by
  ext x x'
  simp only [registerOp_apply, Matrix.kroneckerMap_apply, readout, Matrix.diagonal_apply]
  by_cases he : x = x'
  · subst x'
    simp only [if_true]
    by_cases hg : g (e x).1 = y₁ <;> by_cases hr : r (e x).2 = y₂ <;>
      simp [hf x, hg, hr]
  · have hs : ¬ ((e x).1 = (e x').1 ∧ (e x).2 = (e x').2) := by
      intro h
      exact he (e.injective (Prod.ext h.1 h.2))
    rcases not_and_or.mp hs with hs | hs <;> simp [he, hs]

theorem readout_constant (y₀ y : Y) :
    readout (fun _ : I => y₀) y = if y₀ = y then 1 else 0 := by
  ext x x'
  by_cases hy : y₀ = y <;> by_cases hx : x = x' <;> simp [readout, hy, hx, Matrix.one_apply]

end Diagonal

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

theorem prefixReadout_cons_succ {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (h : (CL.CLFun.cons S L next).SupportedOn V) (k : ℕ) (y : ι → F) :
    readout (fun x : V → F => ((CL.CLFun.cons S L next).truncate (k+1)).eval
      (insertRegister V x)) y = registerOp (coordinateSplit S V h.1)
        (synOf wZ (coordinateLinear L) (coordinateRestrict S y) ⊗ₖ
          readout (fun x : ↥(V \ S) → F => ((next (CL.proj S y)).truncate k).eval
            (insertRegister (V \ S) x)) (CL.proj Sᶜ y)) := by
  rw [← readout_eq_synOf]
  apply readout_split
  intro x
  have hp := h.proj_eval_truncate_succ k (insertRegister V x)
  constructor
  · intro hx
    have hL : L (insertRegister V x) = CL.proj S y := by rw [← hp.1, hx]
    have hl := congrArg (coordinateRestrict S) hL
    rw [linear_insertRegister h.1, coordinateRestrict_insert] at hl
    have hr := hp.2
    rw [hx, hL, tail_insertRegister S V h.1] at hr
    refine ⟨?_, hr.symm⟩
    simpa only [← coordinateInsert_restrict, coordinateRestrict_insert] using hl
  · rintro ⟨hl, hr⟩
    have hL : L (insertRegister V x) = CL.proj S y := by
      rw [linear_insertRegister h.1, hl, coordinateInsert_restrict]
    rw [CL.CLFun.truncate_succ_cons, CL.CLFun.eval_cons, hL,
      tail_insertRegister S V h.1, hr, CL.proj_add_proj_compl]

/-- The actual honest Hide marginal equals the preceding Z prefix multiplied
by the current X-dual spectral readout. Earlier dual answers have been summed
out in the proved adaptive recursion. -/
theorem dualRegister_factor (P : CL.CLFun F ι ℓ) (k : ℕ)
    (V : Finset ι) (h : P.SupportedOn V) (y yp : ι → F) :
    dualRegister P k V h (y,yp) =
      readout (fun x : V → F => (P.truncate k).eval (insertRegister V x)) y *
        synOf wX (fun x : V → F => CLChecks.dualReadout P k y (insertRegister V x)) yp := by
  induction P generalizing V k y yp with
  | zero =>
    have hd : dualRegister (CL.CLFun.zero : CL.CLFun F ι 0) k V h (y,yp) =
        dualRegister .zero 0 V h (y,yp) := by cases k <;> rfl
    rw [hd, dualRegister_zero]
    simp only [CL.CLFun.eval_truncate_zero, CLChecks.dualReadout, readout_constant]
    by_cases hy : y = 0
    · subst y; simp
    · simp [hy, Ne.symm hy]
  | cons S L next ih =>
    cases k with
    | zero =>
      rw [dualRegister_zero]
      simp only [CL.CLFun.truncate_zero, CL.CLFun.eval_zero, readout_constant]
      by_cases hy : y = 0
      · subst y; simp
      · simp [hy, Ne.symm hy]
    | succ k =>
      rw [dualRegister_cons_succ L next h k y yp, prefixReadout_cons_succ L next h k y,
        dualReadout_tail_split L next h k y yp,
        ← registerOp_mul, ← Matrix.mul_kronecker_mul, mul_one, ih _ k (V \ S) (h.2 _)]

theorem synX_univRestriction {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : (ι → F) → Y) (y : Y) :
    registerOp univRestriction (synOf wX (fun x => f (insertRegister univ x)) y) =
      synOf wX f y := by
  ext x x'
  simp only [registerOp_apply, synOf, Matrix.sum_apply, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (univRestriction (F := F) (ι := ι))
  intro z
  simp only [insertRegister_univ]
  by_cases hz : f z = y
  · simp only [hz, if_true]
    exact (congrArg (fun M => M x x') (pauliX_univRestriction z)).symm
  · simp [hz]

/-- The source prefix/dual product is the existing honest Read dual marginal,
not a separately stipulated family. -/
theorem readDualOp_factor (P : CL.CLFun F ι ℓ) (h : P.SupportedOn univ)
    (k : ℕ) (y yp : ι → F) :
    readDualOp P k h (some (y,yp)) = hidingPrefixOp P k (some y) *
      synOf wX (CLChecks.dualReadout P k y) yp := by
  rw [readDualOp_eq_registerDual, dualRegister_factor, registerOp_mul, synX_univRestriction,
    hidingPrefixOp_some]
  congr 1
  ext x x'
  simp [registerOp_apply, readout, Matrix.diagonal_apply,
    univRestriction.injective.eq_iff]

/-- The current dual-X readout on exactly the unvisited register. -/
def residualDualOp (P : CL.CLFun F ι ℓ) (k : ℕ) (y yp : ι → F) :
    Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) (↥((CLChecks.prefixRegister P k y)ᶜ) → F) ℂ :=
  synOf wX (fun x => CLChecks.dualReadout P k y
    (insertRegister (CLChecks.prefixRegister P k y)ᶜ x)) yp

/-- Full concrete tensor factorization under the prefix's own coordinate split,
valid uniformly at every CL stage and every claimed prefix/dual label. -/
theorem readDualOp_prefix_factor (P : CL.CLFun F ι ℓ) (h : P.SupportedOn univ)
    (k : ℕ) (y yp : ι → F) :
    readDualOp P k h (some (y,yp)) =
      registerOp (ambientSplit (CLChecks.prefixRegister P k y))
        (prefixProjector P k y ⊗ₖ residualDualOp P k y yp) := by
  rw [readDualOp_factor, hidingPrefixOp_factor P h, dualReadout_prefix_split P h,
    ← registerOp_mul, ← Matrix.mul_kronecker_mul, mul_one, one_mul]
  rfl

end MIPRE.Introspection.Honest
