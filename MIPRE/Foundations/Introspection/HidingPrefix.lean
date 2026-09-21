/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HidingRigidity

/-! # The information retained by a hiding prefix

These identities hold for arbitrary claimed outputs. They justify processing
the next hiding test from the preceding coarse outcome, without assuming that
an answer belongs to the image of the CL map.
-/

noncomputable section

namespace MIPRE.Introspection.CLChecks

open Finset Classical

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- Longer claimed prefixes retain all the registers of shorter prefixes. -/
theorem prefixRegister_mono (P : CL.CLFun F ι ℓ) (y : ι → F)
    {k m : ℕ} (hkm : k ≤ m) : prefixRegister P k y ⊆ prefixRegister P m y := by
  induction P generalizing k m y with
  | zero => cases k <;> cases m <;> simp [prefixRegister]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      cases m with
      | zero => omega
      | succ m =>
        exact union_subset_union (Subset.refl S) (ih _ _ (k := k) (m := m) (by omega))

/-- Taking a shorter prefix of a claimed prefix does not change it. -/
theorem outputPrefix_outputPrefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (y : ι → F) {k m : ℕ} (hkm : k ≤ m) :
    P.outputPrefix k (P.outputPrefix m y) = P.outputPrefix k y := by
  induction P generalizing T k m y with
  | zero => cases k <;> simp [CL.CLFun.outputPrefix]
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      cases m with
      | zero => omega
      | succ m =>
        obtain ⟨hfirst, hrest⟩ := proj_outputPrefix_cons hP m y
        rw [CL.CLFun.outputPrefix_cons, hfirst, hrest,
          ih _ (hP.2 _) _ (by omega), CL.CLFun.outputPrefix_cons]

/-- Equal preceding prefixes choose the same next register, including on
answers outside the image of the sampler. -/
theorem prefixRegister_congr {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) {y z : ι → F}
    (h : P.outputPrefix k y = P.outputPrefix k z) :
    prefixRegister P (k + 1) y = prefixRegister P (k + 1) z := by
  rw [← prefixRegister_outputPrefix_succ hP k y,
    ← prefixRegister_outputPrefix_succ hP k z, h]

/-- A dual readout only uses coordinates in the presentation's support. -/
theorem dualReadout_congr {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) {x t : ι → F}
    (h : ∀ i ∈ T, x i = t i) : dualReadout P k y x = dualReadout P k y t := by
  induction P generalizing T k y with
  | zero => rfl
  | cons S L next ih =>
    cases k with
    | zero =>
      simp only [dualReadout]
      congr 2
      funext i
      exact h _ (hP.1 ((Fintype.equivFin S).symm i).property)
    | succ k =>
      exact ih _ (hP.2 _) k _ (fun i hi => h i (mem_sdiff.mp hi).1)

/-- The next dual readout can be computed from the tail retained by the
previous hiding measurement. -/
theorem dualReadout_proj_compl_prefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    dualReadout P k y (CL.proj (prefixRegister P k y)ᶜ x) =
      dualReadout P k y x := by
  induction P generalizing T k y with
  | zero => rfl
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister, dualReadout]
    | succ k =>
      simp only [prefixRegister, dualReadout]
      calc
        _ = dualReadout (next (CL.proj S y)) k (CL.proj Sᶜ y)
            (CL.proj (prefixRegister (next (CL.proj S y)) k (CL.proj Sᶜ y))ᶜ x) := by
          apply dualReadout_congr (hP.2 _)
          intro i hi
          have hiS := (mem_sdiff.mp hi).2
          simp [CL.proj_apply, hiS]
        _ = _ := ih _ (hP.2 _) k _

/-- Removing an earlier prefix does not change any later tail. -/
theorem tail_proj_tail (P : CL.CLFun F ι ℓ) (y x : ι → F)
    {k m : ℕ} (hkm : k ≤ m) :
    CL.proj (prefixRegister P m y)ᶜ (CL.proj (prefixRegister P k y)ᶜ x) =
      CL.proj (prefixRegister P m y)ᶜ x := by
  apply CL.proj_proj_of_subset
  exact compl_subset_compl.mpr (prefixRegister_mono P y hkm)

end MIPRE.Introspection.CLChecks

end
