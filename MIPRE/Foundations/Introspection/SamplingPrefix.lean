/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.Basic

/-! # Reading prefixes from arbitrary claimed CL outputs

The sampling test coarse-grains the entire answer alphabet, not merely the
image of the CL map. The prefix map therefore follows the claimed output's
coordinate branches and does not apply the stage linear maps again.
-/

namespace MIPRE.CL.CLFun

open Finset

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- Extract the first `k` register components from any claimed output. -/
def outputPrefix : {ℓ : ℕ} → CLFun F ι ℓ → ℕ → (ι → F) → (ι → F)
  | _, _, 0, _ => 0
  | _, .zero, _ + 1, _ => 0
  | _, .cons S _ next, k + 1, y =>
    proj S y + (next (proj S y)).outputPrefix k (proj Sᶜ y)

@[simp] theorem outputPrefix_zero (P : CLFun F ι ℓ) (y : ι → F) :
    P.outputPrefix 0 y = 0 := by cases P <;> rfl

@[simp] theorem outputPrefix_cons (S : Finset ι) (L : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    (cons S L next).outputPrefix (k + 1) y =
      proj S y + (next (proj S y)).outputPrefix k (proj Sᶜ y) := rfl

/-- An honest output's first register and remainder recover the two construction branches. -/
theorem SupportedOn.proj_eval_cons {S T : Finset ι} {L : RegLinear F S}
    {next : (ι → F) → CLFun F ι ℓ} (hP : (cons S L next).SupportedOn T) (z : ι → F) :
    proj S ((cons S L next).eval z) = L z ∧
      proj Sᶜ ((cons S L next).eval z) = (next (L z)).eval (proj Sᶜ z) := by
  have h := hP.proj_eval_truncate_succ ℓ z
  simpa only [truncate_self] using h

/-- The sampling check can compute the honest marginal from the complete claimed output. -/
theorem SupportedOn.outputPrefix_eval {P : CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (z : ι → F) :
    P.outputPrefix k (P.eval z) = (P.truncate k).eval z := by
  induction P generalizing T k z with
  | zero => cases k <;> simp [outputPrefix]
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨hfirst, hrest⟩ := hP.proj_eval_cons z
      rw [outputPrefix_cons, hfirst, hrest, truncate_succ_cons, eval_cons,
        ih _ (hP.2 _) k (proj Sᶜ z)]

/-- No image-membership condition is used to compute prefixes of claimed answers. -/
theorem ExactlyOn.outputPrefix_self {P : CLFun F ι ℓ} {T : Finset ι}
    (hP : P.ExactlyOn T) (y : ι → F) : P.outputPrefix ℓ (proj T y) = proj T y := by
  induction P generalizing T y with
  | zero =>
    have hT : T = ∅ := hP
    simp [hT, outputPrefix]
  | cons S L next ih =>
    obtain ⟨hS, hnext⟩ := hP
    rw [outputPrefix_cons, proj_proj_of_subset hS]
    have hp : proj Sᶜ (proj T y) = proj (T \ S) y := by
      rw [proj_proj, inter_comm, ← sdiff_eq_inter_compl]
    rw [hp, ih _ (hnext _) y]
    have hp' : proj (T \ S) y = proj Sᶜ (proj T y) := hp.symm
    rw [hp', ← proj_proj_of_subset hS y, proj_add_proj_compl]

/-- For a full CL presentation, the full claimed prefix is every answer vector. -/
theorem ExactlyOn.outputPrefix_univ {P : CLFun F ι ℓ} (hP : P.ExactlyOn univ) (y : ι → F) :
    P.outputPrefix ℓ y = y := by
  simpa only [proj_univ] using hP.outputPrefix_self y

end MIPRE.CL.CLFun
