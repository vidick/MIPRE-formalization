/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ConditionalNormalizerIdeal

/-! # Concrete tensor support of an adaptive CL prefix projector

A claimed prefix selects its used coordinates even outside the image of the
CL map. Membership in its fibre depends only on those coordinates. The ideal
prefix projector therefore acts as identity on their complement under the
explicit coordinate restriction equivalence.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

namespace CLChecks

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- Agreement on the registers selected by a claimed prefix preserves its
fibre, without assuming that the claimed prefix is attainable. -/
theorem truncate_fibre_of_agree {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x x' : ι → F)
    (hag : ∀ i ∈ prefixRegister P k y, x i = x' i)
    (hx : (P.truncate k).eval x = y) : (P.truncate k).eval x' = y := by
  induction P generalizing T k y x x' with
  | zero => simpa using hx
  | cons S L next ih =>
    cases k with
    | zero => simpa using hx
    | succ k =>
      have he : CL.proj S x' = CL.proj S x := by
        ext i
        by_cases hi : i ∈ S
        · simp only [CL.proj_apply, if_pos hi]
          exact (hag i (mem_union_left _ hi)).symm
        · simp [CL.proj_apply, hi]
      have hL : L x' = L x := by rw [← L.apply_proj x', he, L.apply_proj]
      have hp := hP.proj_eval_truncate_succ k x
      rw [hx] at hp
      have ht : ((next (CL.proj S y)).truncate k).eval (CL.proj Sᶜ x) = CL.proj Sᶜ y := by
        rw [hp.1]
        exact hp.2.symm
      have ht' := ih (CL.proj S y) (hP.2 _) k (CL.proj Sᶜ y)
        (CL.proj Sᶜ x) (CL.proj Sᶜ x') (by
          intro i hi
          by_cases hiS : i ∈ S
          · simp [CL.proj_apply, hiS]
          · simpa only [CL.proj_apply, mem_compl, hiS, not_false_eq_true, if_true] using
              hag i (mem_union_right S hi)) ht
      rw [CL.CLFun.truncate_succ_cons, CL.CLFun.eval_cons, hL, ← hp.1, ht']
      ext i
      by_cases hi : i ∈ S <;> simp [CL.proj_apply, hi]

theorem truncate_fibre_congr {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x x' : ι → F)
    (hag : ∀ i ∈ prefixRegister P k y, x i = x' i) :
    (P.truncate k).eval x = y ↔ (P.truncate k).eval x' = y :=
  ⟨truncate_fibre_of_agree hP k y x x' hag,
    truncate_fibre_of_agree hP k y x' x (fun i hi => (hag i hi).symm)⟩

theorem truncate_fibre_proj {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    (P.truncate k).eval x = y ↔
      (P.truncate k).eval (CL.proj (prefixRegister P k y) x) = y :=
  truncate_fibre_congr hP k y x _ (fun i hi => by simp [CL.proj_apply, hi])

end CLChecks

namespace Honest

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

theorem insertRegister_ambientSplit (V : Finset ι) (x : ι → F) :
    insertRegister V (ambientSplit V x).1 = CL.proj V x := by
  ext i
  simp [insertRegister, ambientSplit, CL.proj_apply]

/-- The actual prefix projector on exactly the already used coordinates. -/
def prefixProjector (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    Matrix (CLChecks.prefixRegister P k y → F) (CLChecks.prefixRegister P k y → F) ℂ :=
  readout (fun u => (P.truncate k).eval (insertRegister (CLChecks.prefixRegister P k y) u)) y

/-- A general diagonal readout factorization under a concrete register split. -/
theorem readout_ambientSplit {Y : Type*} [Fintype Y] [DecidableEq Y]
    (V : Finset ι) (f : (ι → F) → Y) (g : (V → F) → Y) (y : Y)
    (hf : ∀ x, f x = y ↔ g (ambientSplit V x).1 = y) :
    readout f y = registerOp (ambientSplit V)
      (readout g y ⊗ₖ (1 : Matrix (↥(Vᶜ) → F) (↥(Vᶜ) → F) ℂ)) := by
  ext x x'
  simp only [registerOp_apply, Matrix.kroneckerMap_apply, readout, Matrix.diagonal_apply,
    Matrix.one_apply]
  by_cases he : x = x'
  · subst x'
    simp only [if_true, mul_one]
    exact if_congr (hf x) rfl rfl
  · have hs : ¬ ((ambientSplit V x).1 = (ambientSplit V x').1 ∧
        (ambientSplit V x).2 = (ambientSplit V x').2) := by
      intro h
      exact he ((ambientSplit V).injective (Prod.ext h.1 h.2))
    rcases not_and_or.mp hs with hs | hs <;> simp [he, hs]

/-- The adaptive ideal prefix has no action on unused coordinates. This is
an exact matrix identity for every claimed prefix, including empty fibres. -/
theorem hidingPrefixOp_factor [Algebra (ZMod 2) F]
    (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ) (k : ℕ) (y : ι → F) :
    hidingPrefixOp P k (some y) = registerOp (ambientSplit (CLChecks.prefixRegister P k y))
      (prefixProjector P k y ⊗ₖ
        (1 : Matrix (↥((CLChecks.prefixRegister P k y)ᶜ) → F) _ ℂ)) := by
  rw [hidingPrefixOp_some]
  apply readout_ambientSplit
  intro x
  rw [insertRegister_ambientSplit]
  exact CLChecks.truncate_fibre_proj hP k y x

end Honest
end MIPRE.Introspection
