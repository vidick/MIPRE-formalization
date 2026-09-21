/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveAnswerRefinement

/-! # Updating the full answer after an adaptive stage

The decoder overwrites precisely the visited coordinates and retains the
unvisited tail. Valid answers therefore report the new prefix even after
mixing and dilation change their old coordinate label. The malformed
outcome remains `none`; no assertion that its mass vanishes is used.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Classical
set_option linter.unusedSectionVars false

variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}

/-- Overwrite the determined prefix while retaining the unvisited answer tail. -/
def stageAnswerDecode (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    Option ((ι → F) × A) → Option ((ι → F) × A)
  | none => none
  | some a => some (advancePrefix P k y z + CL.proj (stageRemaining P (k + 1) y) a.1, a.2)

theorem stageAnswerDecode_none (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    stageAnswerDecode (A := A) P k y z none = none := rfl

theorem stageAnswerDecode_eq_none (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (a : Option ((ι → F) × A)) :
    stageAnswerDecode P k y z a = none ↔ a = none := by cases a <;> simp [stageAnswerDecode]

/-- Every fixed old prefix remains fixed after inserting arbitrary current
coordinates; no membership in the linear map's image is required. -/
theorem advancePrefix_outputPrefix_fixed {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) (hy : P.outputPrefix k y = y)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    P.outputPrefix (k + 1) (advancePrefix P k y z) = advancePrefix P k y z := by
  rw [← CLChecks.proj_prefixRegister hP, advancePrefix_register hP]
  apply CL.proj_eq_self_iff.mpr
  intro i hi
  have hiy : i ∉ CLChecks.prefixRegister P k y := by
    intro hh
    exact hi (CLChecks.prefixRegister_mono P y (Nat.le_succ k) hh)
  have hiz : i ∉ P.factorOfPrefix k y := by
    intro hh
    exact hi (by rw [CLChecks.prefixRegister_step]; exact mem_union_right _ hh)
  have hyp := congrFun ((CLChecks.proj_prefixRegister hP k y).trans hy) i
  have hy0 : y i = 0 := by simpa [CL.proj_apply, hiy] using hyp.symm
  simp [advancePrefix, coordinateInsert, hy0, hiz]

/-- A decoded valid answer reports the actual advanced prefix automatically. -/
theorem stageAnswerDecode_prefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) (hy : P.outputPrefix k y = y)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (x : ι → F) :
    P.outputPrefix (k + 1)
      (advancePrefix P k y z + CL.proj (stageRemaining P (k + 1) y) x) =
      advancePrefix P k y z := by
  calc
    _ = P.outputPrefix (k + 1) (advancePrefix P k y z) := by
      apply CLChecks.outputPrefix_eq_of_agree
      intro i hi
      rw [advancePrefix_register hP] at hi
      simp [stageRemaining, CL.proj_apply, hi]
    _ = _ := advancePrefix_outputPrefix_fixed hP k y hy z

/-- On the old deterministic graph, decoding recovers the entire answer
whenever its old prefix agrees with the branch. -/
theorem stageAnswerDecode_recover_some {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) (a : A)
    (hy : P.outputPrefix k x = y) :
    stageAnswerDecode P k y (stageAnswerCoordinate P k y (some (x, a))) (some (x, a)) =
      some (x, a) := by
  have he : P.outputPrefix k y = P.outputPrefix k x := by
    rw [← hy, CLChecks.outputPrefix_outputPrefix hP x (le_refl k)]
  have hr := CLChecks.prefixRegister_congr hP k he
  have hf := CLChecks.stageFactor_congr hP k he
  have hd : Disjoint (CLChecks.prefixRegister P k x) (P.factorOfPrefix k x) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (mem_sdiff.mp (CLChecks.stageFactor_subset_residual hP k x hj)).2 hi
  simp only [stageAnswerDecode, stageAnswerCoordinate, advancePrefix,
    coordinateInsert_restrict, stageRemaining, hr, hf]
  congr 2
  rw [← hy, ← CLChecks.proj_prefixRegister hP k x,
    ← CL.proj_union_of_disjoint hd, ← CLChecks.prefixRegister_step,
    CL.proj_add_proj_compl]

/-- Recovery includes the malformed outcome, with no hypothesis on its mass. -/
theorem stageAnswerDecode_recover {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) (a : Option ((ι → F) × A))
    (ha : ∀ x b, a = some (x, b) → P.outputPrefix k x = y) :
    stageAnswerDecode P k y (stageAnswerCoordinate P k y a) a = a := by
  cases a with
  | none => rfl
  | some a => exact stageAnswerDecode_recover_some hP k y a.1 a.2 (ha _ _ rfl)

/-- For a full answer with the correct old prefix, advancing by its actual
selected coordinates gives precisely its reported next prefix. -/
theorem advancePrefix_coordinate_of_outputPrefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F)
    (hy : P.outputPrefix k x = y) :
    advancePrefix P k y (coordinateRestrict (P.factorOfPrefix k y) x) =
      P.outputPrefix (k + 1) x := by
  have hyfix : P.outputPrefix k y = y := by
    rw [← hy, CLChecks.outputPrefix_outputPrefix hP x (le_refl k)]
  have hr := stageAnswerDecode_recover_some (A := Unit) hP k y x () hy
  have he : advancePrefix P k y (coordinateRestrict (P.factorOfPrefix k y) x) +
      CL.proj (stageRemaining P (k + 1) y) x = x := by
    exact congrArg Prod.fst (Option.some.inj hr)
  have hp := stageAnswerDecode_prefix hP k y hyfix
    (coordinateRestrict (P.factorOfPrefix k y) x) x
  rw [he] at hp
  exact hp.symm

/-- Once the next prefix is named, the update depends only on that prefix
and its remaining answer tail. -/
theorem stageAnswerDecode_next {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) (a : Option ((ι → F) × A)) :
    stageAnswerDecode P k y z a = a.map (fun p =>
      (advancePrefix P k y z +
        CL.proj (stageRemaining P (k + 1) (advancePrefix P k y z)) p.1, p.2)) := by
  cases a <;> simp [stageAnswerDecode, advancePrefix_remaining hP]

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The actual stage refinement followed by the updating decoder recovers
the old residual measurement under its exact old-prefix support invariant.
There is deliberately no vanishing hypothesis for the malformed effect. -/
theorem stageAnswerRefinementPOVM_decode_recover {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F)
    (M : POVM (Option ((ι → F) × A)) ((stageRemaining P k y → F) × H))
    (hsupport : ∀ x a, P.outputPrefix k x ≠ y → (M.mats (some (x, a))).val = 0) :
    (stageAnswerRefinementPOVM P k y M).map
      (fun p => stageAnswerDecode P k y p.1 p.2) = M := by
  apply graphRefinementPOVM_decode
  intro a ha
  apply stageAnswerDecode_recover hP
  intro x b hab
  subst a
  by_contra h
  exact ha (hsupport x b h)

end MIPRE.Introspection
end
