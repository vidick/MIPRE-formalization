/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestRead

/-! # The full honest Read measurement and the reading edge

The auxiliary answer is measured using the original strategy at the question
reported by the adaptive register measurement. Its marginal is exactly the
honest Introspect measurement, on the full answer alphabet.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)

/-- The complete honest Read operator: adaptive register data and the original answer. -/
def fullReadOp (w : Bool) (h : (L w).SupportedOn Finset.univ) (a : ReadLabel F ι × A) :
    Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ :=
  readOp (L w) h a.1 ⊗ₖ R.P.M (w, a.1.1) a.2

theorem fullReadOp_isPVM (w : Bool) (h : (L w).SupportedOn Finset.univ) :
    IsPVM (fullReadOp L D R w h) :=
  adaptiveTensor_isPVM _ _ (readOp_isPVM _ h) (fun a => source_isPVM L D R w a.1)

/-- Forgetting only the dual output gives the original honest Introspect operator exactly. -/
theorem fullReadOp_marginal (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (y : ι → F) (a : A) :
    (∑ yp, fullReadOp L D R w h ((y, yp), a)) = coreOp L D R (false, w) (y, a) := by
  simp only [fullReadOp, ← sum_kronecker_left, readOp_marginal]
  rfl

/-- The Introspect/Read product selects exactly equal questions and original answers. -/
theorem introspect_read_mul (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (ya : (ι → F) × A) (v : ReadLabel F ι × A) :
    coreOp L D R (false, w) ya * fullReadOp L D R w h v =
      if ya = (v.1.1, v.2) then fullReadOp L D R w h v else 0 := by
  change (readout (L w).eval ya.1 ⊗ₖ R.P.M (w, ya.1) ya.2) *
    (readOp (L w) h v.1 ⊗ₖ R.P.M (w, v.1.1) v.2) = _
  rw [← Matrix.mul_kronecker_mul, readout_mul_readOp]
  by_cases hy : ya.1 = v.1.1
  · rw [if_pos hy, hy, (source_isPVM L D R w _).mul_eq_ite]
    by_cases ha : ya.2 = v.2
    · have he : ya = (v.1.1, v.2) := Prod.ext hy ha
      simp [he, fullReadOp]
    · have hn : ya ≠ (v.1.1, v.2) := fun he => ha (congrArg Prod.snd he)
      simp [ha, hn]
  · have hn : ya ≠ (v.1.1, v.2) := fun he => hy (congrArg Prod.fst he)
    simp [hy, hn]

theorem read_introspect_mul (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (ya : (ι → F) × A) (v : ReadLabel F ι × A) :
    fullReadOp L D R w h v * coreOp L D R (false, w) ya =
      if ya = (v.1.1, v.2) then fullReadOp L D R w h v else 0 := by
  have he := congrArg Matrix.conjTranspose (introspect_read_mul L D R w h ya v)
  rw [Matrix.conjTranspose_mul, (coreOp_isPVM L D R (false, w)).isSelfAdjoint,
    (fullReadOp_isPVM L D R w h).isSelfAdjoint] at he
  by_cases hy : ya = (v.1.1, v.2) <;>
    simpa [hy, (fullReadOp_isPVM L D R w h).isSelfAdjoint] using he

/-- Honest Introspect and Read commute for every label, without needing source PCC. -/
theorem introspect_read_commute (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (ya : (ι → F) × A) (v : ReadLabel F ι × A) :
    Commute (coreOp L D R (false, w) ya) (fullReadOp L D R w h v) := by
  show _ * _ = _ * _
  rw [introspect_read_mul, read_introspect_mul]

theorem read_typed_check {P PA : Type*} (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (w : Bool)
    (ya : (ι → F) × A) (v : ReadLabel F ι × A) :
    TypedPredicate.check L X Z projectPauli D DP (.inr (.introspect, w)) (.inr (.read, w))
      (.pair ya.1 ya.2) (.read v.1.1 v.1.2 v.2) = decide (ya = (v.1.1, v.2)) := by
  by_cases hy : ya.1 = v.1.1 <;> by_cases ha : ya.2 = v.2 <;>
    simp [TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed,
      CLChecks.reading, Prod.ext_iff, hy, ha]

/-- Rejection on the actual parsed Introspect/Read edge has zero honest operator product. -/
theorem read_typed_reject_zero {P PA : Type*} (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (ya : (ι → F) × A) (v : ReadLabel F ι × A)
    (hr : TypedPredicate.check L X Z projectPauli D DP
      (.inr (.introspect, w)) (.inr (.read, w))
      (.pair ya.1 ya.2) (.read v.1.1 v.1.2 v.2) = false) :
    coreOp L D R (false, w) ya * fullReadOp L D R w h v = 0 := by
  rw [read_typed_check L D X Z projectPauli DP w ya v] at hr
  rw [introspect_read_mul, if_neg (of_decide_eq_false hr)]

end MIPRE.Introspection.Honest
