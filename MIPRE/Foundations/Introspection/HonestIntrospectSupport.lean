/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestCompleteAux

/-! # Attained outputs of honest Introspect measurements

The honest Introspect readout has zero effect on every claimed question outside
the source computation's image. This support statement needs no assumption on
the source strategy's value or commutation.
-/

noncomputable section
namespace MIPRE.Introspection.Honest

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι A PA : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype PA] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)

theorem coreOp_eq_zero_of_unattained (t : CoreType) (y : ι → F) (a : A)
    (hy : ¬ ∃ x, displayed L t x = y) : coreOp L D R t (y,a) = 0 := by
  have hz : readout (displayed L t) y = 0 := by
    ext x x'
    have hn : displayed L t x ≠ y := fun h => hy ⟨x,h⟩
    simp [readout, Matrix.diagonal_apply, hn]
  simp [coreOp, conditionalReadout, hz]

theorem coreOp_displayed_attained (t : CoreType) (y : ι → F) (a : A)
    (ha : coreOp L D R t (y,a) ≠ 0) : ∃ x, displayed L t x = y := by
  by_contra hn
  exact ha (coreOp_eq_zero_of_unattained L D R t y a hn)

/-- A nonzero honest Introspect answer reports an actual full source output. -/
theorem introspectOp_output_attained (w : Bool) (y : ι → F) (a : A)
    (ha : coreOp L D R (false,w) (y,a) ≠ 0) : ∃ x, (L w).eval x = y :=
  coreOp_displayed_attained L D R (false,w) y a ha

theorem parsedIntrospectOp_output_attained (w : Bool) (y : ι → F) (a : A)
    (ha : parsedCoreOp (PA := PA) L D R (false,w) (.pair y a) ≠ 0) :
    ∃ x, (L w).eval x = y := introspectOp_output_attained L D R w y a ha

theorem auxOp_introspect_output_attained (hL : ∀ w, (L w).SupportedOn univ)
    (w : Bool) (y : ι → F) (a : A)
    (ha : auxOp (PA := PA) L D R hL (.introspect,w) (.pair y a) ≠ 0) :
    ∃ x, (L w).eval x = y := parsedIntrospectOp_output_attained (PA := PA) L D R w y a ha

/-- The complete parsed alphabet has no additional nonzero Introspect labels. -/
theorem auxOp_introspect_nonzero (hL : ∀ w, (L w).SupportedOn univ)
    (w : Bool) (a : ParsedAnswer (ι → F) A PA)
    (ha : auxOp L D R hL (.introspect,w) a ≠ 0) :
    ∃ y b x, a = .pair y b ∧ (L w).eval x = y := by
  cases a <;> simp only [auxOp, parsedCoreOp, ne_eq, not_true_eq_false] at ha
  case pair y b =>
    obtain ⟨x,hx⟩ := introspectOp_output_attained L D R w y b ha
    exact ⟨y,b,x,rfl,hx⟩

end MIPRE.Introspection.Honest
