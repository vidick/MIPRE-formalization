/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestHidingProducts
import MIPRE.Foundations.Introspection.HonestHidingChecks

/-! # Perfect acceptance along the honest adaptive hiding chain

A nonzero product of two neighboring honest measurements satisfies the actual
CL hiding check. The proof follows the same adaptive branches as the concrete
operators, using zero products to exclude incompatible earlier outcomes.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

private theorem exists_entry_ne_zero {I : Type*} (M : Matrix I I ℂ) (h : M ≠ 0) :
    ∃ i j, M i j ≠ 0 := by
  by_contra hn
  push Not at hn
  exact h (by ext i j; exact hn i j)

theorem hideRegister_supported (P : CL.CLFun F ι ℓ) (k : ℕ) (V : Finset ι)
    (h : P.SupportedOn V) (a : HideLabel F ι) (ha : hideRegister P k V h a ≠ 0) :
    CL.proj V a.1 = a.1 ∧ CL.proj V a.2.1 = a.2.1 ∧ CL.proj V a.2.2 = a.2.2 := by
  obtain ⟨x, x', hh⟩ := exists_entry_ne_zero _ ha
  exact hideRegister_entry_supported P k V h a x x' hh

theorem readRegister_supported (P : CL.CLFun F ι ℓ) (V : Finset ι)
    (h : P.SupportedOn V) (a : ReadLabel F ι) (ha : readRegister P V h a ≠ 0) :
    CL.proj V a.1 = a.1 ∧ CL.proj V a.2 = a.2 := by
  obtain ⟨x, x', hh⟩ := exists_entry_ne_zero _ ha
  exact readRegister_entry_supported P V h a x x' hh

set_option backward.isDefEq.respectTransparency false in
/-- Nonzero neighboring Hide products satisfy all four actual hiding comparisons. -/
theorem hideRegister_accepts_next (P : CL.CLFun F ι ℓ) (k : ℕ) (hk : k + 1 < ℓ)
    (V : Finset ι) (h : P.SupportedOn V) (a b : HideLabel F ι)
    (hab : hideRegister P k V h a * hideRegister P (k + 1) V h b ≠ 0) :
    CLChecks.hidingNext P k a b := by
  induction P generalizing V k a b with
  | zero => omega
  | cons S L next ih =>
      cases k with
      | zero =>
          simp only [hideRegister, hideRegister_zero_fun] at hab
          rw [stopHide_split S V h.1 L next, ← registerOp_mul] at hab
          have hm := (registerOp_ne_zero (coordinateSplit S V h.1) _).mp hab
          obtain ⟨bt, zc, ha, hb, hprod⟩ :=
            coarseOp_product_ne_zero (stopLabel S V) (joinHide S) _ _ a b hm
          change (synOf wX (CL.lperp (coordinateLinear L)) bt.1 ⊗ₖ proj wX bt.2) *
            (localRead L zc.1 ⊗ₖ stopHide (next (coordinateInsert S zc.1.1)) (V \ S) zc.2) ≠ 0 at hprod
          rw [stop_local_product] at hprod
          have hlabels : bt.1 = zc.1.2 ∧
              stopHideAnswer (next (coordinateInsert S zc.1.1)) (V \ S) bt.2 = zc.2 := by
            by_contra hn
            exact hprod (by simp [hn])
          rw [← ha, ← hb]
          change CLChecks.hidingNext _ 0 (stopLabel S V (bt.1, bt.2))
            (joinHide S (zc.1, zc.2))
          rw [← hlabels.2, hlabels.1]
          exact hidingNext_stop_join L next h zc.1 bt.2
      | succ k =>
          simp only [hideRegister] at hab
          rw [← registerOp_mul] at hab
          have hm := (registerOp_ne_zero (coordinateSplit S V h.1) _).mp hab
          obtain ⟨zu, zv, ha, hb, hprod⟩ :=
            coarseOp_product_ne_zero (joinHide S) (joinHide S) _ _ a b hm
          rcases zu with ⟨z, u⟩
          rcases zv with ⟨z', v⟩
          obtain ⟨hz, ht⟩ := adaptiveTensor_product_ne_zero
            (localRead L) (localRead_isPVM L) _ _ (z, u) (z', v) hprod
          dsimp only at hz
          subst z'
          have hu := hideRegister_supported (next (coordinateInsert S z.1)) k (V \ S) (h.2 _) u
            (by intro he; exact ht (by rw [he, zero_mul]))
          have hv := hideRegister_supported (next (coordinateInsert S z.1)) (k + 1) (V \ S) (h.2 _) v
            (by intro he; exact ht (by rw [he, mul_zero]))
          rw [← ha, ← hb]
          exact hidingNext_join L next h k z u v hu hv
            (ih (coordinateInsert S z.1) k (by omega) (V \ S) (h.2 _) u v ht)

theorem readRegister_zero_eq (P : CL.CLFun F ι 0) (V : Finset ι)
    (h : P.SupportedOn V) (a : ReadLabel F ι) :
    readRegister P V h a = if a = (0, 0) then 1 else 0 := by
  cases P
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The terminal Hide/Read product satisfies the actual common-prefix/full-dual check. -/
theorem hideRegister_accepts_read {A : Type*} (P : CL.CLFun F ι ℓ)
    (k : ℕ) (hk : k + 1 = ℓ) (V : Finset ι) (h : P.SupportedOn V)
    (a : HideLabel F ι) (b : ReadLabel F ι) (c : A)
    (hab : hideRegister P k V h a * readRegister P V h b ≠ 0) :
    CLChecks.hidingRead P a (b.1, b.2, c) := by
  induction P generalizing V k a b with
  | zero => omega
  | @cons n S L next ih =>
      cases k with
      | zero =>
          have hn : n = 0 := by omega
          subst n
          simp only [hideRegister, readRegister] at hab
          rw [stopHide_split S V h.1 L next, ← registerOp_mul] at hab
          have hm := (registerOp_ne_zero (coordinateSplit S V h.1) _).mp hab
          obtain ⟨bt, zc, ha, hb, hprod⟩ :=
            coarseOp_product_ne_zero (stopLabel S V) (joinRead S) _ _ a b hm
          change (synOf wX (CL.lperp (coordinateLinear L)) bt.1 ⊗ₖ proj wX bt.2) *
            (localRead L zc.1 ⊗ₖ readRegister (next (coordinateInsert S zc.1.1)) (V \ S) (h.2 _) zc.2) ≠ 0 at hprod
          rw [← Matrix.mul_kronecker_mul, localDual_mul_read, readRegister_zero_eq] at hprod
          have hdual : bt.1 = zc.1.2 := by
            by_contra hn
            exact hprod (by simp [hn])
          have htail : zc.2 = (0, 0) := by
            by_contra hn
            exact hprod (by simp [hn])
          rw [← ha, ← hb]
          simp [CLChecks.hidingRead, stopLabel, joinRead, hdual, htail]
      | succ k =>
          simp only [hideRegister, readRegister] at hab
          rw [← registerOp_mul] at hab
          have hm := (registerOp_ne_zero (coordinateSplit S V h.1) _).mp hab
          obtain ⟨zu, zv, ha, hb, hprod⟩ :=
            coarseOp_product_ne_zero (joinHide S) (joinRead S) _ _ a b hm
          rcases zu with ⟨z, u⟩
          rcases zv with ⟨z', v⟩
          obtain ⟨hz, ht⟩ := adaptiveTensor_product_ne_zero
            (localRead L) (localRead_isPVM L) _ _ (z, u) (z', v) hprod
          dsimp only at hz
          subst z'
          have hu := hideRegister_supported (next (coordinateInsert S z.1)) k (V \ S) (h.2 _) u
            (by intro he; exact ht (by rw [he, zero_mul]))
          have hv := readRegister_supported (next (coordinateInsert S z.1)) (V \ S) (h.2 _) v
            (by intro he; exact ht (by rw [he, mul_zero]))
          rw [← ha, ← hb]
          exact hidingRead_join L next (by omega) z u v c hu.1 hv.1
            (ih (coordinateInsert S z.1) k (by omega) (V \ S) (h.2 _) u v ht)

/-- Every rejected actual adjacent hiding comparison has zero honest operator product. -/
theorem hideOp_reject_next_zero (P : CL.CLFun F ι ℓ) (k : ℕ) (hk : k + 1 < ℓ)
    (h : P.SupportedOn Finset.univ) (a b : HideLabel F ι)
    (hab : ¬ CLChecks.hidingNext P k a b) : hideOp P k h a * hideOp P (k + 1) h b = 0 := by
  by_contra hn
  apply hab
  apply hideRegister_accepts_next P k hk Finset.univ h a b
  exact (registerOp_ne_zero univRestriction _).mp (by simpa only [hideOp, registerOp_mul] using hn)

/-- Every rejected terminal hiding/Read comparison has zero honest register product. -/
theorem hideOp_reject_read_zero {A : Type*} (P : CL.CLFun F ι ℓ) (k : ℕ) (hk : k + 1 = ℓ)
    (h : P.SupportedOn Finset.univ) (a : HideLabel F ι) (b : ReadLabel F ι) (c : A)
    (hab : ¬ CLChecks.hidingRead P a (b.1, b.2, c)) : hideOp P k h a * readOp P h b = 0 := by
  by_contra hn
  apply hab
  apply hideRegister_accepts_read P k hk Finset.univ h a b c
  exact (registerOp_ne_zero univRestriction _).mp
    (by simpa only [hideOp, readOp, registerOp_mul] using hn)

end MIPRE.Introspection.Honest
