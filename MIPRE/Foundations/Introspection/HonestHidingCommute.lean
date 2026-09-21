/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestHidingStep
import MIPRE.Foundations.Introspection.HonestHiding

/-! # Commutation along the honest hiding chain

The base step uses the concrete dual-X/tail factorization of the stopping
measurement. Earlier adaptive stages lift the step using orthogonality of the
shared local Z/dual-X measurement. Different branch labels therefore vanish
before any commutation claim about different continuations is needed.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

section Composition
variable {I J A B C U V : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

theorem pvm_commute {P : A → Matrix I I ℂ} (hP : IsPVM P) (a b : A) :
    Commute (P a) (P b) := by
  show _ * _ = _ * _
  by_cases h : a = b
  · subst b; rfl
  · rw [hP.orthogonal h, hP.orthogonal (Ne.symm h)]

theorem coarseOp_commute (f : A → U) (g : B → V)
    (P : A → Matrix I I ℂ) (Q : B → Matrix I I ℂ)
    (hc : ∀ a b, Commute (P a) (Q b)) (u : U) (v : V) :
    Commute (coarseOp f P u) (coarseOp g Q v) := by
  apply Commute.sum_left
  intro a _
  apply Commute.sum_right
  intro b _
  exact hc a b

theorem registerOp_commute (e : I ≃ J) {P Q : Matrix J J ℂ} (hc : Commute P Q) :
    Commute (registerOp e P) (registerOp e Q) := by
  show _ * _ = _ * _
  rw [← registerOp_mul, ← registerOp_mul, hc.eq]

theorem kronecker_commute {P P' : Matrix I I ℂ} {Q Q' : Matrix J J ℂ}
    (hP : Commute P P') (hQ : Commute Q Q') : Commute (P ⊗ₖ Q) (P' ⊗ₖ Q') := by
  show _ * _ = _ * _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hP.eq, hQ.eq]

/-- Shared earlier outcomes either agree, or orthogonality kills both products. -/
theorem adaptiveTensor_commute (P : A → Matrix I I ℂ) (hP : IsPVM P)
    (Q : A → B → Matrix J J ℂ) (R : A → C → Matrix J J ℂ)
    (hc : ∀ a b c, Commute (Q a b) (R a c)) (ab : A × B) (ac : A × C) :
    Commute (adaptiveTensor P Q ab) (adaptiveTensor P R ac) := by
  rcases ab with ⟨a, b⟩
  rcases ac with ⟨a', c⟩
  change (P a ⊗ₖ Q a b) * (P a' ⊗ₖ R a' c) = (P a' ⊗ₖ R a' c) * (P a ⊗ₖ Q a b)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  by_cases ha : a = a'
  · subst a'
    rw [(hc a b c).eq]
  · rw [hP.orthogonal ha, hP.orthogonal (Ne.symm ha)]
    simp

end Composition

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

theorem pauliX_commute_stopHide (P : CL.CLFun F ι ℓ) (V : Finset ι)
    (x : V → F) (a : HideLabel F ι) : Commute (proj wX x) (stopHide P V a) := by
  apply Commute.sum_right
  intro y _
  show _ * _ = _ * _
  rw [proj_mul_proj isWeylFamily_wX, proj_mul_proj isWeylFamily_wX]
  by_cases h : x = y
  · subst y; rfl
  · simp [h, Ne.symm h]

theorem localDual_commute_read {S : Finset ι} (L : CL.RegLinear F S)
    (b : Fin (Fintype.card S) → F)
    (a : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) :
    Commute (synOf wX (CL.lperp (coordinateLinear L)) b) (localRead L a) := by
  have hz := linear_measurements_commute (coordinateLinear L) (CL.lperp (coordinateLinear L))
    (by simp only [CL.ker_lperp, CL.perp_perp]; exact le_rfl) a.1 b
  have hx := pvm_commute (linear_measurement_isPVM wX isWeylFamily_wX
    (CL.lperp (coordinateLinear L))) b a.2
  show _ * (_ * _) = (_ * _) * _
  rw [← mul_assoc, hz.eq.symm, mul_assoc, hx.eq, ← mul_assoc]

/-- A stopping node commutes with the next local joint read and any X-compatible tail. -/
theorem stopHide_commute_adaptive {B U : Type*} [Fintype B] [DecidableEq B]
    [Fintype U] [DecidableEq U]
    (S V : Finset ι) (h : S ⊆ V) (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (Q : ((Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) →
      B → Matrix (↥(V \ S) → F) (↥(V \ S) → F) ℂ)
    (hc : ∀ z x b, Commute (proj wX x) (Q z b))
    (f : (((Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) × B) → U)
    (a : HideLabel F ι) (b : U) :
    Commute (stopHide (.cons S L next) V a)
      (registerOp (coordinateSplit S V h) (coarseOp f (adaptiveTensor (localRead L) Q) b)) := by
  rw [stopHide_split S V h L next]
  apply registerOp_commute
  apply coarseOp_commute
  intro bt zc
  exact kronecker_commute (localDual_commute_read L bt.1 zc.1) (hc zc.1 bt.2 zc.2)

set_option backward.isDefEq.respectTransparency false in
/-- Every pair of neighboring honest hiding levels commutes on every answer label. -/
theorem hideRegister_commute_next (P : CL.CLFun F ι ℓ) (k : ℕ)
    (V : Finset ι) (h : P.SupportedOn V) (a b : HideLabel F ι) :
    Commute (hideRegister P k V h a) (hideRegister P (k + 1) V h b) := by
  induction P generalizing V k a b with
  | zero =>
      cases k <;> exact pvm_commute (stopHide_isPVM _ _) a b
  | cons S L next ih =>
      cases k with
      | zero =>
          simp only [hideRegister, hideRegister_zero_fun]
          change Commute (stopHide (.cons S L next) V a)
            (registerOp (coordinateSplit S V h.1) (coarseOp (joinHide S)
              (adaptiveTensor (localRead L)
                (fun z => stopHide (next (coordinateInsert S z.1)) (V \ S))) b))
          exact stopHide_commute_adaptive S V h.1 L next
            (fun z => stopHide (next (coordinateInsert S z.1)) (V \ S))
            (fun z x c => pauliX_commute_stopHide (next (coordinateInsert S z.1)) (V \ S) x c)
            (joinHide S) a b
      | succ k =>
          simp only [hideRegister]
          change Commute
            (registerOp (coordinateSplit S V h.1) (coarseOp (joinHide S)
              (adaptiveTensor (localRead L)
                (fun z => hideRegister (next (coordinateInsert S z.1)) k (V \ S) (h.2 _))) a))
            (registerOp (coordinateSplit S V h.1) (coarseOp (joinHide S)
              (adaptiveTensor (localRead L)
                (fun z => hideRegister (next (coordinateInsert S z.1)) (k + 1) (V \ S) (h.2 _))) b))
          apply registerOp_commute
          apply coarseOp_commute (joinHide S) (joinHide S)
          exact adaptiveTensor_commute (localRead L) (localRead_isPVM L) _ _
            (fun z c d => ih (coordinateInsert S z.1) k (V \ S) (h.2 _) c d)

theorem pauliX_commute_readRegister_zero (P : CL.CLFun F ι 0) (V : Finset ι)
    (h : P.SupportedOn V) (x : V → F) (a : ReadLabel F ι) :
    Commute (proj wX x) (readRegister P V h a) := by
  cases P
  change Commute _ (if a = (0, 0) then 1 else 0)
  split
  · exact Commute.one_right _
  · exact Commute.zero_right _

set_option backward.isDefEq.respectTransparency false in
/-- The terminal honest hiding level commutes with the complete adaptive Read family. -/
theorem hideRegister_commute_read (P : CL.CLFun F ι ℓ) (k : ℕ) (hk : ℓ ≤ k + 1)
    (V : Finset ι) (h : P.SupportedOn V) (a : HideLabel F ι) (b : ReadLabel F ι) :
    Commute (hideRegister P k V h a) (readRegister P V h b) := by
  induction P generalizing V k a b with
  | zero =>
      change Commute _ (if b = (0, 0) then 1 else 0)
      split
      · exact Commute.one_right _
      · exact Commute.zero_right _
  | @cons n S L next ih =>
      cases k with
      | zero =>
          have hn : n = 0 := by omega
          subst n
          apply stopHide_commute_adaptive S V h.1 L next _ _ (joinRead S) a b
          intro z x c
          exact pauliX_commute_readRegister_zero _ _ _ x c
      | succ k =>
          apply registerOp_commute
          apply coarseOp_commute (joinHide S) (joinRead S)
          exact adaptiveTensor_commute (localRead L) (localRead_isPVM L) _ _
            (fun z c d => ih (coordinateInsert S z.1) k (by omega) (V \ S) (h.2 _) c d)

theorem hideOp_commute_next (P : CL.CLFun F ι ℓ) (k : ℕ)
    (h : P.SupportedOn Finset.univ) (a b : HideLabel F ι) :
    Commute (hideOp P k h a) (hideOp P (k + 1) h b) :=
  registerOp_commute _ (hideRegister_commute_next P k _ h a b)

theorem hideOp_commute_read (P : CL.CLFun F ι ℓ) (k : ℕ) (hk : ℓ ≤ k + 1)
    (h : P.SupportedOn Finset.univ) (a : HideLabel F ι) (b : ReadLabel F ι) :
    Commute (hideOp P k h a) (readOp P h b) :=
  registerOp_commute _ (hideRegister_commute_read P k hk _ h a b)

end MIPRE.Introspection.Honest
