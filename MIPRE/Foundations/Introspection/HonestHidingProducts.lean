/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestHidingStep

/-! # Exact products at an honest hiding transition -/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

section Witness
variable {I J A B C U V : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

theorem registerOp_ne_zero (e : I ≃ J) (P : Matrix J J ℂ) : registerOp e P ≠ 0 ↔ P ≠ 0 := by
  constructor
  · intro h he
    exact h (he ▸ rfl)
  · intro h he
    have hh := congrArg (registerOp e.symm) he
    rw [registerOp_inv] at hh
    exact h hh

theorem coarseOp_product_ne_zero (f : A → U) (g : B → V)
    (P : A → Matrix I I ℂ) (Q : B → Matrix I I ℂ) (u : U) (v : V)
    (h : coarseOp f P u * coarseOp g Q v ≠ 0) :
    ∃ a b, f a = u ∧ g b = v ∧ P a * Q b ≠ 0 := by
  unfold coarseOp at h
  rw [Finset.sum_mul] at h
  obtain ⟨a, ha, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mul_sum] at hprod
  obtain ⟨b, hb, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hprod
  exact ⟨a, b, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, hne⟩

theorem adaptiveTensor_product_ne_zero (P : A → Matrix I I ℂ) (hP : IsPVM P)
    (Q : A → B → Matrix J J ℂ) (R : A → C → Matrix J J ℂ)
    (ab : A × B) (ac : A × C)
    (h : adaptiveTensor P Q ab * adaptiveTensor P R ac ≠ 0) :
    ab.1 = ac.1 ∧ Q ab.1 ab.2 * R ac.1 ac.2 ≠ 0 := by
  change (P ab.1 ⊗ₖ Q ab.1 ab.2) * (P ac.1 ⊗ₖ R ac.1 ac.2) ≠ 0 at h
  rw [← Matrix.mul_kronecker_mul] at h
  constructor
  · by_contra hn
    exact h (by rw [hP.orthogonal hn]; simp)
  · intro hn
    exact h (by rw [hn]; simp)

end Witness

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- A complete X answer fixes the stopping Hide answer exactly. -/
theorem pauliX_mul_stopHide (P : CL.CLFun F ι ℓ) (V : Finset ι)
    (x : V → F) (a : HideLabel F ι) :
    proj wX x * stopHide P V a =
      if stopHideAnswer P V x = a then proj wX x else 0 := by
  unfold stopHide synOf
  rw [Finset.mul_sum]
  simp only [proj_mul_proj isWeylFamily_wX]
  by_cases h : stopHideAnswer P V x = a
  · rw [if_pos h, Finset.sum_eq_single_of_mem x (by simp [h])]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y hy
    have hxy : x ≠ y := by
      intro he
      subst y
      exact h (Finset.mem_filter.mp hy).2
    simp [hxy]

/-- The current local dual value is retained by the next joint Z/dual-X read. -/
theorem localDual_mul_read {S : Finset ι} (L : CL.RegLinear F S)
    (b : Fin (Fintype.card S) → F)
    (a : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) :
    synOf wX (CL.lperp (coordinateLinear L)) b * localRead L a =
      if b = a.2 then localRead L a else 0 := by
  have hz := linear_measurements_commute (coordinateLinear L) (CL.lperp (coordinateLinear L))
    (by simp only [CL.ker_lperp, CL.perp_perp]; exact le_rfl) a.1 b
  unfold localRead
  rw [← mul_assoc, hz.eq.symm, mul_assoc,
    (linear_measurement_isPVM wX isWeylFamily_wX (CL.lperp (coordinateLinear L))).mul_eq_ite]
  by_cases hb : b = a.2
  · simp [hb]
  · simp [hb]

/-- Both tested X data are retained at the first actual adaptive hiding transition. -/
theorem stop_local_product (S V : Finset ι) (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (bt : (Fin (Fintype.card S) → F) × (↥(V \ S) → F))
    (a : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
    (v : HideLabel F ι) :
    (synOf wX (CL.lperp (coordinateLinear L)) bt.1 ⊗ₖ proj wX bt.2) *
      (localRead L a ⊗ₖ stopHide (next (coordinateInsert S a.1)) (V \ S) v) =
      if bt.1 = a.2 ∧ stopHideAnswer (next (coordinateInsert S a.1)) (V \ S) bt.2 = v then
        localRead L a ⊗ₖ proj wX bt.2 else 0 := by
  rw [← Matrix.mul_kronecker_mul, localDual_mul_read, pauliX_mul_stopHide]
  by_cases hb : bt.1 = a.2 <;>
    by_cases ht : stopHideAnswer (next (coordinateInsert S a.1)) (V \ S) bt.2 = v <;>
    simp [hb, ht]

end MIPRE.Introspection.Honest
