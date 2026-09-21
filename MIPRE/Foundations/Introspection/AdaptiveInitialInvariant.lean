/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePrefixMixing

/-! # Initializing the adaptive residual measurement

At stage zero the used register is empty and the remaining register contains
every coordinate. The original measurement therefore gives the residual
measurement at prefix zero, by explicit coordinate restriction. Impossible
prefixes receive a deterministic malformed answer. Their prefix projectors
vanish, so the original measurement is recovered exactly, including its
malformed-answer operator.
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}

theorem prefixRegister_initial (P : CL.CLFun F ι ℓ) (y : ι → F) :
    CLChecks.prefixRegister P 0 y = ∅ := by
  cases P <;> rfl

theorem stageRemaining_initial (P : CL.CLFun F ι ℓ) (y : ι → F) :
    stageRemaining P 0 y = univ := by
  simp only [stageRemaining, prefixRegister_initial, Finset.compl_empty]

/-- The zero-stage remaining register is the actual original coordinate
register, with no choice of an arbitrary basis equivalence. -/
def initialRegisterEquiv (P : CL.CLFun F ι ℓ) (y : ι → F) :
    (stageRemaining P 0 y → F) ≃ (ι → F) where
  toFun u i := u ⟨i, by rw [stageRemaining_initial]; exact mem_univ i⟩
  invFun x i := x i
  left_inv u := by funext i; rfl
  right_inv x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- At stage zero only prefix zero survives, and there are no used-register
indices left to constrain an operator entry. -/
theorem prefixResidualOp_initial_apply (P : CL.CLFun F ι ℓ) (y : ι → F)
    (M : Matrix ((stageRemaining P 0 y → F) × H)
      ((stageRemaining P 0 y → F) × H) ℂ)
    (x x' : ι → F) (a a' : H) :
    prefixResidualOp P 0 y M (x, a) (x', a') =
      if y = 0 then M (fun i => x i, a) (fun i => x' i, a') else 0 := by
  have he : (fun i : CLChecks.prefixRegister P 0 y => x i) =
      (fun i : CLChecks.prefixRegister P 0 y => x' i) := by
    funext i
    have hi : i.val ∈ (∅ : Finset ι) := by
      simpa only [prefixRegister_initial] using i.property
    exact False.elim (Finset.not_mem_empty i.val hi)
  unfold prefixResidualOp Honest.prefixProjector
  simp only [registerOp_apply, registerParty, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.prodAssoc_apply, ambientSplit,
    Matrix.kroneckerMap_apply, readout, Matrix.diagonal_apply,
    he, if_true, CL.CLFun.truncate_zero, CL.CLFun.eval_zero]
  by_cases hy : y = 0 <;> simp [hy, eq_comm]

/-- The initial residual measurement retains the complete option-valued
answer alphabet. At an impossible prefix it returns `none` deterministically. -/
def initialResidualPOVM (P : CL.CLFun F ι ℓ)
    (N : POVM (Option ((ι → F) × A)) ((ι → F) × H)) (y : ι → F) :
    POVM (Option ((ι → F) × A)) ((stageRemaining P 0 y → F) × H) :=
  if y = 0 then
    registerPOVM ((initialRegisterEquiv P y).prodCongr (Equiv.refl H)) N
  else
    (readout_isPVM (fun _ : (stageRemaining P 0 y → F) × H =>
      (none : Option ((ι → F) × A)))).toPOVM

theorem initialResidualPOVM_isPVM (P : CL.CLFun F ι ℓ)
    (N : POVM (Option ((ι → F) × A)) ((ι → F) × H))
    (hN : IsPVM (fun a => (N.mats a).val)) (y : ι → F) :
    IsPVM (fun a => ((initialResidualPOVM P N y).mats a).val) := by
  by_cases hy : y = 0
  · simpa only [initialResidualPOVM, if_pos hy, registerPOVM_mats] using
      registerOp_isPVM ((initialRegisterEquiv P y).prodCongr (Equiv.refl H)) hN
  · simpa only [initialResidualPOVM, if_neg hy, IsPVM.toPOVM_mats] using
      readout_isPVM (fun _ : (stageRemaining P 0 y → F) × H =>
        (none : Option ((ι → F) × A)))

set_option backward.isDefEq.respectTransparency false in
theorem initialResidualPOVM_block (P : CL.CLFun F ι ℓ)
    (N : POVM (Option ((ι → F) × A)) ((ι → F) × H))
    (y : ι → F) (b : Option ((ι → F) × A)) :
    prefixResidualOp P 0 y ((initialResidualPOVM P N y).mats b).val =
      if y = 0 then (N.mats b).val else 0 := by
  ext ⟨x, a⟩ ⟨x', a'⟩
  rw [prefixResidualOp_initial_apply]
  by_cases hy : y = 0
  · simp only [if_pos hy, initialResidualPOVM, registerPOVM_mats, registerOp_apply,
      Equiv.prodCongr_apply, Equiv.refl_apply, initialRegisterEquiv]
  · simp only [if_neg hy, Matrix.zero_apply]

/-- Exact initialization of the full option-valued prefix invariant. No
projectivity or success assumption is required for this algebraic equality. -/
theorem initialResidualPOVM_reassembly (P : CL.CLFun F ι ℓ)
    (N : POVM (Option ((ι → F) × A)) ((ι → F) × H))
    (b : Option ((ι → F) × A)) :
    (N.mats b).val =
      ∑ y, prefixResidualOp P 0 y ((initialResidualPOVM P N y).mats b).val := by
  simp only [initialResidualPOVM_block, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Every valid residual answer is supported on its claimed initial prefix;
the malformed answer is retained without a zero-operator assumption. -/
theorem initialResidualPOVM_some_support (P : CL.CLFun F ι ℓ)
    (N : POVM (Option ((ι → F) × A)) ((ι → F) × H))
    (y x : ι → F) (a : A) (hy : P.outputPrefix 0 x ≠ y) :
    ((initialResidualPOVM P N y).mats (some (x, a))).val = 0 := by
  have hn : y ≠ 0 := by
    intro he
    exact hy (by simpa only [he] using P.outputPrefix_zero x)
  ext i j
  simp [initialResidualPOVM, hn, IsPVM.toPOVM_mats, readout]

/-- Every projective measurement has the concrete initial adaptive form,
with the original ancilla and the full option-valued answer alphabet. -/
theorem exists_initial_residual (P : CL.CLFun F ι ℓ)
    (N : POVM (Option ((ι → F) × A)) ((ι → F) × H))
    (hN : IsPVM (fun a => (N.mats a).val)) :
    ∃ M : (y : ι → F) →
        POVM (Option ((ι → F) × A)) ((stageRemaining P 0 y → F) × H),
      (∀ y, IsPVM (fun a => ((M y).mats a).val)) ∧
      (∀ b, (N.mats b).val = ∑ y, prefixResidualOp P 0 y ((M y).mats b).val) ∧
      (∀ y x a, P.outputPrefix 0 x ≠ y → ((M y).mats (some (x, a))).val = 0) := by
  exact ⟨initialResidualPOVM P N, initialResidualPOVM_isPVM P N hN,
    initialResidualPOVM_reassembly P N, initialResidualPOVM_some_support P N⟩

end MIPRE.Introspection
end
