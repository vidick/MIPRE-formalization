/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptivePrefixMixing

@[expose] public section

/-! # Initializing the adaptive residual measurement

At stage zero the used register is empty and the remaining register contains
every coordinate. The original measurement therefore gives the residual
measurement at prefix zero, by explicit coordinate restriction. Impossible
prefixes receive a deterministic malformed answer. Their prefix projectors
vanish, so the original measurement is recovered exactly, including its
malformed-answer operator.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the original measurement is a
POVM of block matrices over the coordinate register `ι → F` with entries in the first player's
algebra `𝒜` (`POVMIn _ (Matrix (ι → F) (ι → F) 𝒜)`), and a residual measurement at the prefix `y`
one of block matrices over the remaining register `stageRemaining P 0 y → F`. At prefix zero it
is the original measurement relabelled along `initialRegisterEquiv`, pushed forward along the
unital `⋆`-homomorphism `submatrixHom` (the `ΦA` of `regRelabel`); at an impossible prefix it is
the register readout of the constant malformed answer, entering as `smulKron 1 _`. The reassembly
through `prefixResidualOp` is an identity of block matrices, checked entry by entry.
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]

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

/-- At stage zero only prefix zero survives, and there are no used-register
indices left to constrain an operator entry. -/
theorem prefixResidualOp_initial_apply (P : CL.CLFun F ι ℓ) (y : ι → F)
    (M : Matrix (stageRemaining P 0 y → F) (stageRemaining P 0 y → F) 𝒜)
    (x x' : ι → F) :
    prefixResidualOp P 0 y M x x' =
      if y = 0 then M (fun i => x i) (fun i => x' i) else 0 := by
  have he : (fun i : CLChecks.prefixRegister P 0 y => x i) =
      (fun i : CLChecks.prefixRegister P 0 y => x' i) := by
    funext i
    have hi : i.val ∈ (∅ : Finset ι) := by
      simpa only [prefixRegister_initial] using i.property
    simp at hi
  rw [prefixResidualOp, regSplitHom_apply, smulKron_apply, Matrix.smul_apply]
  change (Honest.prefixProjector P 0 y (fun i => x i) (fun i => x' i)) •
      M (fun i => x i) (fun i => x' i) = _
  simp only [Honest.prefixProjector, readout, Matrix.diagonal_apply, he, ite_true,
    CL.CLFun.truncate_zero, CL.CLFun.eval_zero]
  by_cases hy : y = 0 <;> simp [hy, eq_comm]

section Measurement

variable [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]

/-- The initial residual measurement retains the complete option-valued
answer alphabet. At an impossible prefix it returns `none` deterministically. -/
def initialResidualPOVM (P : CL.CLFun F ι ℓ)
    (N : POVMIn (Option ((ι → F) × A)) (Matrix (ι → F) (ι → F) 𝒜)) (y : ι → F) :
    POVMIn (Option ((ι → F) × A))
      (Matrix (stageRemaining P 0 y → F) (stageRemaining P 0 y → F) 𝒜) :=
  if y = 0 then
    N.pushforward (submatrixHom (initialRegisterEquiv P y)) (submatrixHom_one _)
  else
    (IsPVMIn.smulKron_one (R := 𝒜) (readout_isPVM (fun _ : stageRemaining P 0 y → F =>
      (none : Option ((ι → F) × A)))).toIn).toPOVMIn

theorem initialResidualPOVM_isPVM (P : CL.CLFun F ι ℓ)
    (N : POVMIn (Option ((ι → F) × A)) (Matrix (ι → F) (ι → F) 𝒜))
    (hN : IsPVMIn N.op) (y : ι → F) :
    IsPVMIn (initialResidualPOVM P N y).op := by
  by_cases hy : y = 0
  · rw [initialResidualPOVM, ite_eq_left hy]
    exact POVMIn.isPVMIn_pushforward _ _ hN
  · rw [initialResidualPOVM, ite_eq_right hy]
    exact IsPVMIn.smulKron_one (readout_isPVM _).toIn

theorem initialResidualPOVM_block (P : CL.CLFun F ι ℓ)
    (N : POVMIn (Option ((ι → F) × A)) (Matrix (ι → F) (ι → F) 𝒜))
    (y : ι → F) (b : Option ((ι → F) × A)) :
    prefixResidualOp P 0 y ((initialResidualPOVM P N y).op b) =
      if y = 0 then N.op b else 0 := by
  ext x x'
  rw [prefixResidualOp_initial_apply]
  by_cases hy : y = 0
  · rw [ite_eq_left hy, ite_eq_left hy, initialResidualPOVM, ite_eq_left hy, POVMIn.pushforward_op,
      submatrixHom_apply, submatrix_apply]
    rfl
  · rw [ite_eq_right hy, ite_eq_right hy, Matrix.zero_apply]

/-- Exact initialization of the full option-valued prefix invariant. No
projectivity or success assumption is required for this algebraic equality. -/
theorem initialResidualPOVM_reassembly (P : CL.CLFun F ι ℓ)
    (N : POVMIn (Option ((ι → F) × A)) (Matrix (ι → F) (ι → F) 𝒜))
    (b : Option ((ι → F) × A)) :
    N.op b = ∑ y, prefixResidualOp P 0 y ((initialResidualPOVM P N y).op b) := by
  simp only [initialResidualPOVM_block, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Every valid residual answer is supported on its claimed initial prefix;
the malformed answer is retained without a zero-operator assumption. -/
theorem initialResidualPOVM_some_support (P : CL.CLFun F ι ℓ)
    (N : POVMIn (Option ((ι → F) × A)) (Matrix (ι → F) (ι → F) 𝒜))
    (y x : ι → F) (a : A) (hy : P.outputPrefix 0 x ≠ y) :
    (initialResidualPOVM P N y).op (some (x, a)) = 0 := by
  have hn : y ≠ 0 := by
    intro he
    exact hy (by simpa only [he] using P.outputPrefix_zero x)
  rw [initialResidualPOVM, ite_eq_right hn, IsPVMIn.toPOVMIn_op]
  ext i j
  simp [readout, smulKron_apply]

/-- Every projective measurement has the concrete initial adaptive form,
with the original ancilla and the full option-valued answer alphabet. -/
theorem exists_initial_residual (P : CL.CLFun F ι ℓ)
    (N : POVMIn (Option ((ι → F) × A)) (Matrix (ι → F) (ι → F) 𝒜))
    (hN : IsPVMIn N.op) :
    ∃ M : (y : ι → F) → POVMIn (Option ((ι → F) × A))
        (Matrix (stageRemaining P 0 y → F) (stageRemaining P 0 y → F) 𝒜),
      (∀ y, IsPVMIn (M y).op) ∧
      (∀ b, N.op b = ∑ y, prefixResidualOp P 0 y ((M y).op b)) ∧
      (∀ y x a, P.outputPrefix 0 x ≠ y → (M y).op (some (x, a)) = 0) :=
  ⟨initialResidualPOVM P N, initialResidualPOVM_isPVM P N hN,
    initialResidualPOVM_reassembly P N, initialResidualPOVM_some_support P N⟩

end Measurement

end MIPRE.Introspection
end

end
