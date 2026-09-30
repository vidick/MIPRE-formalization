/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptivePrefixMixing

@[expose] public section

/-! # The actual adaptive computational readout

Reading a seed and retaining its CL prefix and selected next coordinates is
exactly the prefix projector tensored with the next local Z measurement.
The outcome type remembers the prefix, so the selected register can vary.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the readouts are register
operators over `ℂ`, and their relabelling identities (`registerOp_readout_fst`,
`registerOp_readout_pair`) are unchanged. They enter the first player's algebra `Matrix I I 𝒜` as
`smulKron 1`, so the factorizations through a register split (`registerReadout_wZ`) and through the
prefix reinsertion `prefixResidualOp` (`prefixResidualOp_readout`, `adaptiveZ_readout_factor`) are
identities of block matrices over any algebra `𝒜`. The one step they share: `X ⊗ (P ⊗ N)`, read
along `e : I ≃ J × R`, is `regSplitHom e` applied to the block matrix `(X ⊗ N) ⊗ P`.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

section Readout

variable {I J R C : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

theorem registerOp_readout_fst (e : I ≃ J × R) (f : J → C) (c : C) :
    registerOp e (readout f c ⊗ₖ (1 : Matrix R R ℂ)) =
      readout (fun i => f (e i).1) c := by
  ext i j
  simp only [registerOp_apply, Matrix.kroneckerMap_apply, readout,
    Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have he : ¬ ((e i).1 = (e j).1 ∧ (e i).2 = (e j).2) := by
      intro h
      exact hij (e.injective (Prod.ext h.1 h.2))
    rcases not_and_or.mp he with he | he <;> simp [hij, he]

theorem registerOp_readout_pair (e : I ≃ J × R)
    (f : J → C) (c : C) {D : Type*} [Fintype D] [DecidableEq D]
    (g : R → D) (d : D) :
    registerOp e (readout f c ⊗ₖ readout g d) =
      readout (fun i => (f (e i).1, g (e i).2)) (c, d) := by
  ext i j
  simp only [registerOp_apply, Matrix.kroneckerMap_apply, readout,
    Matrix.diagonal_apply, Prod.mk.injEq]
  by_cases hij : i = j
  · subst j
    by_cases hf : f (e i).1 = c <;> by_cases hg : g (e i).2 = d <;> simp [hf, hg]
  · have he : ¬ ((e i).1 = (e j).1 ∧ (e i).2 = (e j).2) := by
      intro h
      exact hij (e.injective (Prod.ext h.1 h.2))
    rcases not_and_or.mp he with he | he <;> simp [hij, he]

/-- A register operator `P ⊗ N`, read along `e : I ≃ J × R` and tensored with `X`, is the block
matrix `(X ⊗ N) ⊗ P` over `J` of block matrices over `R`, read along the split. -/
private theorem smulKron_registerOp_kron {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
    (e : I ≃ J × R) (X : 𝒜) (P : Matrix J J ℂ) (N : Matrix R R ℂ) :
    smulKron X (registerOp e (P ⊗ₖ N)) = regSplitHom e (smulKron (smulKron X N) P) := by
  ext i i'
  simp only [smulKron_apply, registerOp_apply, regSplitHom_apply, kroneckerMap_apply, mul_smul,
    Matrix.smul_apply]

end Readout

variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {ℓ : ℕ}
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]

/-- The Z readout of a linear map on the selected coordinates of a register is the readout of the
map on those coordinates, as a register operator. -/
theorem registerReadout_wZ {I R : Type*} [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R] {n : ℕ}
    (e : I ≃ (Fin n → F) × R) (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (z : Fin n → F) :
    (registerReadout e wZ L z : Matrix I I 𝒜) = smulKron 1 (readout (fun i => L (e i).1) z) := by
  rw [registerReadout, ← readout_eq_synOf, ← registerOp_readout_fst e (⇑L) z,
    smulKron_registerOp_kron, smulKron_one_one]

/-- A register readout reinserted behind its prefix projector is the joint readout of the prefix
and of the residual label. -/
theorem prefixResidualOp_readout (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) {C : Type*} [Fintype C] [DecidableEq C]
    (g : (stageRemaining P k y → F) → C) (z : C) :
    prefixResidualOp P k y (smulKron (1 : 𝒜) (readout g z)) =
      smulKron 1 (readout (fun x => ((P.truncate k).eval x,
        g (ambientSplit (CLChecks.prefixRegister P k y) x).2)) (y, z)) := by
  have hp x : (P.truncate k).eval x = y ↔
      (P.truncate k).eval (Honest.insertRegister (CLChecks.prefixRegister P k y)
        (ambientSplit (CLChecks.prefixRegister P k y) x).1) = y := by
    rw [Honest.insertRegister_ambientSplit]
    exact CLChecks.truncate_fibre_proj hP k y x
  rw [prefixResidualOp, ← smulKron_registerOp_kron, Honest.prefixProjector,
    registerOp_readout_pair]
  congr 1
  ext i j
  simp only [readout, Matrix.diagonal_apply, Prod.mk.injEq]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    exact if_congr (and_congr (hp i).symm Iff.rfl) rfl rfl
  · simp [hij]

/-- The actual seed coarse-graining keeps the CL prefix and its selected next register. -/
def adaptiveZOutcome (P : CL.CLFun F ι ℓ) (k : ℕ) (x : ι → F) :
    (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F) :=
  ⟨(P.truncate k).eval x, coordinateRestrict (P.factorOfPrefix k ((P.truncate k).eval x)) x⟩

/-- Exact factorization of the actual adaptive Z readout, including zero-weight prefixes. -/
theorem adaptiveZ_readout_factor (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    smulKron (1 : 𝒜) (readout (adaptiveZOutcome P k) ⟨y, z⟩) =
      prefixResidualOp P k y (registerReadout (stageSplit P hP k y) wZ LinearMap.id z) := by
  rw [registerReadout_wZ, prefixResidualOp_readout P hP]
  congr 1
  ext x x'
  simp only [readout, Matrix.diagonal_apply]
  by_cases hxx : x = x'
  · subst x'
    simp only [ite_true]
    apply if_congr _ rfl rfl
    by_cases hy : (P.truncate k).eval x = y
    · subst y
      simp only [adaptiveZOutcome, Sigma.mk.inj_iff, heq_eq_eq, true_and, Prod.mk.injEq]
      rfl
    · have hn : adaptiveZOutcome P k x ≠ ⟨y, z⟩ := by
        intro he
        exact hy (congrArg Sigma.fst he)
      simp [hn, hy]
  · simp [hxx]

end MIPRE.Introspection

end

end
