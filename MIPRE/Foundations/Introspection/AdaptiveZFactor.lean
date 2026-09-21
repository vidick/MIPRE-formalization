/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePrefixMixing

/-! # The actual adaptive computational readout

Reading a seed and retaining its CL prefix and selected next coordinates is
exactly the prefix projector tensored with the next local Z measurement.
The outcome type remembers the prefix, so the selected register can vary.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

section Readout

variable {I J R H C : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype R] [DecidableEq R]
  [Fintype H] [DecidableEq H] [Fintype C] [DecidableEq C]

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

end Readout

variable {ι F H : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] {ℓ : ℕ}

theorem registerReadout_wZ {I R : Type*} [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R] {n : ℕ}
    (e : I ≃ (Fin n → F) × R) (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (z : Fin n → F) :
    registerReadout (H := H) e wZ L z = aOp (readout (fun i => L (e i).1) z) := by
  unfold registerReadout
  rw [← readout_eq_synOf]
  rw [aOp, registerOp_readout_fst]
  rw [show (fun i : I × H => L (registerParty e H i).1) =
      (fun i : I × H => L (e i.1).1) from rfl]
  ext i j
  simp only [readout, Matrix.diagonal_apply, aOp, Matrix.kroneckerMap_apply, Matrix.one_apply]
  by_cases hi : i.1 = j.1 <;> by_cases hh : i.2 = j.2 <;>
    simp [Prod.ext_iff, hi, hh]

theorem prefixResidualOp_readout (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) {C : Type*} [Fintype C] [DecidableEq C]
    (g : (stageRemaining P k y → F) → C) (z : C) :
    prefixResidualOp (H := H) P k y (aOp (readout g z)) =
      aOp (readout (fun x => ((P.truncate k).eval x,
        g (ambientSplit (CLChecks.prefixRegister P k y) x).2)) (y, z)) := by
  have hp x : (P.truncate k).eval x = y ↔
      (P.truncate k).eval (Honest.insertRegister (CLChecks.prefixRegister P k y)
        (ambientSplit (CLChecks.prefixRegister P k y) x).1) = y := by
    rw [Honest.insertRegister_ambientSplit]
    exact CLChecks.truncate_fibre_proj hP k y x
  unfold prefixResidualOp Honest.prefixProjector
  rw [show (aOp (readout g z) : Matrix ((stageRemaining P k y → F) × H) _ ℂ) =
      readout (fun p => g p.1) z from by
        ext i j
        simp only [aOp, readout, Matrix.diagonal_apply, Matrix.kroneckerMap_apply,
          Matrix.one_apply]
        by_cases hi : i.1 = j.1 <;> by_cases hh : i.2 = j.2 <;>
          simp [Prod.ext_iff, hi, hh]]
  rw [registerOp_readout_pair]
  ext i j
  simp only [readout, Matrix.diagonal_apply, aOp, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases hi : i.1 = j.1 <;> by_cases hh : i.2 = j.2
  · have hij := Prod.ext hi hh
    subst j
    simp only [if_true, mul_one]
    exact if_congr (and_congr (hp i.1).symm Iff.rfl) rfl rfl
  all_goals simp [Prod.ext_iff, hi, hh]

/-- The actual seed coarse-graining keeps the CL prefix and its selected next register. -/
def adaptiveZOutcome (P : CL.CLFun F ι ℓ) (k : ℕ) (x : ι → F) :
    (y : ι → F) × (Fin (Fintype.card (P.factorOfPrefix k y)) → F) :=
  ⟨(P.truncate k).eval x, coordinateRestrict (P.factorOfPrefix k ((P.truncate k).eval x)) x⟩

/-- Exact factorization of the actual adaptive Z readout, including zero-weight prefixes. -/
theorem adaptiveZ_readout_factor (P : CL.CLFun F ι ℓ) (hP : P.SupportedOn univ)
    (k : ℕ) (y : ι → F) (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F) :
    (aOp (readout (adaptiveZOutcome P k) ⟨y, z⟩) : Matrix ((ι → F) × H) _ ℂ) =
      prefixResidualOp P k y (registerReadout (stageSplit P hP k y) wZ LinearMap.id z) := by
  rw [registerReadout_wZ, prefixResidualOp_readout P hP]
  congr 1
  ext x x'
  simp only [readout, Matrix.diagonal_apply]
  by_cases hxx : x = x'
  · subst x'
    simp only [if_true]
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
