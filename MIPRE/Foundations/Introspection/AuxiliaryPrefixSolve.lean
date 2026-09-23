/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptivePrefixFactor
import MIPRE.Foundations.Introspection.AdaptiveResidual
import MIPRE.Foundations.LowDegree.BinaryMatrixSolve

/-! # Witness-preserving attainable-prefix extension

A source sampler only promises correct linear and factor queries on attained
prefixes. The next witness is obtained by binary Gaussian elimination and
replacing only the fresh register in the preceding witness. This preserves
all earlier outputs and avoids enumerating the exponentially larger seed set.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryPrefix
open Finset CLChecks

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

theorem mapOfPrefix_outputPrefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    P.mapOfPrefix k (P.outputPrefix k y) = P.mapOfPrefix k y := by
  induction P generalizing T k y with
  | zero => simp
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨ha, hb⟩ := proj_outputPrefix_cons hP k y
      simp only [CL.CLFun.mapOfPrefix_cons_succ]
      rw [ha, hb, ih _ (hP.2 _) k _]

theorem outputPrefix_step {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    P.outputPrefix (k + 1) y = P.outputPrefix k y + CL.proj (P.factorOfPrefix k y) y := by
  have hd : Disjoint (prefixRegister P k y) (P.factorOfPrefix k y) := by
    apply disjoint_left.mpr
    intro i hi hs
    exact (mem_sdiff.mp (stageFactor_subset_residual hP k y hs)).2 hi
  rw [← proj_prefixRegister hP, prefixRegister_step, CL.proj_union_of_disjoint hd,
    proj_prefixRegister hP]

/-- Retain the old seed outside the fresh register and insert a solved seed there. -/
def replaceSeed (P : CL.CLFun F ι ℓ) (k : ℕ) (u x z : ι → F) : ι → F :=
  CL.proj (P.factorOfPrefix k u)ᶜ x + CL.proj (P.factorOfPrefix k u) z

theorem replaceSeed_old {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (u x z : ι → F)
    (hx : (P.truncate k).eval x = u) :
    (P.truncate k).eval (replaceSeed P k u x z) = u := by
  apply truncate_fibre_of_agree hP k u x _ _ hx
  intro i hi
  have hn : i ∉ P.factorOfPrefix k u := by
    intro hs
    exact (mem_sdiff.mp (stageFactor_subset_residual hP k u hs)).2 hi
  simp [replaceSeed, CL.proj_apply, hn]

theorem replaceSeed_next {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (u x z : ι → F)
    (hx : (P.truncate k).eval x = u) :
    (P.truncate (k + 1)).eval (replaceSeed P k u x z) = u + P.mapOfPrefix k u z := by
  rw [truncate_eval_step hP, replaceSeed_old hP k u x z hx]
  congr 1
  rw [← CL.RegLinear.toLinearMap_apply, stageLinear_toLinearMap]
  rw [← stageLinear_toLinearMap P k u]
  change (stageLinear P k u) (replaceSeed P k u x z) = (stageLinear P k u) z
  simp [replaceSeed, CL.RegLinear.apply_proj_compl]

/-- A consistent stage equation extends a legal prefix using only a linear solve. -/
theorem extend_claimed {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x z : ι → F)
    (hx : (P.truncate k).eval x = P.outputPrefix k y)
    (hz : P.mapOfPrefix k (P.outputPrefix k y) z = CL.proj (P.factorOfPrefix k y) y) :
    (P.truncate (k + 1)).eval (replaceSeed P k (P.outputPrefix k y) x z) =
      P.outputPrefix (k + 1) y := by
  rw [replaceSeed_next hP k _ x z hx, hz, outputPrefix_step hP]

open LowDegree.BinaryLinear Cost

/-- The concrete polynomial-time matrix solver applied to the queried stage matrix. -/
def solveStage {n : ℕ} (L : (Fin n → CL.𝔽₂) →ₗ[CL.𝔽₂] (Fin n → CL.𝔽₂))
    (v : Fin n → CL.𝔽₂) : Fin n → CL.𝔽₂ :=
  vectorValue n (matrixSolveProg (unary n, matrixBits (LinearMap.toMatrix' L), vectorBits v))

theorem solveStage_correct {n : ℕ}
    (L : (Fin n → CL.𝔽₂) →ₗ[CL.𝔽₂] (Fin n → CL.𝔽₂))
    (v : Fin n → CL.𝔽₂) (hv : ∃ x, L x = v) : L (solveStage L v) = v := by
  have he : (LinearMap.toMatrix' L).mulVecLin = L := Matrix.toLin'_toMatrix' L
  have hv' : ∃ x, (LinearMap.toMatrix' L).mulVec x = v := by
    simpa only [← Matrix.mulVecLin_apply, he] using hv
  have h := matrixSolveProg_correct (LinearMap.toMatrix' L) v hv'
  simpa only [← Matrix.mulVecLin_apply, he, solveStage] using h

end MIPRE.Introspection.AuxiliaryPrefix
end
