/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Expanded
public import MIPRE.Foundations.WeylEPR
public import MIPRE.Foundations.Introspection.RegisterModel

@[expose] public section

/-! # Exactly consistent Pauli readouts with arbitrary ancillary states

In a bipartite model (Phase 4 of `planning/mipco-track.md`) the ancillary state is a model `Ξ`,
and the EPR state on the sampled register is adjoined to it: the register model
`Ξ.reg (Fin n → F)` (`BipartiteModel.reg`), whose state has the norm of `Ξ`'s
(`BipartiteModel.norm_reg_ψ`).
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl
open scoped Kronecker

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Exact consistency survives adjoining any bipartite ancillary state. -/
theorem mirror_expand (ψ : V × W → ℂ) (P : Matrix V V ℂ) (Q : Matrix W W ℂ)
    (h : stateVec ψ P = stateVecB ψ Q) :
    (Ξ.expand ψ).π ((Ξ.expand ψ).πA (smulKron 1 P)) (Ξ.expand ψ).ψ =
      (Ξ.expand ψ).π ((Ξ.expand ψ).πB (smulKron 1 Q)) (Ξ.expand ψ).ψ := by
  have hbase := congrArg WithLp.ofLp h
  change (P ⊗ₖ (1 : Matrix W W ℂ)) *ᵥ ψ = ((1 : Matrix V V ℂ) ⊗ₖ Q) *ᵥ ψ at hbase
  have h1 : (Ξ.expand ψ).πA (smulKron 1 P) =
      (Ξ.expand ψ).πA (smulKron 1 P) * (Ξ.expand ψ).πB (smulKron (1 : ℬ) (1 : Matrix W W ℂ)) := by
    rw [smulKron_one_one, map_one, mul_one]
  have h2 : (Ξ.expand ψ).πB (smulKron 1 Q) =
      (Ξ.expand ψ).πA (smulKron (1 : 𝒜) (1 : Matrix V V ℂ)) * (Ξ.expand ψ).πB (smulKron 1 Q) := by
    rw [smulKron_one_one, map_one, one_mul]
  rw [h1, h2, BipartiteModel.expand_π_smulKron_ψ, BipartiteModel.expand_π_smulKron_ψ, hbase]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {n : ℕ}

/-- A coarse-grained eigenbasis measurement of a symmetric family is symmetric. -/
theorem synOf_transpose {w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ}
    (hw : ∀ a, (w a)ᵀ = w a) {C : Type*} [DecidableEq C] (φ : (Fin n → F) → C) (o : C) :
    (synOf w φ o)ᵀ = synOf w φ o := by
  rw [synOf, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [proj_def, Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [Matrix.transpose_smul, hw a]

/-- The same `X` Pauli on the two EPR halves is an exact mirror, with arbitrary ancillas. -/
theorem reg_wX_mirror (v : Fin n → F) :
    (Ξ.reg (Fin n → F)).xSqNorm (smulKron 1 (wX v)) (smulKron 1 (wX v)) = 0 := by
  have h := Ξ.reg_mirror (wX v)
  rw [wX_transpose] at h
  rw [BipartiteModel.xSqNorm, BipartiteModel.xNorm, StateModel.snorm, Op.snorm, map_sub,
    _root_.sub_apply, h, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- A coarse-grained `Z` readout has the same exact mirror. -/
theorem reg_readout_mirror (L : (Fin n → F) →ₗ[F] (Fin n → F)) (y : Fin n → F) :
    (Ξ.reg (Fin n → F)).π ((Ξ.reg (Fin n → F)).πA (smulKron 1 (synOf wZ L y)))
        (Ξ.reg (Fin n → F)).ψ =
      (Ξ.reg (Fin n → F)).π ((Ξ.reg (Fin n → F)).πB (smulKron 1 (synOf wZ L y)))
        (Ξ.reg (Fin n → F)).ψ := by
  have h := Ξ.reg_mirror (synOf wZ L y)
  rwa [synOf_transpose wZ_transpose] at h

end MIPRE.Introspection

end

end
