/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.AncillaModel

@[expose] public section

/-!
# Matrices of scalars on a register, and the contraction against a vector

A finite register `ι` adjoined to a Hilbert space `H` is the `ℓ²` sum
`OperatorMatrix.Ampl ι H` (`H ⊗ ℂ^ι`, the register the outer index). A matrix `R` of scalars on the
register acts on it as `R ⊗ 1_H`: `regAct R`, a unital `⋆`-algebra homomorphism from
`Matrix ι ι ℂ`, so that sums, products and adjoints of register matrices are computed on the
register alone. Two computations are all the analyses need of it.

* **On a product vector** `e ⊗ ξ` (`WithLp.toLp 2 fun i => e i • ξ`) it acts on the register's
  factor alone: `regAct R (e ⊗ ξ) = (R e) ⊗ ξ` (`regAct_toLp_smul`).
* **The rank-one matrix `|e⟩⟨f|` contracts**: it sends `θ` to `e ⊗ (∑_j f_j θ_j)`
  (`regAct_vecMulVec`). At the maximally entangled vector of a pair of registers this is the EPR
  contraction of the Pauli basis test's swap isometry: the range of `|EPR⟩⟨EPR| ⊗ 1` is the set of
  products `EPR ⊗ aux`, and the contraction is the `aux`.

And one link with the ancilla extension of a bipartite model
(`MIPRE/Foundations/AncillaModel.lean`): in `M.expand e`, whose space is `Ampl (α × β) M.H`, a
matrix of scalars `P` on the first player's register times one `Q` on the second's acts as the
register matrix `P ⊗ Q` (`BipartiteModel.expand_π_smulKron_one_mul`), whatever the model. So a
quadratic form of such a product on any vector of the extension is a quadratic form of `regAct`.
-/

noncomputable section

namespace MIPRE

open scoped InnerProductSpace Kronecker
open Matrix

namespace OperatorMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The matrices of scalars acting on the register** of `ℂ^ι ⊗ H`, `R ↦ R ⊗ 1_H`, as a unital
`⋆`-algebra homomorphism: the entrywise inclusion of the scalars, followed by the action of
operator matrices. -/
def regActHom : Matrix ι ι ℂ →⋆ₐ[ℂ] (Ampl ι H →L[ℂ] Ampl ι H) :=
  toCLMStarAlgHom.comp (mapMatrixStarAlgHom (StarAlgHom.ofId ℂ (H →L[ℂ] H)))

/-- **A matrix of scalars acting on the register** of `ℂ^ι ⊗ H`: `R ⊗ 1_H`. -/
def regAct (R : Matrix ι ι ℂ) : Ampl ι H →L[ℂ] Ampl ι H :=
  regActHom (ι := ι) (H := H) R

theorem regActHom_apply (R : Matrix ι ι ℂ) : regActHom (H := H) R = regAct R :=
  rfl

/-- `regAct R` is the operator matrix with the entries `R i j • 1`. -/
theorem regAct_eq_toCLM (R : Matrix ι ι ℂ) :
    regAct (H := H) R = toCLM (R.map fun r => r • (1 : H →L[ℂ] H)) := by
  show toCLM (R.map (algebraMap ℂ (H →L[ℂ] H))) = _
  exact congrArg toCLM (Matrix.ext fun i j => Algebra.algebraMap_eq_smul_one (R i j))

theorem regAct_mul (R S : Matrix ι ι ℂ) : regAct (H := H) (R * S) = regAct R * regAct S :=
  map_mul (regActHom (ι := ι) (H := H)) R S

theorem regAct_one : regAct (H := H) (1 : Matrix ι ι ℂ) = 1 :=
  map_one (regActHom (ι := ι) (H := H))

theorem regAct_conjTranspose (R : Matrix ι ι ℂ) : regAct (H := H) Rᴴ = star (regAct R) :=
  map_star (regActHom (ι := ι) (H := H)) R

theorem regAct_add (R S : Matrix ι ι ℂ) : regAct (H := H) (R + S) = regAct R + regAct S :=
  map_add (regActHom (ι := ι) (H := H)) R S

theorem regAct_smul (c : ℂ) (R : Matrix ι ι ℂ) : regAct (H := H) (c • R) = c • regAct R :=
  map_smul (regActHom (ι := ι) (H := H)) c R

theorem regAct_sum {κ : Type*} (s : Finset κ) (R : κ → Matrix ι ι ℂ) :
    regAct (H := H) (∑ k ∈ s, R k) = ∑ k ∈ s, regAct (R k) :=
  map_sum (regActHom (ι := ι) (H := H)) R s

/-- The register action of a self-adjoint idempotent is an orthogonal projection. -/
theorem isStarProjection_regAct {P : Matrix ι ι ℂ} (hsa : Pᴴ = P) (hid : P * P = P) :
    IsStarProjection (regAct (H := H) P) :=
  ⟨by rw [IsIdempotentElem, ← regAct_mul, hid], by
    rw [IsSelfAdjoint, ← regAct_conjTranspose, hsa]⟩

/-- The components of `regAct R θ`: `(R θ)_i = ∑_j R_{ij} θ_j`. -/
theorem regAct_apply (R : Matrix ι ι ℂ) (θ : Ampl ι H) (i : ι) :
    regAct R θ i = ∑ j, R i j • θ j := by
  rw [regAct_eq_toCLM, toCLM_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_apply, _root_.smul_apply, one_apply_eq_self]

/-- **On a product vector a register matrix acts on the register's factor alone**:
`(R ⊗ 1)(e ⊗ ξ) = (R e) ⊗ ξ`. -/
theorem regAct_toLp_smul (R : Matrix ι ι ℂ) (e : ι → ℂ) (ξ : H) :
    regAct R (WithLp.toLp 2 fun i => e i • ξ : Ampl ι H)
      = WithLp.toLp 2 fun i => (R *ᵥ e) i • ξ := by
  ext i
  rw [regAct_apply, PiLp.toLp_apply, mulVec, dotProduct, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PiLp.toLp_apply, smul_smul]

/-- **The contraction against a vector**: the rank-one register matrix `|e⟩⟨f|` sends `θ` to the
product vector `e ⊗ ∑_j f_j θ_j`. -/
theorem regAct_vecMulVec (e f : ι → ℂ) (θ : Ampl ι H) :
    regAct (vecMulVec e f) θ = WithLp.toLp 2 fun i => e i • ∑ j, f j • θ j := by
  ext i
  rw [regAct_apply, PiLp.toLp_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [vecMulVec_apply, smul_smul]

omit [DecidableEq ι] [CompleteSpace H] in
/-- **The norm of a product vector is the product of the norms.** -/
theorem norm_toLp_smul (e : ι → ℂ) (ξ : H) :
    ‖(WithLp.toLp 2 fun i => e i • ξ : Ampl ι H)‖ = ‖evec e‖ * ‖ξ‖ := by
  have h : ‖(WithLp.toLp 2 fun i => e i • ξ : Ampl ι H)‖ ^ 2 = (‖evec e‖ * ‖ξ‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, evec, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.toLp_apply, PiLp.toLp_apply, norm_smul, mul_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1 h

end OperatorMatrix

open OperatorMatrix

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α × β → ℂ)

/-- **A matrix of scalars on the first player's register of an extension** acts as the register
matrix `P ⊗ 1`. -/
theorem expand_π_πA_smulKron_one (P : Matrix α α ℂ) :
    (M.expand e).π ((M.expand e).πA (smulKron 1 P)) = regAct (P ⊗ₖ (1 : Matrix β β ℂ)) := by
  rw [expand_πA_smulKron, map_one, expand_π_apply, regAct_eq_toCLM]
  congr 1
  ext p q
  rw [map_apply, liftLeft_apply, map_apply, kronecker_apply, one_apply]
  by_cases h : p.2 = q.2
  · rw [ite_eq_left h, ite_eq_left h, smulKron_apply, map_smul, map_one, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, map_zero, mul_zero, zero_smul]

/-- **A matrix of scalars on the second player's register of an extension** acts as the register
matrix `1 ⊗ Q`. -/
theorem expand_π_πB_smulKron_one (Q : Matrix β β ℂ) :
    (M.expand e).π ((M.expand e).πB (smulKron 1 Q)) = regAct ((1 : Matrix α α ℂ) ⊗ₖ Q) := by
  rw [expand_πB_smulKron, map_one, expand_π_apply, regAct_eq_toCLM]
  congr 1
  ext p q
  rw [map_apply, liftRight_apply, map_apply, kronecker_apply, one_apply]
  by_cases h : p.1 = q.1
  · rw [ite_eq_left h, ite_eq_left h, smulKron_apply, map_smul, map_one, one_mul]
  · rw [ite_eq_right h, ite_eq_right h, map_zero, zero_mul, zero_smul]

/-- **A product of matrices of scalars on the two players' registers of an extension** acts as
the register matrix `P ⊗ Q`. -/
theorem expand_π_smulKron_one_mul (P : Matrix α α ℂ) (Q : Matrix β β ℂ) :
    (M.expand e).π ((M.expand e).πA (smulKron 1 P) * (M.expand e).πB (smulKron 1 Q))
      = regAct (P ⊗ₖ Q) := by
  rw [expand_πA_smulKron, expand_πB_smulKron, map_one, map_one, expand_π_apply,
    regAct_eq_toCLM]
  congr 1
  ext p q
  rw [map_apply, liftLeft_mul_liftRight, smulKron_apply, smulKron_apply, smul_mul_smul_comm,
    mul_one, map_apply, kronecker_apply, map_smul, map_one]

end BipartiteModel

end MIPRE

end
