/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.Repetition.TenProofs.QuantumParallelRepetition
import MIPRE.Background.Repetition.Direct

/-!
# Direct parallel repetition for entangled strategies

The uniform exponential parallel repetition theorem for finite-dimensional tensor-product
strategies (blueprint `thm:direct-repetition-q`), in the vocabulary of this repository,
transferred from the vendored module `MIPRE/Background/Repetition/TenProofs/`
(OpenAI, *Ten advances in mathematics and theoretical computer science*, 2026,
Chapter 6): there is a universal `c > 0` such that for every game `G` with nonempty answer
alphabets and `ε = 1 - val*(G) > 0`, and every `n ≥ 1`,
`val*(G^{⊗n}) ≤ exp(-c·n·ε¹³/(ε + log(|A||B|)))`.

A game of this repository is literally a game of the vendored module (same question
weights, same `Bool` predicate), and so is its direct repetition. The values differ in
their strategy classes: `MIPRE.quantumValue` ranges over pure states and projective
measurements on `ℂ^dA ⊗ ℂ^dB`, the vendored `entangledValue` over density matrices and
POVMs on arbitrary finite-dimensional spaces. That they agree (purification and Naimark
dilation) is `quantumValue_eq_entangledValue` (blueprint `lem:povm-value-eq`), the one
statement here whose proof is still open.
-/

namespace MIPRE.Repetition

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

section Bridge

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- A game of this repository as a game of the vendored module. -/
def toTP (G : Game X Y A B) : QuantumParallelRepetition.Game X Y A B where
  questionWeight := G.μ
  weight_nonneg := G.μ_nonneg
  weight_normalized := G.μ_sum_one
  predicate := G.D

/-- The two direct repetitions are the same construction. -/
theorem toTP_repeat (G : Game X Y A B) (n : ℕ) :
    toTP (G.repeat n) = (toTP G).repeat n :=
  rfl

/-! ### From a tensor-product strategy to a strategy of the vendored kind

The embedding direction of `lem:povm-value-eq`: a pure state is a density matrix, a
projective measurement is a POVM, and the two index conventions already agree (both sides
put Alice's and Bob's systems in a Kronecker product over `Fin dA × Fin dB`). -/

/-- A self-adjoint idempotent matrix is positive semidefinite: it equals `Pᴴ * P`. -/
theorem posSemidef_of_selfAdjoint_idem {d : Type} [Fintype d] [DecidableEq d]
    {P : Matrix d d ℂ} (hs : star P = P) (hp : P * P = P) : P.PosSemidef := by
  have hH : Pᴴ = P := by rw [← Matrix.star_eq_conjTranspose]; exact hs
  have hPP : P = Pᴴ * P := by rw [hH]; exact hp.symm
  rw [hPP]
  exact Matrix.posSemidef_conjTranspose_mul_self P

/-- The Born rule for a pure state written as a rank-one density matrix:
`tr(|ψ⟩⟨ψ| E) = ⟨ψ| E |ψ⟩`. -/
theorem trace_vecMulVec_star_mul {d : Type} [Fintype d] (ψ : d → ℂ) (E : Matrix d d ℂ) :
    Matrix.trace (Matrix.vecMulVec ψ (star ψ) * E) = star ψ ⬝ᵥ (E *ᵥ ψ) := by
  rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm]

/-- A tensor-product strategy of this repository, as a strategy of the vendored module:
the state is the rank-one density matrix `|ψ⟩⟨ψ|`, and each projective measurement is a
POVM. -/
noncomputable def ofTensorProductStrategy {G : Game X Y A B}
    (S : TensorProductStrategy G) : QuantumParallelRepetition.Strategy (toTP G) where
  Alice := Fin S.dA
  Bob := Fin S.dB
  alice_fintype := inferInstance
  bob_fintype := inferInstance
  alice_decidableEq := inferInstance
  bob_decidableEq := inferInstance
  state :=
    { matrix := Matrix.vecMulVec S.ψ (star S.ψ)
      positive := Matrix.posSemidef_vecMulVec_self_star S.ψ
      trace_one := by
        rw [Matrix.trace_vecMulVec, dotProduct_comm]
        exact S.ψ_unit }
  aliceMeasurement x :=
    { effect := S.PA.M x
      positive := fun a =>
        posSemidef_of_selfAdjoint_idem (S.PA.selfAdjoint x a) (S.PA.projective x a)
      complete := S.PA.normalized x }
  bobMeasurement y :=
    { effect := S.PB.M y
      positive := fun b =>
        posSemidef_of_selfAdjoint_idem (S.PB.selfAdjoint y b) (S.PB.projective y b)
      complete := S.PB.normalized y }

/-- The embedding preserves the value. -/
theorem ofTensorProductStrategy_winProbability {G : Game X Y A B}
    (S : TensorProductStrategy G) :
    (ofTensorProductStrategy S).winProbability = S.value := by
  classical
  unfold QuantumParallelRepetition.Strategy.winProbability TensorProductStrategy.value
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hprob :
      (ofTensorProductStrategy S).outcomeProbability x y a b =
        (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re := by
    change
      (Matrix.trace
        (Matrix.vecMulVec S.ψ (star S.ψ) * (S.PA.M x a ⊗ₖ S.PB.M y b))).re = _
    rw [trace_vecMulVec_star_mul]
  rw [hprob]
  by_cases h : G.D x y a b = true
  · simp [toTP, h]
  · simp [toTP, h]

/-- **The embedding direction of `lem:povm-value-eq`**: every tensor-product strategy is a
strategy of the vendored kind with the same value, so the quantum value of this repository
is at most the vendored entangled value. -/
theorem quantumValue_le_entangledValue (G : Game X Y A B) :
    quantumValue G ≤ QuantumParallelRepetition.entangledValue (toTP G) := by
  refine Real.iSup_le (fun S => ?_)
    (QuantumParallelRepetition.entangledValue_nonneg (toTP G))
  rw [← ofTensorProductStrategy_winProbability S]
  exact le_csSup (QuantumParallelRepetition.winProbabilities_bddAbove (toTP G))
    ⟨ofTensorProductStrategy S, rfl⟩

/-- **Purification**, the first of the two inputs to the dilation direction. A density
matrix `ρ` on `d` is the reduced state of a unit vector on `d × d`: factoring `ρ = K * Kᴴ`,
the vector `ψ (i, r) = K i r` satisfies `⟨ψ| M ⊗ 1 |ψ⟩ = tr(ρ M)` for every `M`, the second
factor being the reference system. Neither a matrix square root nor the spectral theorem is
needed, only the factorization of a positive semidefinite matrix. (General-purpose: it
belongs in `MIPRE/Mathlib/` once the dilation direction lands.) -/
theorem exists_purification {d : Type} [Fintype d] [DecidableEq d]
    {ρ : Matrix d d ℂ} (hρ : ρ.PosSemidef) (htr : Matrix.trace ρ = 1) :
    ∃ ψ : d × d → ℂ, star ψ ⬝ᵥ ψ = 1 ∧
      ∀ M : Matrix d d ℂ,
        star ψ ⬝ᵥ ((M ⊗ₖ (1 : Matrix d d ℂ)) *ᵥ ψ) = Matrix.trace (ρ * M) := by
  classical
  obtain ⟨K₀, hK₀⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  set K : Matrix d d ℂ := star K₀ with hKdef
  have hρK : ρ = K * star K := by rw [hKdef, star_star]; exact hK₀
  refine ⟨fun p => K p.1 p.2, ?_, fun M => ?_⟩
  · have hn : star (fun p : d × d => K p.1 p.2) ⬝ᵥ (fun p : d × d => K p.1 p.2)
        = Matrix.trace (K * star K) := by
      simp [dotProduct, Matrix.trace, Matrix.diag, Matrix.mul_apply,
        Fintype.sum_prod_type, Pi.star_apply, Matrix.star_apply, mul_comm]
    rw [hn, ← hρK, htr]
  · have hb : star (fun p : d × d => K p.1 p.2) ⬝ᵥ
        ((M ⊗ₖ (1 : Matrix d d ℂ)) *ᵥ fun p : d × d => K p.1 p.2)
        = Matrix.trace (M * (K * star K)) := by
      simp [dotProduct, Matrix.mulVec, Matrix.kroneckerMap_apply, Matrix.one_apply,
        Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
        Pi.star_apply, Matrix.star_apply, Finset.mul_sum, Finset.sum_mul, mul_comm]
      -- the two sides differ only by the order of the inner two summations
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => by ring
    rw [hb, ← hρK, Matrix.trace_mul_comm]

/-- **The dilation direction of `lem:povm-value-eq`**, still open (issue #28): mixed states
and POVMs do not help. Two standard finite-dimensional constructions are needed, neither of
them in Mathlib as of v4.33:

* *Purification.* A density matrix `ρ` on `Alice × Bob` factors as `ρ = star K * K`
  (`CStarAlgebra.nonneg_iff_eq_star_mul_self`), and the vector `ψ (d, r) = K r d` on
  `(Alice × Bob) × R` with `R := Alice × Bob` satisfies `⟨ψ| M ⊗ 1 |ψ⟩ = tr(ρ M)`.
  Reassociating so that the reference system `R` sits on Bob's side keeps the bipartite
  structure, Bob's effects acting as `B ⊗ 1` on `Bob × R`.
* *Naimark dilation of a family.* For each question `x` the POVM `{E^x_a}` dilates to a
  projective measurement, but the dilating isometry depends on `x` while the state may not.
  The fixed-state form is needed: adjoin one ancilla `ℂ^A` in a fixed state, extend each
  isometry `v ↦ ∑_a (√(E^x_a) v) ⊗ |a⟩` to a unitary `U_x` of `ℂ^d ⊗ ℂ^A`, and take
  `P^x_a := U_xᴴ (1 ⊗ |a⟩⟨a|) U_x`.

Both systems are then reindexed by `Fin` types through `Fintype.equivFin`, which changes no
outcome probability. -/
theorem entangledValue_le_quantumValue (G : Game X Y A B) :
    QuantumParallelRepetition.entangledValue (toTP G) ≤ quantumValue G := by
  sorry

/-- The quantum value of this repository (pure states, projective measurements) equals
the entangled value of the vendored module (density matrices, POVMs): purification and
Naimark dilation (blueprint `lem:povm-value-eq`). The embedding direction is proved; the
dilation direction is `entangledValue_le_quantumValue` (issue #28). -/
theorem quantumValue_eq_entangledValue (G : Game X Y A B) :
    quantumValue G = QuantumParallelRepetition.entangledValue (toTP G) :=
  le_antisymm (quantumValue_le_entangledValue G) (entangledValue_le_quantumValue G)

end Bridge

/-- **Uniform exponential parallel repetition for entangled strategies** (blueprint
`thm:direct-repetition-q`; OpenAI 2026, Chapter 6, via the vendored root
`QuantumParallelRepetition.distributionUniformExponential`): there is a universal constant
`c > 0` such that for every game `G` with nonempty answer alphabets and
`ε = 1 - val*(G) > 0`, and every `n ≥ 1`,
`val*(G^{⊗n}) ≤ exp(-c·n·ε¹³/(ε + log(|A||B|)))`. -/
theorem quantumValue_repeat_le :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B), Nonempty A → Nonempty B →
        0 < 1 - quantumValue G →
        ∀ n : ℕ, 0 < n →
          quantumValue (G.repeat n) ≤
            Real.exp
              (-(c * ((1 - quantumValue G) ^ 13 /
                ((1 - quantumValue G) +
                  Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))))
                * (n : ℝ)) := by
  obtain ⟨c, hc, h⟩ := QuantumParallelRepetition.distributionUniformExponential
  refine ⟨c, hc, ?_⟩
  intro X Y A B _ _ _ _ G hA hB hε n hn
  rw [quantumValue_eq_entangledValue, quantumValue_eq_entangledValue, toTP_repeat]
  rw [quantumValue_eq_entangledValue] at hε
  exact h (toTP G) hA hB hε n hn

end MIPRE.Repetition
