/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.Repetition.TenProofs.QuantumParallelRepetition
import MIPRE.Background.Repetition.Direct
import MIPRE.Foundations.Dilation

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

The Naimark dilation itself, and the Born-rule transport lemmas that go with it, used to be
written out in this file; they now live in `MIPRE/Foundations/Dilation.lean`. They are generic
matrix mathematics that reach none of the vendored trees, and a second consumer appeared
(blueprint `lem:ms-direct-anticomm`, in `MIPRE/LCS/`, which may not import
`MIPRE/Background/`) for which being behind this file's 71k-line vendored import made them
unusable.
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

/-- A tensor-product strategy's value is at most one, because it is the winning probability
of the vendored strategy it embeds to. -/
theorem value_le_one {G : Game X Y A B} (S : TensorProductStrategy G) : S.value ≤ 1 := by
  rw [← ofTensorProductStrategy_winProbability S]
  exact (ofTensorProductStrategy S).winProbability_le_one

/-- A tensor-product strategy's value is nonnegative, for the same reason. -/
theorem value_nonneg {G : Game X Y A B} (S : TensorProductStrategy G) : 0 ≤ S.value := by
  rw [← ofTensorProductStrategy_winProbability S]
  exact (ofTensorProductStrategy S).winProbability_nonneg

/-- The values of tensor-product strategies are bounded above, so `val*` is attained as a
genuine supremum and `le_ciSup` applies to it. -/
theorem bddAbove_range_value (G : Game X Y A B) :
    BddAbove (Set.range fun S : TensorProductStrategy G => S.value) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨S, rfl⟩
  exact value_le_one S

/-- `val*(G) ≥ 0`, including when no tensor-product strategy exists (then it is `0`). -/
theorem quantumValue_nonneg (G : Game X Y A B) : 0 ≤ quantumValue G :=
  Real.iSup_nonneg fun S => value_nonneg S

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

/-! ### From arbitrary finite local spaces to `Fin d` -/

/-- A pure state together with two projective families on *arbitrary* finite local spaces
already bounds `val*(G)` from below: reindexing the two spaces by `Fintype.equivFin` turns
them into a `TensorProductStrategy`, and a bijective reindexing changes no outcome
probability. This is what lets the dilation steps above work with the natural index types
(`Alice × A`, `(Bob × R) × B`) and only convert to `Fin d` at the end. -/
theorem projective_value_le_quantumValue {HA HB : Type} [Fintype HA] [DecidableEq HA]
    [Fintype HB] [DecidableEq HB] {G : Game X Y A B} (ψ : HA × HB → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1)
    (PA : ProjectiveMeasurement X A (Matrix HA HA ℂ))
    (PB : ProjectiveMeasurement Y B (Matrix HB HB ℂ)) :
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
        (star ψ ⬝ᵥ ((PA.M x a ⊗ₖ PB.M y b) *ᵥ ψ)).re ≤ quantumValue G := by
  classical
  set fA : Fin (Fintype.card HA) ≃ HA := (Fintype.equivFin HA).symm with hfA
  set fB : Fin (Fintype.card HB) ≃ HB := (Fintype.equivFin HB).symm with hfB
  set e : (Fin (Fintype.card HA) × Fin (Fintype.card HB)) ≃ (HA × HB) :=
    fA.prodCongr fB with he
  have hsub : ∀ (M : Matrix HA HA ℂ) (N : Matrix HB HB ℂ),
      (M.submatrix fA fA) ⊗ₖ (N.submatrix fB fB) = (M ⊗ₖ N).submatrix e e := by
    intro M N
    ext p q
    rfl
  have hAself : ∀ x a, star ((PA.M x a).submatrix fA fA) = (PA.M x a).submatrix fA fA := by
    intro x a
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      ← Matrix.star_eq_conjTranspose, PA.selfAdjoint]
  have hAproj : ∀ x a, (PA.M x a).submatrix fA fA * (PA.M x a).submatrix fA fA
      = (PA.M x a).submatrix fA fA := by
    intro x a
    rw [Matrix.submatrix_mul_equiv, PA.projective]
  have hAnorm : ∀ x, ∑ a, (PA.M x a).submatrix fA fA = 1 := by
    intro x
    have h : ∑ a : A, (PA.M x a).submatrix fA fA = (∑ a : A, PA.M x a).submatrix fA fA := by
      ext i j
      simp [Matrix.sum_apply]
    rw [h, PA.normalized, Matrix.submatrix_one_equiv]
  have hBself : ∀ y b, star ((PB.M y b).submatrix fB fB) = (PB.M y b).submatrix fB fB := by
    intro y b
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      ← Matrix.star_eq_conjTranspose, PB.selfAdjoint]
  have hBproj : ∀ y b, (PB.M y b).submatrix fB fB * (PB.M y b).submatrix fB fB
      = (PB.M y b).submatrix fB fB := by
    intro y b
    rw [Matrix.submatrix_mul_equiv, PB.projective]
  have hBnorm : ∀ y, ∑ b, (PB.M y b).submatrix fB fB = 1 := by
    intro y
    have h : ∑ b : B, (PB.M y b).submatrix fB fB = (∑ b : B, PB.M y b).submatrix fB fB := by
      ext i j
      simp [Matrix.sum_apply]
    rw [h, PB.normalized, Matrix.submatrix_one_equiv]
  obtain ⟨S, hS⟩ : ∃ S : TensorProductStrategy G, S.value =
      ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
        (star ψ ⬝ᵥ ((PA.M x a ⊗ₖ PB.M y b) *ᵥ ψ)).re := by
    refine ⟨{ dA := Fintype.card HA
              dB := Fintype.card HB
              ψ := ψ ∘ e
              ψ_unit := by rw [dotProduct_comp_equiv, hψ]
              PA := { M := fun x a => (PA.M x a).submatrix fA fA
                      selfAdjoint := hAself
                      projective := hAproj
                      normalized := hAnorm }
              PB := { M := fun y b => (PB.M y b).submatrix fB fB
                      selfAdjoint := hBself
                      projective := hBproj
                      normalized := hBnorm } }, ?_⟩
    unfold TensorProductStrategy.value
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hq : star (ψ ∘ e) ⬝ᵥ
        ((((PA.M x a).submatrix fA fA) ⊗ₖ ((PB.M y b).submatrix fB fB)) *ᵥ (ψ ∘ e))
          = star ψ ⬝ᵥ ((PA.M x a ⊗ₖ PB.M y b) *ᵥ ψ) := by
      rw [hsub, dotProduct_mulVec_submatrix]
    rw [hq]
  rw [← hS]
  exact le_ciSup (bddAbove_range_value G) S

/-- Purification with the reference system placed on Bob's side. A density matrix `ρ` on
`dA × dB` is the reduced state of a pure state on `dA × (dB × R)` with `R = dA × dB`, against
which Alice's operators act as `E ⊗ 1` and Bob's as `F ⊗ 1_R`; so the purification keeps the
bipartite structure, at the cost of enlarging Bob's space. -/
theorem exists_purification_bipartite {dA dB : Type} [Fintype dA] [DecidableEq dA]
    [Fintype dB] [DecidableEq dB] {ρ : Matrix (dA × dB) (dA × dB) ℂ} (hρ : ρ.PosSemidef)
    (htr : Matrix.trace ρ = 1) :
    ∃ ψ : dA × (dB × (dA × dB)) → ℂ, star ψ ⬝ᵥ ψ = 1 ∧
      ∀ (E : Matrix dA dA ℂ) (F : Matrix dB dB ℂ),
        star ψ ⬝ᵥ ((E ⊗ₖ (F ⊗ₖ (1 : Matrix (dA × dB) (dA × dB) ℂ))) *ᵥ ψ)
          = Matrix.trace (ρ * (E ⊗ₖ F)) := by
  classical
  obtain ⟨ψ₀, hunit, hborn⟩ := exists_purification hρ htr
  refine ⟨ψ₀ ∘ (Equiv.prodAssoc dA dB (dA × dB)).symm, ?_, ?_⟩
  · rw [dotProduct_comp_equiv, hunit]
  · intro E F
    have h : E ⊗ₖ (F ⊗ₖ (1 : Matrix (dA × dB) (dA × dB) ℂ))
        = ((E ⊗ₖ F) ⊗ₖ (1 : Matrix (dA × dB) (dA × dB) ℂ)).submatrix
            (Equiv.prodAssoc dA dB (dA × dB)).symm
            (Equiv.prodAssoc dA dB (dA × dB)).symm := by
      rw [← Matrix.kronecker_assoc, Matrix.reindex_apply]
    rw [h, dotProduct_mulVec_submatrix, hborn]

/-- **The dilation direction of `lem:povm-value-eq`**: mixed states and POVMs do not help.
Given a vendored strategy — a density matrix `ρ` on `Alice × Bob` and POVMs `{E^x_a}`,
`{F^y_b}` — purify `ρ` into a pure state on `Alice × (Bob × R)`, dilate each POVM family to a
projective family on one extra register (`exists_projective_dilation`, whose compressing
isometry is the same for every question), and reindex the two local spaces to `Fin` types
(`projective_value_le_quantumValue`). No outcome probability changes along the way, so the
winning probability is the value of a tensor-product strategy. -/
theorem entangledValue_le_quantumValue (G : Game X Y A B) :
    QuantumParallelRepetition.entangledValue (toTP G) ≤ quantumValue G := by
  classical
  unfold QuantumParallelRepetition.entangledValue
  refine Real.sSup_le ?_ (quantumValue_nonneg G)
  rintro r ⟨S, rfl⟩
  -- the question distribution is a probability distribution, so there is a question to ask
  have hX : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    have h := G.μ_sum_one
    simp at h
  obtain ⟨x₀⟩ := hX
  have hY : Nonempty Y := by
    by_contra hY
    rw [not_nonempty_iff] at hY
    have h := G.μ_sum_one
    simp at h
  obtain ⟨y₀⟩ := hY
  -- a state of trace one lives on a nonempty space, and then a POVM has a nonempty outcome set
  have hAB : Nonempty (S.Alice × S.Bob) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have htr := S.state.trace_one
    simp [Matrix.trace] at htr
  have hA : Nonempty A := by
    by_contra hA
    rw [not_nonempty_iff] at hA
    have hc := (S.aliceMeasurement x₀).complete
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hc
    obtain ⟨i, _⟩ := hAB
    have h := congrFun (congrFun hc i) i
    simp at h
  have hB : Nonempty B := by
    by_contra hB
    rw [not_nonempty_iff] at hB
    have hc := (S.bobMeasurement y₀).complete
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hc
    obtain ⟨_, j⟩ := hAB
    have h := congrFun (congrFun hc j) j
    simp at h
  obtain ⟨a₀⟩ := hA
  obtain ⟨b₀⟩ := hB
  -- purify, keeping the bipartite structure
  obtain ⟨ψ, hψunit, hψborn⟩ :=
    exists_purification_bipartite S.state.positive S.state.trace_one
  -- Bob's POVMs, acting on his enlarged space `Bob × R`
  have hFpos : ∀ (y : Y) (b : B),
      (((S.bobMeasurement y).effect b) ⊗ₖ
        (1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ)).PosSemidef :=
    fun y b => ((S.bobMeasurement y).positive b).kronecker Matrix.PosSemidef.one
  have hFsum : ∀ y : Y, ∑ b : B, ((S.bobMeasurement y).effect b ⊗ₖ
      (1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ)) = 1 := by
    intro y
    have h : ∑ b : B, ((S.bobMeasurement y).effect b ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ))
        = (∑ b : B, (S.bobMeasurement y).effect b) ⊗ₖ
          (1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ) := by
      ext p q
      simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
    rw [h, (S.bobMeasurement y).complete, Matrix.one_kronecker_one]
  -- dilate both POVM families to projective families
  obtain ⟨PA, hPAself, hPAproj, hPAnorm, hPAcomp⟩ :=
    exists_projective_dilation a₀ (fun x a => (S.aliceMeasurement x).positive a)
      (fun x => (S.aliceMeasurement x).complete)
  obtain ⟨PB, hPBself, hPBproj, hPBnorm, hPBcomp⟩ :=
    exists_projective_dilation b₀ hFpos hFsum
  -- the shared state, with both ancillas in their fixed states
  obtain ⟨ψ₂, hψ₂⟩ :
      ∃ v : (S.Alice × A) × ((S.Bob × (S.Alice × S.Bob)) × B) → ℂ,
        v = (ancillaEmbed S.Alice a₀ ⊗ₖ ancillaEmbed (S.Bob × (S.Alice × S.Bob)) b₀) *ᵥ ψ :=
    ⟨_, rfl⟩
  have hWiso : (ancillaEmbed S.Alice a₀ ⊗ₖ
      ancillaEmbed (S.Bob × (S.Alice × S.Bob)) b₀)ᴴ *
      (ancillaEmbed S.Alice a₀ ⊗ₖ ancillaEmbed (S.Bob × (S.Alice × S.Bob)) b₀) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ancillaEmbed_isometry,
      ancillaEmbed_isometry, Matrix.one_kronecker_one]
  have hψ₂unit : star ψ₂ ⬝ᵥ ψ₂ = 1 := by
    rw [hψ₂]
    have h := dotProduct_mulVec_conj
      (ancillaEmbed S.Alice a₀ ⊗ₖ ancillaEmbed (S.Bob × (S.Alice × S.Bob)) b₀) 1 ψ
    rw [Matrix.one_mulVec] at h
    rw [h, Matrix.one_mul, hWiso, Matrix.one_mulVec, hψunit]
  -- the Born probabilities are unchanged
  have hborn2 : ∀ (x : X) (y : Y) (a : A) (b : B),
      star ψ₂ ⬝ᵥ ((PA x a ⊗ₖ PB y b) *ᵥ ψ₂)
        = Matrix.trace (S.state.matrix *
            ((S.aliceMeasurement x).effect a ⊗ₖ (S.bobMeasurement y).effect b)) := by
    intro x y a b
    rw [hψ₂, dotProduct_mulVec_conj]
    have hc : (ancillaEmbed S.Alice a₀ ⊗ₖ ancillaEmbed (S.Bob × (S.Alice × S.Bob)) b₀)ᴴ *
          ((PA x a ⊗ₖ PB y b) *
            (ancillaEmbed S.Alice a₀ ⊗ₖ ancillaEmbed (S.Bob × (S.Alice × S.Bob)) b₀))
        = (S.aliceMeasurement x).effect a ⊗ₖ ((S.bobMeasurement y).effect b ⊗ₖ
            (1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ)) := by
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        hPAcomp, hPBcomp]
    rw [hc, hψborn]
  -- assemble: the winning probability is the value of a pure projective strategy
  have hval : QuantumParallelRepetition.Strategy.winProbability S
      = ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
          (star ψ₂ ⬝ᵥ ((PA x a ⊗ₖ PB y b) *ᵥ ψ₂)).re := by
    unfold QuantumParallelRepetition.Strategy.winProbability
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hprob : (star ψ₂ ⬝ᵥ ((PA x a ⊗ₖ PB y b) *ᵥ ψ₂)).re
        = S.outcomeProbability x y a b := by
      rw [hborn2 x y a b]
      rfl
    rw [hprob]
    by_cases h : G.D x y a b = true
    · simp [toTP, h]
    · simp [toTP, h]
  rw [hval]
  exact projective_value_le_quantumValue ψ₂ hψ₂unit
    { M := PA, selfAdjoint := hPAself, projective := hPAproj, normalized := hPAnorm }
    { M := PB, selfAdjoint := hPBself, projective := hPBproj, normalized := hPBnorm }

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
