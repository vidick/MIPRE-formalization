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

/-! ### Naimark dilation of a question-indexed family

The second input to the dilation direction. A POVM dilates to an isometry into one extra
register (`exists_isometry_of_povm`); extending that isometry to a unitary turns it into a
*projective* measurement on the larger space whose expectations against a **fixed** state are
the POVM's. The extension is what makes the construction work for a whole question-indexed
family at once: the isometry depends on the question, the state must not. -/

/-- The ancilla projection `1 ⊗ |a⟩⟨a|` on `d × A`: the identity on the first factor and the
rank-one projection onto `a` on the second. It is a diagonal matrix, and saying so is what
makes the dilation computations below elementary. -/
def ancillaProj (d : Type) [DecidableEq d] {A : Type} [DecidableEq A] (a : A) :
    Matrix (d × A) (d × A) ℂ :=
  Matrix.diagonal fun p => if p.2 = a then 1 else 0

theorem ancillaProj_conjTranspose {d A : Type} [DecidableEq d] [DecidableEq A] (a : A) :
    (ancillaProj d a)ᴴ = ancillaProj d a := by
  rw [ancillaProj, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem ancillaProj_mul_self {d A : Type} [Fintype d] [DecidableEq d] [Fintype A]
    [DecidableEq A] (a : A) :
    ancillaProj d a * ancillaProj d a = ancillaProj d a := by
  rw [ancillaProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> simp

theorem sum_ancillaProj {d A : Type} [DecidableEq d] [Fintype A] [DecidableEq A] :
    ∑ a : A, ancillaProj d a = (1 : Matrix (d × A) (d × A) ℂ) := by
  ext p q
  rw [Matrix.sum_apply]
  by_cases h : p = q
  · subst h
    simp [ancillaProj, Matrix.one_apply_eq]
  · simp [ancillaProj, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

/-- Every POVM dilates to an isometry into one extra register: there is `V` with `Vᴴ V = 1`
and `Vᴴ (1 ⊗ |a⟩⟨a|) V = E a`. Only the factorization of a positive semidefinite matrix is
used, not a square root: with `E a = (K a)ᴴ (K a)`, the isometry is
`V : v ↦ ∑ a, (K a v) ⊗ |a⟩`. -/
theorem exists_isometry_of_povm {d A : Type} [Fintype d] [DecidableEq d]
    [Fintype A] [DecidableEq A] {E : A → Matrix d d ℂ}
    (hpos : ∀ a, (E a).PosSemidef) (hsum : ∑ a, E a = 1) :
    ∃ V : Matrix (d × A) d ℂ, Vᴴ * V = 1 ∧
      ∀ a : A, Vᴴ * (ancillaProj d a * V) = E a := by
  classical
  choose K hK using fun a : A => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hpos a).nonneg
  have hKE : ∀ (a : A) (j k : d),
      E a j k = ∑ i : d, (starRingEnd ℂ) (K a i j) * K a i k := by
    intro a j k
    rw [hK a]
    simp [Matrix.mul_apply, Matrix.star_apply]
  set V : Matrix (d × A) d ℂ := Matrix.of fun p j => K p.2 p.1 j with hVdef
  refine ⟨V, ?_, ?_⟩
  · ext j k
    have h1 : (Vᴴ * V) j k = ∑ i : d, ∑ a : A, (starRingEnd ℂ) (K a i j) * K a i k := by
      simp [hVdef, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    rw [h1, Finset.sum_comm]
    have h2 : ∑ a : A, ∑ i : d, (starRingEnd ℂ) (K a i j) * K a i k = ∑ a : A, E a j k :=
      Finset.sum_congr rfl fun a _ => (hKE a j k).symm
    rw [h2, ← Matrix.sum_apply, hsum]
  · intro a
    ext j k
    have hAV : ∀ (p : d × A) (m : d),
        (ancillaProj d a * V) p m = if p.2 = a then K p.2 p.1 m else 0 := by
      intro p m
      rw [ancillaProj, Matrix.diagonal_mul, hVdef]
      split_ifs <;> simp
    have h3 : (Vᴴ * (ancillaProj d a * V)) j k
        = ∑ i : d, (starRingEnd ℂ) (K a i j) * K a i k := by
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp only [hAV, Matrix.conjTranspose_apply, mul_ite, mul_zero]
      simp [hVdef]
    rw [h3, ← hKE a j k]

/-- The isometry `d → d × A` that pads a vector with the fixed ancilla state `|a₀⟩`. -/
def ancillaEmbed (d : Type) [DecidableEq d] {A : Type} [DecidableEq A] (a₀ : A) :
    Matrix (d × A) d ℂ :=
  Matrix.of fun p j => if p = (j, a₀) then 1 else 0

theorem ancillaEmbed_isometry {d A : Type} [Fintype d] [DecidableEq d]
    [Fintype A] [DecidableEq A] (a₀ : A) :
    (ancillaEmbed d a₀)ᴴ * ancillaEmbed d a₀ = (1 : Matrix d d ℂ) := by
  ext j k
  rw [Matrix.mul_apply, Finset.sum_eq_single (k, a₀)]
  · by_cases h : j = k
    · subst h
      simp [ancillaEmbed, Matrix.one_apply]
    · simp [ancillaEmbed, Matrix.one_apply_ne h, Prod.mk.injEq, Ne.symm h]
  · intro p _ hp
    simp [ancillaEmbed, hp]
  · simp

/-- Any isometry into `d × A` extends to a unitary of `d × A` agreeing with it on the
`a₀`-slice: `U · (ancillaEmbed d a₀) = V`. This is the completion of an orthonormal family to
an orthonormal basis, imported from Mathlib as
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`; it is the step that lets a whole
question-indexed family of POVMs be dilated against one fixed state. -/
theorem exists_unitary_extending {d A : Type} [Fintype d] [DecidableEq d]
    [Fintype A] [DecidableEq A] (a₀ : A) {V : Matrix (d × A) d ℂ}
    (hV : Vᴴ * V = (1 : Matrix d d ℂ)) :
    ∃ U : Matrix (d × A) (d × A) ℂ, Uᴴ * U = 1 ∧ U * ancillaEmbed d a₀ = V := by
  classical
  set w : (d × A) → EuclideanSpace ℂ (d × A) :=
    fun p => WithLp.toLp 2 (fun q => V q p.1) with hw
  have hinner : ∀ p q : d × A, inner ℂ (w p) (w q) = (Vᴴ * V) p.1 q.1 := by
    intro p q
    rw [hw, EuclideanSpace.inner_toLp_toLp, Matrix.mul_apply]
    simp [dotProduct, Matrix.conjTranspose_apply, mul_comm]
  have hortho : Orthonormal ℂ (Set.domRestrict {p : d × A | p.2 = a₀} w) := by
    rw [orthonormal_iff_ite]
    intro p q
    have hpq : inner ℂ (w (p : d × A)) (w (q : d × A))
        = (1 : Matrix d d ℂ) (p : d × A).1 (q : d × A).1 := by
      rw [hinner, hV]
    have hiff : (p = q) ↔ ((p : d × A).1 = (q : d × A).1) := by
      refine ⟨fun h => by rw [h], fun h => Subtype.ext (Prod.ext h ?_)⟩
      have hp : (p : d × A).2 = a₀ := p.property
      have hq : (q : d × A).2 = a₀ := q.property
      rw [hp, hq]
    show inner ℂ (w (p : d × A)) (w (q : d × A)) = _
    rw [hpq, Matrix.one_apply]
    by_cases h : p = q
    · simp [h, hiff.mp h]
    · have h' : ¬((p : d × A).1 = (q : d × A).1) := fun hc => h (hiff.mpr hc)
      rw [if_neg h, if_neg h']
  obtain ⟨b, hb⟩ := hortho.exists_orthonormalBasis_extension_of_card_eq finrank_euclideanSpace
  have hbb : ∀ p p' : d × A,
      ∑ q : d × A, star ((b p : EuclideanSpace ℂ (d × A)) q) * (b p' q)
        = if p = p' then (1 : ℂ) else 0 := by
    intro p p'
    rw [← orthonormal_iff_ite.mp b.orthonormal p p', EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, mul_comm]
  refine ⟨Matrix.of fun q p => (b p : EuclideanSpace ℂ (d × A)) q, ?_, ?_⟩
  · ext p p'
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [hbb, Matrix.one_apply]
  · ext q j
    rw [Matrix.mul_apply, Finset.sum_eq_single (j, a₀)]
    · have hj : b (j, a₀) = w (j, a₀) := hb _ rfl
      simp [ancillaEmbed, hj, hw]
    · intro p _ hp
      simp [ancillaEmbed, hp]
    · simp

/-- **Naimark dilation of a question-indexed POVM family against a fixed state.** A family of
POVMs `{E^x_a}` on `d` is the compression, by the *single* question-independent isometry
`ancillaEmbed d a₀`, of a family of genuinely *projective* measurements `{P^x_a}` on `d × A`.
That the compression does not depend on the question is what lets the dilation be applied to a
fixed shared state, and it is why the unitary extension of the previous step was needed. -/
theorem exists_projective_dilation {d A X : Type} [Fintype d] [DecidableEq d]
    [Fintype A] [DecidableEq A] (a₀ : A) {E : X → A → Matrix d d ℂ}
    (hpos : ∀ x a, (E x a).PosSemidef) (hsum : ∀ x, ∑ a, E x a = 1) :
    ∃ P : X → A → Matrix (d × A) (d × A) ℂ,
      (∀ x a, star (P x a) = P x a) ∧
      (∀ x a, P x a * P x a = P x a) ∧
      (∀ x, ∑ a, P x a = 1) ∧
      (∀ x a, (ancillaEmbed d a₀)ᴴ * (P x a * ancillaEmbed d a₀) = E x a) := by
  classical
  choose V hViso hVE using fun x : X => exists_isometry_of_povm (hpos x) (hsum x)
  choose U hUiso hUV using fun x : X => exists_unitary_extending a₀ (hViso x)
  have hUU : ∀ x, U x * (U x)ᴴ = 1 := fun x => mul_eq_one_comm.mp (hUiso x)
  refine ⟨fun x a => (U x)ᴴ * (ancillaProj d a * U x), ?_, ?_, ?_, ?_⟩
  · intro x a
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, ancillaProj_conjTranspose, Matrix.mul_assoc]
  · intro x a
    have h : (U x)ᴴ * (ancillaProj d a * U x) * ((U x)ᴴ * (ancillaProj d a * U x))
        = (U x)ᴴ * (ancillaProj d a * (U x * (U x)ᴴ * (ancillaProj d a * U x))) := by
      simp only [Matrix.mul_assoc]
    rw [h, hUU, Matrix.one_mul, ← Matrix.mul_assoc (ancillaProj d a) (ancillaProj d a) (U x),
      ancillaProj_mul_self]
  · intro x
    have h : ∑ a : A, (U x)ᴴ * (ancillaProj d a * U x)
        = (U x)ᴴ * ((∑ a : A, ancillaProj d a) * U x) := by
      rw [Finset.sum_mul, Finset.mul_sum]
    rw [h, sum_ancillaProj, Matrix.one_mul, hUiso]
  · intro x a
    have h : (ancillaEmbed d a₀)ᴴ * ((U x)ᴴ * (ancillaProj d a * U x) * ancillaEmbed d a₀)
        = (U x * ancillaEmbed d a₀)ᴴ * (ancillaProj d a * (U x * ancillaEmbed d a₀)) := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [h, hUV, hVE]

/-! ### Transport of Born-rule expectations

Three ways a quadratic form `⟨v| M |v⟩` moves: along a bijective reindexing of the space,
along an arbitrary linear map (which is how a dilation is compressed back), and the
special case `M = 1` that transports unit vectors. -/

/-- Reindexing the space by a bijection changes no Born-rule expectation. -/
theorem dotProduct_mulVec_submatrix {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (M : Matrix κ κ ℂ) (v : κ → ℂ) :
    star (v ∘ e) ⬝ᵥ ((M.submatrix e e) *ᵥ (v ∘ e)) = star v ⬝ᵥ (M *ᵥ v) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Function.comp_apply,
    Pi.star_apply]
  rw [← Equiv.sum_comp e fun k => star (v k) * ∑ k' : κ, M k k' * v k']
  exact Finset.sum_congr rfl fun i _ => by
    rw [Equiv.sum_comp e fun k' => M (e i) k' * v k']

/-- Reindexing the space by a bijection preserves the norm. -/
theorem dotProduct_comp_equiv {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (v : κ → ℂ) :
    star (v ∘ e) ⬝ᵥ (v ∘ e) = star v ⬝ᵥ v := by
  simp only [dotProduct, Function.comp_apply, Pi.star_apply]
  exact Equiv.sum_comp e fun k => star (v k) * v k

/-- Pulling a Born-rule expectation back along a linear map `W` conjugates the observable:
`⟨Wv| M |Wv⟩ = ⟨v| Wᴴ M W |v⟩`. With `W` an isometry and `M` a projection this is how a
dilated projective measurement compresses back to the POVM it came from. -/
theorem dotProduct_mulVec_conj {ι κ : Type} [Fintype ι] [Fintype κ]
    (W : Matrix κ ι ℂ) (M : Matrix κ κ ℂ) (v : ι → ℂ) :
    star (W *ᵥ v) ⬝ᵥ (M *ᵥ (W *ᵥ v)) = star v ⬝ᵥ ((Wᴴ * (M * W)) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]

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
