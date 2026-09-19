/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Naimark dilation against a fixed state

A POVM is the compression of a projective measurement on a larger space. What the applications
need is more than that: a whole *question-indexed family* of POVMs must be the compression of a
family of projective measurements by **one** question-independent isometry, because the state
the expectations are taken against is shared and must not depend on the question.
`exists_projective_dilation` is that statement, and the unitary extension
(`exists_unitary_extending`) is the step that buys it.

This file was extracted from `MIPRE/Background/Repetition/Entangled.lean`, where it was written
for the dilation direction of `lem:povm-value-eq`. It is generic mathematics --- matrices, an
ancilla register, and the completion of an orthonormal family to a basis --- and it reaches
none of the vendored trees, but `Entangled.lean` imports the 71k-line vendored
`Repetition/TenProofs/QuantumParallelRepetition`, and `MIPRE/LCS/` may not import
`MIPRE/Background/` at all. The second consumer is blueprint `lem:ms-direct-anticomm`, whose
proof dilates each of the Magic Square's six constraint POVMs against one shared ancilla, so
the code has to live outside `MIPRE/Background/` to be usable at all.

The Born-rule transport lemmas at the end travel with it: they are how a dilated projective
measurement is compressed back, and they say nothing about repetition either.
-/

namespace MIPRE

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

/-! ## Naimark dilation of a question-indexed family

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
      simp [ancillaEmbed]
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
    · simp [h]
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

/-! ## Transport of Born-rule expectations

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
end MIPRE
