/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Games, strategies, and values

This file contains the definitions of blueprint Section 2.1 ("Games, strategies, and
values") of the MIP* = RE formalization project: two-player one-round nonlocal games, the
three classes of strategies (tensor-product, synchronous, and commuting), the associated
values, and the entanglement requirement.

The three strategy classes are built on a common skeleton, which this file factors out:
a question-indexed family of projective measurements in a complex star algebra
(`MIPRE.ProjectiveMeasurement`). Tensor-product strategies instantiate it on two matrix
algebras joined by a state vector and the Born rule; synchronous strategies instantiate
it on one matrix algebra `ℂ^{d×d}`, evaluated against the dimension-normalized trace;
commuting strategies are the general case of an abstract unital C*-algebra with a
tracial state (`MIPRE.TracialState`), evaluated by the generic value
`MIPRE.tracialValue`. The inclusion of synchronous into commuting strategies is
`MIPRE.SyncStrategy.toCommutingStrategy`, which preserves the value definitionally; the
comparison of values (blueprint `lem:sync-le-valco`) follows.

The matrix-based definitions (`POVM`, `SynchronousGame`, and the synchronous value)
agree with those of `MIPRE.HaltingGameValue`, which is kept self-contained. The
synchronous strategy is packaged differently there (with `POVM`s in place of a
`ProjectiveMeasurement`); `MIPRE.SyncStrategy.ofPOVM` and `MIPRE.SyncStrategy.value_eq`
provide the correspondence.

## Main definitions

- `MIPRE.Game`: two-player one-round games (blueprint `def:game`).
- `MIPRE.SynchronousGame`: synchronous games, with the interpretation
  `MIPRE.SynchronousGame.toGame` (blueprint `def:sync-game`).
- `MIPRE.ProjectiveMeasurement`: question-indexed projective measurement families in a
  star ring, the common skeleton of the three strategy classes.
- `MIPRE.TracialState`: tracial states on a complex star algebra;
  `MIPRE.normalizedTrace` is the normalized matrix trace `Tr(·)/d`.
- `MIPRE.tracialValue`: the generic value of a projective measurement family against a
  tracial state.
- `MIPRE.POVM`: positive operator-valued measures, following the QuantumLib
  (Lean-QuantumInfo) definition; the vocabulary of the distance measures
  (`MIPRE.Foundations.Distances`) and of the correspondence with
  `MIPRE.HaltingGameValue`.
- `MIPRE.TensorProductStrategy`: finite-dimensional tensor-product strategies, with
  projective measurements on both factors (blueprint `def:tensor-strategy`).
- `MIPRE.quantumValue`: the quantum value `val*` of a game (blueprint `def:q-value`).
- `MIPRE.SyncStrategy`: synchronous strategies (blueprint `def:sync-strategy`), the
  instantiation of the skeleton at `ℂ^{d×d}` with the normalized trace.
- `MIPRE.SyncStrategy.IsPCC`: PCC (projective, consistent, and commuting) strategies
  (blueprint `def:pcc`).
- `MIPRE.syncValue`: the synchronous value of a synchronous game (blueprint
  `def:sync-value`).
- `MIPRE.CommutingStrategy`: commuting strategies, given by a unital C*-algebra with a
  tracial state (blueprint `def:commuting-strategy`).
- `MIPRE.commValue`: the commuting value of a synchronous game (blueprint
  `def:commuting-value`).
- `MIPRE.SyncStrategy.toCommutingStrategy`: a synchronous strategy is a commuting
  strategy, with the same value (`MIPRE.SyncStrategy.value_toCommutingStrategy`).
- `MIPRE.entRequirement`: the entanglement requirement `Ent(G, ν)` (blueprint `def:ent`).

## Main statements

- `MIPRE.tracialValue_nonneg` and `MIPRE.tracialValue_le_one`: the generic value lies in
  `[0, 1]`; the synchronous and commuting values inherit both bounds.
- `MIPRE.ProjectiveMeasurement.consistency`: against a tracial state, a projective
  family answers equal questions with equal answers (probability zero for `a ≠ b`).
- `MIPRE.syncValue_le_quantumValue`: the synchronous value lower-bounds the quantum value
  (blueprint `lem:sync-le-valstar`).
- `MIPRE.syncValue_le_commValue`: the synchronous value lower-bounds the commuting value
  (blueprint `lem:sync-le-valco`).

## Implementation notes

- Question distributions are bare real-valued functions with nonnegativity and
  normalization fields, rather than `PMF` (which is `ℝ≥0∞`-valued and would force
  coercions in the value definitions).
- Outcome probabilities are nonnegative reals, but proving so requires positivity
  arguments; as in `MIPRE.HaltingGameValue`, each value takes the real part `.re` of the
  relevant complex quantity so that the definitions carry no proof obligations.
- The shared layer (`ProjectiveMeasurement`, `TracialState`, `tracialValue`) requires no
  norm: the definitions and the basic lemmas hold over any complex star algebra. The
  C*-structure enters only in `CommutingStrategy`, following the blueprint. In
  particular the matrix-based strategies never need mathlib's (scoped) matrix
  operator-norm instances.
- Tensor-product strategies are defined with projective measurements, as in JNVWY
  (where strategies are assumed projective; by Naimark dilation this loses no
  generality, and allowing general POVMs would define the same quantum value — a fact
  we do not need and do not formalize). General POVMs remain as `POVM`, the vocabulary
  of the distance measures and rounding arguments.
- The algebra of a `CommutingStrategy` lives in universe `0`. This loses no generality:
  for a finite game, the GNS representation of the (separable) C*-subalgebra generated by
  the finitely many measurement operators realizes the same correlation, and it lives in
  universe `0`.
- `SyncStrategy.toCommutingStrategy` realizes the matrix algebra as
  `CStarMatrix (Fin d) (Fin d) ℂ`, mathlib's type synonym of `Matrix` carrying the
  (unscoped) operator-norm `CStarAlgebra` instance. All algebraic instances of
  `CStarMatrix` are definitionally those of `Matrix`, so the strategy transported along
  `CStarMatrix.ofMatrixStarAlgEquiv` has the same value by `rfl`.
- A commuting strategy whose algebra is finite-dimensional is *not* literally a
  synchronous strategy: a finite-dimensional C*-algebra is a direct sum of matrix
  blocks, and its tracial states are the convex combinations of the normalized traces
  of the blocks. The two notions give the same supremum of values (decompose the trace
  and pick the best block), but we do not need this fact; the inclusion
  `SyncStrategy.toCommutingStrategy` is the direction the project uses.
- `POVM` matches the QuantumLib (Lean-QuantumInfo) definition
  (`QuantumInfo.Finite.POVM`), with `selfAdjoint (Matrix d d ℂ)` spelled out for its
  definitionally equal `HermitianMat d ℂ`, so that the strategy layer can be upstreamed.
  `SyncStrategy.povm` and `SyncStrategy.ofPOVM` convert between the
  `ProjectiveMeasurement` packaging and the POVM packaging.

## References

- Ji, Natarajan, Vidick, Wright, Yuen, *MIP\* = RE*, arXiv:2001.04383.
-/

namespace MIPRE

/- The partial order on `ℂ` (for positivity of tracial states) and the Loewner order on
matrices (`0 ≤ A ↔ A.PosSemidef`, for POVM elements) are scoped. -/
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder

/-! ## Games -/

/-- A two-player one-round game (blueprint `def:game`): finite question alphabets `X`,
`Y`, finite answer alphabets `A`, `B`, a probability distribution `μ` on `X × Y`, and a
decision predicate `D` (`true` = accept). -/
structure Game (X Y A B : Type*) [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  /-- The probability that the players are asked the question pair `(x, y)`. -/
  μ : X → Y → ℝ
  /-- Question probabilities are nonnegative. -/
  μ_nonneg : ∀ x y, 0 ≤ μ x y
  /-- Question probabilities sum to one. -/
  μ_sum_one : ∑ x, ∑ y, μ x y = 1
  /-- The decision predicate: `D x y a b = true` means the answers `(a, b)` to the
  questions `(x, y)` are accepted. -/
  D : X → Y → A → B → Bool

/-- A synchronous game (blueprint `def:sync-game`): both players receive questions from
the same alphabet and answer from the same alphabet; on equal questions, unequal answers
always lose. -/
structure SynchronousGame (X A : Type*) [Fintype X] [Fintype A] [DecidableEq A] where
  /-- The probability that the players are asked the question pair `(x, y)`. -/
  μ : X → X → ℝ
  /-- Question probabilities are nonnegative. -/
  μ_nonneg : ∀ x y, 0 ≤ μ x y
  /-- Question probabilities sum to one. -/
  μ_sum_one : ∑ x, ∑ y, μ x y = 1
  /-- The decision predicate: `D x y a b = true` means the answers `(a, b)` to the
  questions `(x, y)` are accepted. -/
  D : X → X → A → A → Bool
  /-- Unequal answers to equal questions are rejected. -/
  synchronous : ∀ x a b, a ≠ b → D x x a b = false

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- A synchronous game is in particular a game, with `Y = X` and `B = A`. -/
def SynchronousGame.toGame [DecidableEq A] (G : SynchronousGame X A) : Game X X A A where
  μ := G.μ
  μ_nonneg := G.μ_nonneg
  μ_sum_one := G.μ_sum_one
  D := G.D

/-! ## Projective measurement families and tracial states

All strategy classes below are built on a common skeleton: a question-indexed family of
projective measurements in a complex star algebra. Tensor-product and synchronous
strategies instantiate it on matrix algebras; commuting strategies on an abstract unital
C*-algebra, evaluated against a tracial state. The skeleton is defined once, so that
the definitions and basic lemmas are shared. No norm is needed at this level of
generality. -/

/-- A question-indexed family of projective measurements with outcomes in a star ring
`𝒜`: for each question `x`, the operators `M x a` are self-adjoint idempotents (i.e.
orthogonal projections) that sum to one. This is the common skeleton of the strategy
classes: tensor-product strategies (`TensorProductStrategy`) and synchronous strategies
(`SyncStrategy`) instantiate it at matrix algebras, commuting strategies
(`CommutingStrategy`) at an abstract unital C*-algebra. -/
structure ProjectiveMeasurement (X A 𝒜 : Type*) [Fintype A] [Ring 𝒜] [StarRing 𝒜] where
  /-- The measurement operators, indexed by questions and answers. -/
  M : X → A → 𝒜
  /-- Each measurement operator is self-adjoint. -/
  selfAdjoint : ∀ x a, star (M x a) = M x a
  /-- Each measurement operator is idempotent, hence a projection. -/
  projective : ∀ x a, M x a * M x a = M x a
  /-- For each question, the measurement operators sum to one. -/
  normalized : ∀ x, ∑ a, M x a = 1

/-- A tracial state on a complex star algebra `𝒜`: a linear functional that is positive
(`0 ≤ τ (star m * m)`, in the order of `ℂ`), unital (`τ 1 = 1`), and tracial
(`τ (m * n) = τ (n * m)`). On a unital C*-algebra this is the standard notion of tracial
state (blueprint `def:commuting-strategy`). -/
structure TracialState (𝒜 : Type*) [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜] extends
    𝒜 →ₗ[ℂ] ℂ where
  /-- The functional is positive. -/
  nonneg' : ∀ m, 0 ≤ toLinearMap (star m * m)
  /-- The functional is unital. -/
  map_one' : toLinearMap 1 = 1
  /-- The functional is tracial. -/
  map_mul_comm' : ∀ m n, toLinearMap (m * n) = toLinearMap (n * m)

variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]

namespace TracialState

instance : FunLike (TracialState 𝒜) 𝒜 ℂ where
  coe τ := ⇑τ.toLinearMap
  coe_injective τ σ h := by
    cases τ; cases σ; congr; exact DFunLike.coe_injective h

instance : LinearMapClass (TracialState 𝒜) ℂ 𝒜 ℂ where
  map_add τ := map_add τ.toLinearMap
  map_smulₛₗ τ := map_smulₛₗ τ.toLinearMap

@[simp] theorem coe_toLinearMap (τ : TracialState 𝒜) : ⇑τ.toLinearMap = ⇑τ := rfl

@[simp] theorem coe_mk (f : 𝒜 →ₗ[ℂ] ℂ) (h₁ h₂ h₃) :
    ⇑(⟨f, h₁, h₂, h₃⟩ : TracialState 𝒜) = ⇑f := rfl

/-- A tracial state is positive. -/
theorem star_mul_self_nonneg (τ : TracialState 𝒜) (m : 𝒜) : 0 ≤ τ (star m * m) :=
  τ.nonneg' m

/-- A tracial state is unital. -/
@[simp] theorem map_one (τ : TracialState 𝒜) : τ 1 = 1 := τ.map_one'

/-- A tracial state is tracial. -/
theorem map_mul_comm (τ : TracialState 𝒜) (m n : 𝒜) : τ (m * n) = τ (n * m) :=
  τ.map_mul_comm' m n

/-- The trace of a product of two projections is nonnegative:
`τ (p * q) = τ (star (q * p) * (q * p))`. This is the positivity of outcome
probabilities for the strategies below. -/
theorem nonneg_mul (τ : TracialState 𝒜) {p q : 𝒜} (hps : star p = p) (hpp : p * p = p)
    (hqs : star q = q) (hqq : q * q = q) : 0 ≤ τ (p * q) := by
  have key : star (q * p) * (q * p) = p * q * p := by
    rw [star_mul, hps, hqs, mul_assoc p q (q * p), ← mul_assoc q q p, hqq, ← mul_assoc]
  calc (0 : ℂ) ≤ τ (star (q * p) * (q * p)) := τ.star_mul_self_nonneg _
    _ = τ (p * q * p) := by rw [key]
    _ = τ (p * q) := by rw [τ.map_mul_comm (p * q) p, ← mul_assoc, hpp]

/-- Real-part form of `TracialState.nonneg_mul`. -/
theorem re_nonneg_mul (τ : TracialState 𝒜) {p q : 𝒜} (hps : star p = p) (hpp : p * p = p)
    (hqs : star q = q) (hqq : q * q = q) : 0 ≤ (τ (p * q)).re := by
  simpa using (Complex.le_def.mp (τ.nonneg_mul hps hpp hqs hqq)).1

/-- Pull back a tracial state along a star-algebra equivalence. -/
def comp (τ : TracialState ℬ) (φ : 𝒜 ≃⋆ₐ[ℂ] ℬ) : TracialState 𝒜 where
  toLinearMap :=
    { toFun := fun m => τ (φ m)
      map_add' := fun m n => by simp [map_add]
      map_smul' := fun c m => by simp [map_smul] }
  nonneg' m := by
    show 0 ≤ τ (φ (star m * m))
    rw [map_mul φ, map_star φ]
    exact τ.star_mul_self_nonneg _
  map_one' := by
    show τ (φ 1) = 1
    rw [_root_.map_one φ, τ.map_one]
  map_mul_comm' m n := by
    show τ (φ (m * n)) = τ (φ (n * m))
    rw [map_mul φ, map_mul φ, τ.map_mul_comm]

@[simp] theorem comp_apply (τ : TracialState ℬ) (φ : 𝒜 ≃⋆ₐ[ℂ] ℬ) (m : 𝒜) :
    τ.comp φ m = τ (φ m) := rfl

end TracialState

namespace ProjectiveMeasurement

/-- Transport a projective measurement family along a star-algebra equivalence. -/
def map (φ : 𝒜 ≃⋆ₐ[ℂ] ℬ) (P : ProjectiveMeasurement X A 𝒜) :
    ProjectiveMeasurement X A ℬ where
  M x a := φ (P.M x a)
  selfAdjoint x a := by rw [← map_star, P.selfAdjoint]
  projective x a := by rw [← map_mul, P.projective]
  normalized x := by rw [← map_sum, P.normalized, map_one]

omit [Fintype X] in
@[simp] theorem map_M (φ : 𝒜 ≃⋆ₐ[ℂ] ℬ) (P : ProjectiveMeasurement X A 𝒜) (x : X)
    (a : A) : (P.map φ).M x a = φ (P.M x a) := rfl

variable [DecidableEq A]

omit [Fintype X] in
/-- Perfect consistency: against a tracial state, a projective measurement family
answers unequal answers to equal questions with probability zero. This is why the
"consistent" condition of a PCC strategy (blueprint `def:pcc`) is automatic for
synchronous strategies. -/
theorem consistency (P : ProjectiveMeasurement X A 𝒜) (τ : TracialState 𝒜) (x : X)
    {a b : A} (hab : a ≠ b) : τ (P.M x a * P.M x b) = 0 := by
  have hnn : ∀ a', 0 ≤ τ (P.M x a' * P.M x b) := fun a' =>
    τ.nonneg_mul (P.selfAdjoint x a') (P.projective x a') (P.selfAdjoint x b)
      (P.projective x b)
  -- the total over `a'` is `τ (M^x_b)`, and the term `a' = b` alone already reaches it
  have hsum : ∑ a', τ (P.M x a' * P.M x b) = τ (P.M x b) := by
    rw [← map_sum, ← Finset.sum_mul, P.normalized, one_mul]
  have herase : ∑ a' ∈ Finset.univ.erase b, τ (P.M x a' * P.M x b) = 0 := by
    have h := Finset.sum_erase_add Finset.univ
      (fun a' => τ (P.M x a' * P.M x b)) (Finset.mem_univ b)
    rw [hsum, P.projective x b] at h
    linear_combination h
  exact (Finset.sum_eq_zero_iff_of_nonneg fun a' _ => hnn a').mp herase a
    (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩)

end ProjectiveMeasurement

/-! ## POVMs -/

/-- A POVM is a (finite) collection of PSD matrices on the same Hilbert space that sum
to the identity. Here `X` indexes the matrices, and `d` is the space dimension.

This is the QuantumLib (Lean-QuantumInfo) definition of `POVM`, with
`selfAdjoint (Matrix d d ℂ)` spelled out for its definitionally equal
`HermitianMat d ℂ`; `0 ≤ mats x` is the Loewner order, i.e. positive semidefiniteness.

General POVMs are not part of the strategy definitions (strategies are projective, via
`ProjectiveMeasurement`); they are the vocabulary of the distance measures
(`MIPRE.Foundations.Distances`) and of the correspondence with
`MIPRE.HaltingGameValue` (`SyncStrategy.povm`, `SyncStrategy.ofPOVM`). -/
structure POVM (X : Type*) (d : Type*) [Fintype X] [Fintype d] [DecidableEq d] where
  /-- The measurement operators, one for each outcome. -/
  mats : X → selfAdjoint (Matrix d d ℂ)
  /-- Each measurement operator is positive semidefinite. -/
  nonneg : ∀ x, 0 ≤ mats x
  /-- The measurement operators sum to the identity. -/
  normalized : ∑ x, mats x = 1

/-! ## Tensor-product strategies and the quantum value -/

/-- A tensor-product strategy for a game `G` (blueprint `def:tensor-strategy`):
finite-dimensional Hilbert spaces `ℂ^dA` and `ℂ^dB`, a unit vector `ψ` in their tensor
product — realized as `Fin dA × Fin dB → ℂ` — and projective measurements `{A^x_a}` on
`ℂ^dA` and `{B^y_b}` on `ℂ^dB`, packaged as `ProjectiveMeasurement` families on the two
matrix algebras. Restricting to projective measurements follows JNVWY; by Naimark
dilation this loses no generality. Outcome probabilities are computed using the Born
rule (see `TensorProductStrategy.value`). -/
structure TensorProductStrategy (G : Game X Y A B) where
  /-- The dimension of the first player's Hilbert space. -/
  dA : ℕ
  /-- The dimension of the second player's Hilbert space. -/
  dB : ℕ
  /-- The shared state, a vector in the tensor product `ℂ^dA ⊗ ℂ^dB = ℂ^(dA × dB)`. -/
  ψ : Fin dA × Fin dB → ℂ
  /-- The shared state is a unit vector. (In particular `dA` and `dB` are positive,
  since a zero-dimensional space contains no unit vector.) -/
  ψ_unit : star ψ ⬝ᵥ ψ = 1
  /-- The first player's measurements: for each question `x`, a projective measurement
  on `ℂ^dA`. -/
  PA : ProjectiveMeasurement X A (Matrix (Fin dA) (Fin dA) ℂ)
  /-- The second player's measurements: for each question `y`, a projective measurement
  on `ℂ^dB`. -/
  PB : ProjectiveMeasurement Y B (Matrix (Fin dB) (Fin dB) ℂ)

/-- The value of a tensor-product strategy in `G` (blueprint `def:q-value`): the players
answer questions `(x, y)` with `(a, b)` with the Born-rule probability
`⟨ψ| A^x_a ⊗ B^y_b |ψ⟩`, the tensor product being realized by the Kronecker product.
The probability is a nonnegative real; we take the real part so that the definition
typechecks with no proof obligations. -/
noncomputable def TensorProductStrategy.value {G : Game X Y A B}
    (S : TensorProductStrategy G) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re

/-- The quantum value `val*(G)` of a game (blueprint `def:q-value`): the supremum of
strategy values over all tensor-product strategies. -/
noncomputable def quantumValue (G : Game X Y A B) : ℝ :=
  ⨆ S : TensorProductStrategy G, S.value

/-! ## The generic tracial value -/

variable [DecidableEq A]

/-- The value of a projective measurement family `P` against a tracial state `τ` in a
synchronous game `G`: the players answer questions `(x, y)` with `(a, b)` with
probability `τ (M^x_a M^y_b)`, a nonnegative real by `TracialState.nonneg_mul`; we take
the real part so that the definition carries no proof obligations. The synchronous value
(blueprint `def:sync-value`) and the commuting value (blueprint `def:commuting-value`)
are instantiations. -/
noncomputable def tracialValue (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    G.μ x y * (if G.D x y a b then 1 else 0) * (τ (P.M x a * P.M y b)).re

/-- The generic value is nonnegative. -/
theorem tracialValue_nonneg (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜) : 0 ≤ tracialValue G τ P := by
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  have hre : 0 ≤ (τ (P.M x a * P.M y b)).re :=
    τ.re_nonneg_mul (P.selfAdjoint x a) (P.projective x a) (P.selfAdjoint y b)
      (P.projective y b)
  have hind : (0 : ℝ) ≤ if G.D x y a b then 1 else 0 := by split_ifs <;> norm_num
  exact mul_nonneg (mul_nonneg (G.μ_nonneg x y) hind) hre

/-- The generic value is at most one: for each question pair the outcome probabilities
`τ (M^x_a M^y_b)` sum to `τ 1 = 1` over the answers. -/
theorem tracialValue_le_one (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜) : tracialValue G τ P ≤ 1 := by
  have key : ∀ x y, ∑ a, ∑ b, (τ (P.M x a * P.M y b)).re = 1 := by
    intro x y
    have hsum : ∑ a, ∑ b, τ (P.M x a * P.M y b) = 1 := by
      have h1 : ∀ a, ∑ b, τ (P.M x a * P.M y b) = τ (P.M x a) := fun a => by
        rw [← map_sum, ← Finset.mul_sum, P.normalized, mul_one]
      simp_rw [h1]
      rw [← map_sum, P.normalized, τ.map_one]
    have := congrArg Complex.re hsum
    simpa [Complex.re_sum] using this
  calc tracialValue G τ P
      ≤ ∑ x, ∑ y, G.μ x y * ∑ a, ∑ b, (τ (P.M x a * P.M y b)).re := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun b _ => ?_
        have hre : 0 ≤ (τ (P.M x a * P.M y b)).re :=
          τ.re_nonneg_mul (P.selfAdjoint x a) (P.projective x a) (P.selfAdjoint y b)
            (P.projective y b)
        cases hD : G.D x y a b with
        | false => simpa [hD] using mul_nonneg (G.μ_nonneg x y) hre
        | true => simp
    _ = ∑ x, ∑ y, G.μ x y := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [key, mul_one]
    _ = 1 := G.μ_sum_one

/-- The dimension-normalized trace `τ(m) = Tr(m)/n` is a tracial state on the matrix
algebra `ℂ^{n×n}` (in fact its unique tracial state, though we do not prove this). -/
noncomputable def normalizedTrace (n : Type*) [Fintype n] [DecidableEq n]
    [hn : Nonempty n] : TracialState (Matrix n n ℂ) where
  toLinearMap := (Fintype.card n : ℂ)⁻¹ • Matrix.traceLinearMap n ℂ ℂ
  nonneg' m := by
    show (0 : ℂ) ≤ (Fintype.card n : ℂ)⁻¹ * (star m * m).trace
    refine mul_nonneg ?_ ?_
    · rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
      exact Complex.zero_le_real.mpr (by positivity)
    · have h := Matrix.posSemidef_conjTranspose_mul_self m
      rw [← Matrix.star_eq_conjTranspose] at h
      exact h.trace_nonneg
  map_one' := by
    show (Fintype.card n : ℂ)⁻¹ * (1 : Matrix n n ℂ).trace = 1
    rw [Matrix.trace_one, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  map_mul_comm' m₁ m₂ := by
    show (Fintype.card n : ℂ)⁻¹ * (m₁ * m₂).trace =
      (Fintype.card n : ℂ)⁻¹ * (m₂ * m₁).trace
    rw [Matrix.trace_mul_comm]

@[simp] theorem normalizedTrace_apply (n : Type*) [Fintype n] [DecidableEq n]
    [Nonempty n] (m : Matrix n n ℂ) :
    normalizedTrace n m = (Fintype.card n : ℂ)⁻¹ * m.trace := rfl

/-! ## Synchronous strategies and the synchronous value -/

/-- A synchronous strategy for a synchronous game (blueprint `def:sync-strategy`): a
question-indexed projective measurement family on `ℂ^d` (`d > 0`). Measurements for
different questions need not commute. There is no state vector: outcome probabilities
are computed with the dimension-normalized trace `τ(M) = Tr(M)/d` (see
`SyncStrategy.value`). This is the instantiation of the commuting framework at the full
matrix algebra with its canonical tracial state, see
`SyncStrategy.toCommutingStrategy`. -/
structure SyncStrategy (G : SynchronousGame X A) where
  /-- The dimension of the Hilbert space. -/
  d : ℕ
  /-- The dimension is positive. -/
  d_pos : 0 < d
  /-- The measurements: for each question, a projective measurement on `ℂ^d`. -/
  P : ProjectiveMeasurement X A (Matrix (Fin d) (Fin d) ℂ)

namespace SyncStrategy

variable {G : SynchronousGame X A}

/-- The value of a synchronous strategy in `G` (blueprint `def:sync-value`): the generic
tracial value against the normalized trace `τ(M) = Tr(M)/d`. See `SyncStrategy.value_eq`
for the explicit form. -/
noncomputable def value (S : SyncStrategy G) : ℝ :=
  tracialValue G (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) S.P

/-- The value of a synchronous strategy, written out (the spelling of blueprint
`def:sync-value` and of `MIPRE.HaltingGameValue.strategyValue`): the players answer
questions `(x, y)` with `(a, b)` with probability `Tr(M^x_a M^y_b)/d`. -/
theorem value_eq (S : SyncStrategy G) :
    S.value = ∑ x, ∑ y, ∑ a, ∑ b,
      G.μ x y * (if G.D x y a b then 1 else 0) *
        ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ)) := by
  unfold value tracialValue
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  show ((Fintype.card (Fin S.d) : ℂ)⁻¹ * (S.P.M x a * S.P.M y b).trace).re = _
  rw [Fintype.card_fin, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.re_ofReal_mul, inv_mul_eq_div]

/-- The value of a synchronous strategy is nonnegative. -/
theorem value_nonneg (S : SyncStrategy G) : 0 ≤ S.value :=
  tracialValue_nonneg G _ S.P

/-- The value of a synchronous strategy is at most one. -/
theorem value_le_one (S : SyncStrategy G) : S.value ≤ 1 :=
  tracialValue_le_one G _ S.P

/-- The measurements of a synchronous strategy, packaged as POVMs (positivity follows
from projectivity). This is the interface to the QuantumLib-compatible `POVM` layer. -/
def povm (S : SyncStrategy G) (x : X) : POVM A (Fin S.d) where
  mats a := ⟨S.P.M x a, selfAdjoint.mem_iff.mpr (S.P.selfAdjoint x a)⟩
  nonneg a := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (S.P.M x a)
    rw [← Matrix.star_eq_conjTranspose, S.P.selfAdjoint x a, S.P.projective x a] at h
    exact Subtype.coe_le_coe.mp h.nonneg
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact S.P.normalized x

/-- Build a synchronous strategy from POVM data with a projectivity certificate (the
packaging of `MIPRE.HaltingGameValue.SyncStrategy`). -/
def ofPOVM (d : ℕ) (d_pos : 0 < d) (povm : X → POVM A (Fin d))
    (projective : ∀ x a,
      ((povm x).mats a).val * ((povm x).mats a).val = ((povm x).mats a).val) :
    SyncStrategy G where
  d := d
  d_pos := d_pos
  P :=
    { M := fun x a => ((povm x).mats a).val
      selfAdjoint := fun x a => selfAdjoint.mem_iff.mp ((povm x).mats a).property
      projective := projective
      normalized := fun x => by
        have h := congrArg Subtype.val (povm x).normalized
        rwa [AddSubmonoidClass.coe_finsetSum, selfAdjoint.val_one] at h }

/-- A synchronous strategy is *PCC* (*projective, consistent, and commuting*, following
JNVWY Section 5.2; blueprint `def:pcc`) if the measurement operators associated with any
pair of questions asked with positive probability commute. Projectivity is part of
`SyncStrategy`, and consistency is automatic for synchronous strategies
(`ProjectiveMeasurement.consistency`), so only the commutation condition remains. -/
def IsPCC (S : SyncStrategy G) : Prop :=
  ∀ x y, 0 < G.μ x y → ∀ a b,
    S.P.M x a * S.P.M y b = S.P.M y b * S.P.M x a

end SyncStrategy

/-- The synchronous value of a synchronous game (blueprint `def:sync-value`): the
supremum of strategy values over all synchronous strategies. -/
noncomputable def syncValue (G : SynchronousGame X A) : ℝ :=
  ⨆ S : SyncStrategy G, S.value

/-! ## Commuting strategies and the commuting value -/

/-- A commuting strategy for a synchronous game (blueprint `def:commuting-strategy`): a
unital C*-algebra `alg` with a tracial state `τ`, together with a question-indexed
projective measurement family in `alg`. Outcome probabilities are computed with `τ` (see
`CommutingStrategy.value`).

The algebra lives in universe `0`; by the GNS representation this loses no generality
(see the module docstring). -/
structure CommutingStrategy (G : SynchronousGame X A) where
  /-- The underlying unital C*-algebra. -/
  alg : Type
  /-- The C*-algebra structure. -/
  [cstarAlgebra : CStarAlgebra alg]
  /-- The tracial state. -/
  τ : TracialState alg
  /-- The measurements: for each question, a projective measurement in `alg`. -/
  P : ProjectiveMeasurement X A alg

attribute [instance] CommutingStrategy.cstarAlgebra

namespace CommutingStrategy

variable {G : SynchronousGame X A}

/-- The value of a commuting strategy in `G` (blueprint `def:commuting-value`): the
generic tracial value; the players answer questions `(x, y)` with `(a, b)` with
probability `τ(M^x_a M^y_b)`. -/
noncomputable def value (S : CommutingStrategy G) : ℝ :=
  tracialValue G S.τ S.P

/-- The value of a commuting strategy is nonnegative. -/
theorem value_nonneg (S : CommutingStrategy G) : 0 ≤ S.value :=
  tracialValue_nonneg G S.τ S.P

/-- The value of a commuting strategy is at most one. -/
theorem value_le_one (S : CommutingStrategy G) : S.value ≤ 1 :=
  tracialValue_le_one G S.τ S.P

/-- The values of commuting strategies are bounded above (by one). -/
theorem bddAbove_range_value (G : SynchronousGame X A) :
    BddAbove (Set.range fun S : CommutingStrategy G => S.value) := by
  refine ⟨1, ?_⟩
  rintro r ⟨S, rfl⟩
  exact S.value_le_one

end CommutingStrategy

/-- The commuting value of a synchronous game (blueprint `def:commuting-value`): the
supremum of strategy values over all commuting strategies. -/
noncomputable def commValue (G : SynchronousGame X A) : ℝ :=
  ⨆ S : CommutingStrategy G, S.value

/-- The commuting value is nonnegative. -/
theorem commValue_nonneg (G : SynchronousGame X A) : 0 ≤ commValue G :=
  Real.iSup_nonneg fun S => S.value_nonneg

/-! ## A synchronous strategy is a commuting strategy -/

/-- A synchronous strategy is a commuting strategy (the content of blueprint
`lem:sync-le-valco`): take the algebra of `d × d` complex matrices with the normalized
trace. The algebra is realized as `CStarMatrix (Fin d) (Fin d) ℂ` — mathlib's type
synonym of `Matrix` carrying the operator-norm `CStarAlgebra` instance — and the
measurements and the state are transported along the definitionally trivial
star-algebra equivalence `CStarMatrix.ofMatrixStarAlgEquiv`. The value is preserved:
`SyncStrategy.value_toCommutingStrategy`. -/
noncomputable def SyncStrategy.toCommutingStrategy {G : SynchronousGame X A}
    (S : SyncStrategy G) : CommutingStrategy G where
  alg := CStarMatrix (Fin S.d) (Fin S.d) ℂ
  τ := (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)).comp
    CStarMatrix.ofMatrixStarAlgEquiv.symm
  P := S.P.map CStarMatrix.ofMatrixStarAlgEquiv

/-- `SyncStrategy.toCommutingStrategy` preserves the value — definitionally. -/
@[simp] theorem SyncStrategy.value_toCommutingStrategy {G : SynchronousGame X A}
    (S : SyncStrategy G) : S.toCommutingStrategy.value = S.value :=
  rfl

/-! ## Entanglement requirement -/

/-- The entanglement requirement `Ent(G, ν)` (blueprint `def:ent`): the least `d` such
that there exists a synchronous strategy with dimension at most `d` achieving value at
least `ν` in `G`, and `∞` if no synchronous strategy achieves `ν`. It is realized as the
infimum in `ℕ∞` of the dimensions of the achieving strategies, which takes the value
`⊤ = ∞` when there are none. -/
noncomputable def entRequirement (G : SynchronousGame X A) (ν : ℝ) : ℕ∞ :=
  ⨅ S : {S : SyncStrategy G // ν ≤ S.value}, (S.val.d : ℕ∞)

/-! ## Relationship lemmas -/

/-- The synchronous value lower-bounds the quantum value (blueprint
`lem:sync-le-valstar`): a synchronous strategy `{M^x_a}` on `ℂ^d` yields the
tensor-product strategy `A^x_a = M^x_a`, `B^y_b = (M^y_b)ᵀ`,
`ψ = d^{-1/2} ∑ᵢ |i⟩|i⟩` with the same value. -/
theorem syncValue_le_quantumValue (G : SynchronousGame X A) :
    syncValue G ≤ quantumValue G.toGame :=
  sorry

/-- The synchronous value lower-bounds the commuting value (blueprint
`lem:sync-le-valco`): a synchronous strategy on `ℂ^d` is a commuting strategy with
`alg = ℂ^{d × d}` and `τ = Tr/d` (`SyncStrategy.toCommutingStrategy`), with the same
value. -/
theorem syncValue_le_commValue (G : SynchronousGame X A) :
    syncValue G ≤ commValue G := by
  refine Real.iSup_le (fun S => ?_) (commValue_nonneg G)
  rw [← S.value_toCommutingStrategy]
  exact le_ciSup (CommutingStrategy.bddAbove_range_value G) S.toCommutingStrategy

end MIPRE
