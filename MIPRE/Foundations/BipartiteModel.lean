/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import MIPRE.Foundations.CommutingOperator
public import MIPRE.Foundations.OpBound
public import MIPRE.Tactics

@[expose] public section

/-!
# The bipartite model: a state and two commuting representations

The stage analyses of compression are bipartite and vector-state: a unit vector, the first
player's operators and the second player's, the two families commuting, and never a trace
(`reports/co-generalization-audit.md`). Their common generalization, the model of Phase 1 of
`planning/mipco-track.md`, is a **bipartite model** (`BipartiteModel`): a state model
(`MIPRE/Foundations/StateModel.lean`: a Hilbert space `H`, a state `ψ`, and a `⋆`-algebra `𝒞`
represented on `H`) with two `⋆`-algebras `𝒜` (the first player's) and `ℬ` (the second
player's) mapped into `𝒞` by `⋆`-homomorphisms `πA` and `πB` whose images commute. That `ψ` is a
unit vector is a hypothesis of the results that need it, as in the matrix calculus.

The players' operators are elements of `𝒜` and of `ℬ`. So a product, a sum or an adjoint of one
player's operators is again one of that player's, and it commutes with the other player's for
free: this is what the matrix analyses get from writing the two players' operators on the two
factors of a tensor product, and what lets them be read in this model unchanged. There are two
instances.

* **The tensor-product model** `BipartiteModel.tensor ψ`: `𝒞 = M_{dA × dB}(ℂ)`, `𝒜 = M_{dA}(ℂ)`,
  `ℬ = M_{dB}(ℂ)`, `πA = aOp` and `πB = bOp`, the Kronecker embeddings of
  `MIPRE/Foundations/OpBound.lean`, and `𝒞` acting on `EuclideanSpace ℂ (dA × dB)`. Its products
  and sums are literally the matrix ones, so the matrix calculus is the model's calculus with
  nothing to translate (`snorm_tensor`, `qform_tensor`, `bnd_tensor`).
* **The commuting-operator model** `CommutingOperatorStrategy.toModel S`: `𝒞 = B(H)`, `𝒜` the
  commutant of the second player's operators and `ℬ` the commutant of `𝒜`. They commute by
  construction, contain the two players' operators (`E_mem_aliceAlg`, `F_mem_bobAlg`), and are
  ordered, since a commutant contains the square roots of its positive elements
  (`starOrderedRing_centralizer`): positivity in them is positivity in `B(H)`, which is what the
  measurements of the analyses need.
-/

namespace MIPRE

open scoped InnerProductSpace

universe u v w x

/-- **A bipartite model**: a state model, and two `⋆`-algebras, the first player's and the
second player's, mapped into its algebra by `⋆`-homomorphisms with commuting images. -/
structure BipartiteModel (𝒞 : Type v) (𝒜 : Type w) (ℬ : Type x) [Ring 𝒞] [StarRing 𝒞]
    [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
    extends StateModel.{u} 𝒞 where
  /-- The first player's algebra. -/
  πA : 𝒜 →⋆ₐ[ℂ] 𝒞
  /-- The second player's algebra. -/
  πB : ℬ →⋆ₐ[ℂ] 𝒞
  /-- The two players' operators commute. -/
  commute : ∀ a b, Commute (πA a) (πB b)

namespace BipartiteModel

variable {𝒞 : Type v} {𝒜 : Type w} {ℬ : Type x} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜]
  [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- The model with the two players exchanged. -/
def swap (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) : BipartiteModel.{u} 𝒞 ℬ 𝒜 where
  toStateModel := M.toStateModel
  πA := M.πB
  πB := M.πA
  commute b a := (M.commute a b).symm

@[simp]
theorem swap_toStateModel (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) :
    M.swap.toStateModel = M.toStateModel := rfl

@[simp]
theorem swap_πA (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) : M.swap.πA = M.πB := rfl

@[simp]
theorem swap_πB (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) : M.swap.πB = M.πA := rfl

@[simp]
theorem swap_swap (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) : M.swap.swap = M := rfl

/-- A self-adjoint idempotent of the first player's algebra is bounded by one. -/
theorem bnd_πA_of_isStarProjection (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) {p : 𝒜}
    (hp : IsStarProjection p) : M.Bnd (M.πA p) 1 :=
  M.bnd_one_of_isStarProjection (hp.map M.πA)

/-- A self-adjoint idempotent of the second player's algebra is bounded by one. -/
theorem bnd_πB_of_isStarProjection (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) {q : ℬ}
    (hq : IsStarProjection q) : M.Bnd (M.πB q) 1 :=
  M.bnd_one_of_isStarProjection (hq.map M.πB)

/-! ## The tensor-product model -/

section Tensor

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- `X ↦ X ⊗ 1`, the first factor's matrices acting on the product, as a `⋆`-algebra
homomorphism. -/
noncomputable def aOpStarAlgHom : Matrix dA dA ℂ →⋆ₐ[ℂ] Matrix (dA × dB) (dA × dB) ℂ where
  toFun := aOp
  map_one' := aOp_one
  map_mul' := aOp_mul
  map_zero' := Matrix.zero_kronecker _
  map_add' := aOp_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, aOp_smul, aOp_one, ← Algebra.algebraMap_eq_smul_one]
  map_star' X := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, aOp_conjTranspose]

/-- `Y ↦ 1 ⊗ Y`, the second factor's matrices acting on the product, as a `⋆`-algebra
homomorphism. -/
noncomputable def bOpStarAlgHom : Matrix dB dB ℂ →⋆ₐ[ℂ] Matrix (dA × dB) (dA × dB) ℂ where
  toFun := bOp
  map_one' := bOp_one
  map_mul' := bOp_mul
  map_zero' := Matrix.kronecker_zero _
  map_add' := bOp_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, bOp_smul, bOp_one, ← Algebra.algebraMap_eq_smul_one]
  map_star' Y := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, bOp_conjTranspose]

@[simp]
theorem aOpStarAlgHom_apply (X : Matrix dA dA ℂ) :
    (aOpStarAlgHom (dB := dB)) X = aOp X := rfl

@[simp]
theorem bOpStarAlgHom_apply (Y : Matrix dB dB ℂ) :
    (bOpStarAlgHom (dA := dA)) Y = bOp Y := rfl

/-- **The tensor-product model** of a vector `ψ` on `ℂ^{dA × dB}`: the first player's matrices
act as `X ⊗ 1`, the second player's as `1 ⊗ Y`, and the product's matrices act on
`EuclideanSpace ℂ (dA × dB)`. -/
noncomputable def tensor (ψ : dA × dB → ℂ) :
    BipartiteModel (Matrix (dA × dB) (dA × dB) ℂ) (Matrix dA dA ℂ) (Matrix dB dB ℂ) where
  toStateModel := StateModel.mat ψ
  πA := aOpStarAlgHom
  πB := bOpStarAlgHom
  commute X Y := aOp_mul_bOp X Y

variable (ψ : dA × dB → ℂ)

@[simp]
theorem tensor_toStateModel : (tensor ψ).toStateModel = StateModel.mat ψ := rfl

@[simp]
theorem tensor_πA (X : Matrix dA dA ℂ) : (tensor ψ).πA X = aOp X := rfl

@[simp]
theorem tensor_πB (Y : Matrix dB dB ℂ) : (tensor ψ).πB Y = bOp Y := rfl

/-- **The matrix state norm is the state norm of the tensor-product model**, by definition. -/
theorem snorm_tensor (T : Matrix (dA × dB) (dA × dB) ℂ) : (tensor ψ).snorm T = snorm ψ T :=
  rfl

/-- **The matrix quadratic form is the quadratic form of the tensor-product model.** -/
theorem qform_tensor (T : Matrix (dA × dB) (dA × dB) ℂ) : (tensor ψ).qform T = qform ψ T :=
  (qform_eq_mat ψ T).symm

/-- **The matrix bound is the bound of the tensor-product model.** -/
theorem bnd_tensor {T : Matrix (dA × dB) (dA × dB) ℂ} {K : ℝ} :
    (tensor ψ).Bnd T K ↔ Bnd T K :=
  (bnd_iff ψ).symm

end Tensor

end BipartiteModel

/-! ## The commutant of a set of operators is ordered -/

section Commutant

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A commutant of operators is a star-ordered ring** with the order of `B(H)`: a positive
element is the square of its square root, which commutes with everything the element commutes
with and so lies in the commutant. -/
theorem starOrderedRing_centralizer (s : Set (H →L[ℂ] H)) :
    StarOrderedRing (StarSubalgebra.centralizer ℂ s) := by
  refine StarOrderedRing.of_nonneg_iff' (fun {x y} hxy z => ?_) (fun x => ⟨fun hx => ?_, ?_⟩)
  · show ((z : H →L[ℂ] H) + x) ≤ (z : H →L[ℂ] H) + y
    exact add_le_add_right (show (x : H →L[ℂ] H) ≤ y from hxy) _
  · have hx' : (0 : H →L[ℂ] H) ≤ x := hx
    have hmem : CFC.sqrt (x : H →L[ℂ] H) ∈ StarSubalgebra.centralizer ℂ s := by
      rw [StarSubalgebra.mem_centralizer_iff]
      intro g hg
      have hxg := ((StarSubalgebra.mem_centralizer_iff ℂ).1 x.2) g hg
      exact ⟨(Commute.cfcₙ_nnreal hxg.1.symm _).eq.symm,
        (Commute.cfcₙ_nnreal hxg.2.symm _).eq.symm⟩
    refine ⟨⟨CFC.sqrt (x : H →L[ℂ] H), hmem⟩, Subtype.ext ?_⟩
    show (x : H →L[ℂ] H) = star (CFC.sqrt (x : H →L[ℂ] H)) * CFC.sqrt (x : H →L[ℂ] H)
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq, CFC.sqrt_mul_sqrt_self _ hx']
  · rintro ⟨r, rfl⟩
    show (0 : H →L[ℂ] H) ≤ star (r : H →L[ℂ] H) * r
    exact star_mul_self_nonneg _

end Commutant

/-! ## The commuting-operator model -/

namespace CommutingOperatorStrategy

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The first player's algebra: the commutant of the second player's operators. -/
noncomputable def aliceAlg (S : CommutingOperatorStrategy X Y A B) :
    StarSubalgebra ℂ (S.H →L[ℂ] S.H) :=
  StarSubalgebra.centralizer ℂ (Set.range fun p : Y × B => S.F p.1 p.2)

/-- The second player's algebra: the commutant of the first player's algebra. -/
noncomputable def bobAlg (S : CommutingOperatorStrategy X Y A B) :
    StarSubalgebra ℂ (S.H →L[ℂ] S.H) :=
  StarSubalgebra.centralizer ℂ (S.aliceAlg : Set (S.H →L[ℂ] S.H))

noncomputable instance (S : CommutingOperatorStrategy X Y A B) : StarOrderedRing S.aliceAlg :=
  starOrderedRing_centralizer _

noncomputable instance (S : CommutingOperatorStrategy X Y A B) : StarOrderedRing S.bobAlg :=
  starOrderedRing_centralizer _

theorem E_mem_aliceAlg (S : CommutingOperatorStrategy X Y A B) (x : X) (a : A) :
    S.E x a ∈ S.aliceAlg := by
  rw [aliceAlg, StarSubalgebra.mem_centralizer_iff]
  rintro _ ⟨⟨y, b⟩, rfl⟩
  rw [(S.F_pos y b).isSelfAdjoint.star_eq]
  exact ⟨(S.commutes x y a b).eq.symm, (S.commutes x y a b).eq.symm⟩

theorem F_mem_bobAlg (S : CommutingOperatorStrategy X Y A B) (y : Y) (b : B) :
    S.F y b ∈ S.bobAlg := by
  rw [bobAlg, StarSubalgebra.mem_centralizer_iff]
  intro g hg
  rw [SetLike.mem_coe] at hg
  have h1 := ((StarSubalgebra.mem_centralizer_iff ℂ).1 hg _ ⟨(y, b), rfl⟩).1
  have h2 := ((StarSubalgebra.mem_centralizer_iff ℂ).1 (star_mem hg) _ ⟨(y, b), rfl⟩).1
  exact ⟨h1.symm, h2.symm⟩

/-- **The two players' algebras commute**, by construction. -/
theorem commute_of_mem (S : CommutingOperatorStrategy X Y A B) {a b : S.H →L[ℂ] S.H}
    (ha : a ∈ S.aliceAlg) (hb : b ∈ S.bobAlg) : Commute a b := by
  rw [bobAlg, StarSubalgebra.mem_centralizer_iff] at hb
  exact (hb a ha).1

/-- **The commuting-operator model of a strategy**: its space and state, with `B(H)` as the
algebra, the commutant of the second player's operators as the first player's algebra, and the
commutant of that as the second player's. -/
noncomputable def toModel (S : CommutingOperatorStrategy X Y A B) :
    BipartiteModel (S.H →L[ℂ] S.H) S.aliceAlg S.bobAlg where
  H := S.H
  ψ := S.ψ
  π := StarAlgHom.id ℂ _
  πA := S.aliceAlg.subtype
  πB := S.bobAlg.subtype
  commute a b := S.commute_of_mem a.2 b.2

theorem toModel_ψ_norm (S : CommutingOperatorStrategy X Y A B) : ‖S.toModel.ψ‖ = 1 :=
  S.ψ_norm

@[simp]
theorem toModel_πA (S : CommutingOperatorStrategy X Y A B) (a : S.aliceAlg) :
    S.toModel.πA a = (a : S.H →L[ℂ] S.H) := rfl

@[simp]
theorem toModel_πB (S : CommutingOperatorStrategy X Y A B) (b : S.bobAlg) :
    S.toModel.πB b = (b : S.H →L[ℂ] S.H) := rfl

/-- **The correlation of a strategy is the quadratic form of its model** at the product of the
two players' operators. -/
theorem correlation_eq_qform (S : CommutingOperatorStrategy X Y A B) (x : X) (y : Y) (a : A)
    (b : B) :
    S.correlation x y a b = S.toModel.qform
      (S.toModel.πA ⟨S.E x a, S.E_mem_aliceAlg x a⟩ *
        S.toModel.πB ⟨S.F y b, S.F_mem_bobAlg y b⟩) :=
  rfl

end CommutingOperatorStrategy

end MIPRE

end
