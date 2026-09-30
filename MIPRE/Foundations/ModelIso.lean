/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.ModelStrategy
public import MIPRE.Foundations.TensorExpand

@[expose] public section

/-!
# Isomorphisms of bipartite models

A local isometry (`BipartiteModel.LocalIsometry`) moves a strategy from one model into another,
and carries its value over on the transported state. When the isometry is onto, the two
homomorphisms are bijective and the state goes to the state, nothing is lost in either direction:
the two models are **isomorphic** (`BipartiteModel.Iso`), and a property of models stated through
Born probabilities --- the soundness of a test, the domination of the strategies by a value ---
passes from either to the other. The constructions of `MIPRE/Foundations/AncillaIsometry.lean`
and `MIPRE/Foundations/TensorExpand.lean` are isomorphisms in this sense, once their state
hypotheses hold:

* **an extension by one-point registers in the state `1`** is the model itself
  (`BipartiteModel.expandUnit`);
* **associativity** of extensions (`BipartiteModel.assocIso`), **relabelling** of the registers
  (`BipartiteModel.relabelIso`), and the **exchange of the players** in an extension
  (`BipartiteModel.swapExpandIso`);
* an isomorphism of models extends to their extensions by the same registers
  (`BipartiteModel.Iso.expandCongr`);
* the extension of a tensor-product model is the tensor-product model of the expanded vector
  (`BipartiteModel.tensorExpandIso`), and a tensor-product model is unchanged by relabelling the
  two factors (`BipartiteModel.tensorReindexIso`), so that a statement about the tensor-product
  models of states on `Fin a × Fin b` holds on any finite factors.

Each of these is a local isometry of those files with inverses (`Iso.ofLocalIsometry`), and every
isomorphism is a local isometry (`Iso.toLocalIsometry`), so the lemmas about local isometries
carrying the state to the state apply. What an isomorphism carries over, exactly: Born
probabilities (`Iso.bornProb_eq`), the players' state norms (`Iso.stateSqNorm_eq`), the value of a
family of measurements and of a projective strategy pushed forward (`Iso.povmValue_push`,
`Iso.value_pushStrat`, and so the domination of a model by a value, `Iso.dominates`), and the
inconsistency of two families (`Iso.inconsistency_eq`). The exchange of the players is an
operation on projective strategies too (`ProjStrat.swap`), which keeps the value of a game that is
symmetric in the players, and on inconsistencies (`BipartiteModel.inconsistency_swap`).
-/

noncomputable section

namespace MIPRE

open Finset Matrix OperatorMatrix
open scoped InnerProductSpace

universe u u' u''

/-! ## A one-point `ℓ²` sum, exchanged registers, and three `⋆`-algebra isomorphisms of matrices -/

namespace OperatorMatrix

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The `ℓ²` sum over a one-point index `{i₀}` is the space itself. -/
def amplSubsingleton [Subsingleton ι] (i₀ : ι) : Ampl ι H ≃ₗᵢ[ℂ] H where
  toFun v := v i₀
  invFun w := WithLp.toLp 2 fun _ => w
  left_inv v := by
    ext i
    rw [Subsingleton.elim i i₀]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' v := by
    show ‖v i₀‖ = ‖v‖
    rw [PiLp.norm_eq_of_L2, Fintype.sum_subsingleton _ i₀, Real.sqrt_sq (norm_nonneg _)]

@[simp]
theorem amplSubsingleton_apply [Subsingleton ι] (i₀ : ι) (v : Ampl ι H) :
    amplSubsingleton i₀ v = v i₀ := rfl

end OperatorMatrix

/-- Exchanging the two registers of a vector keeps its norm. -/
theorem norm_evec_comp_swap {α β : Type*} [Fintype α] [Fintype β] (e : α × β → ℂ) :
    ‖evec (e ∘ Prod.swap)‖ = ‖evec e‖ := by
  rw [evec, evec, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Fintype.sum_equiv (Equiv.prodComm β α) _ _ fun _ => rfl

section StarAlgEquiv

variable {R S : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [Ring S] [StarRing S] [Algebra ℂ S]

variable (R) in
/-- **One-by-one matrices over a `⋆`-algebra are the algebra.** -/
def matrixUnitStarAlgEquiv : Matrix Unit Unit R ≃⋆ₐ[ℂ] R where
  toFun X := X () ()
  invFun r := Matrix.of fun _ _ => r
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' X Y := by
    show (X * Y) () () = X () () * Y () ()
    rw [Matrix.mul_apply, Fintype.sum_unique]
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem matrixUnitStarAlgEquiv_apply (X : Matrix Unit Unit R) :
    matrixUnitStarAlgEquiv R X = X () () := rfl

variable {α α' : Type*} [Fintype α] [Fintype α']

/-- **Relabelling the rows and columns of square matrices along a bijection**, as a `⋆`-algebra
isomorphism. -/
def submatrixStarAlgEquiv (f : α' ≃ α) : Matrix α α R ≃⋆ₐ[ℂ] Matrix α' α' R :=
  StarAlgEquiv.ofNonUnitalStarAlgHom (submatrixHom f) (submatrixHom f.symm)
    (NonUnitalStarAlgHom.ext fun X => by ext i j; simp)
    (NonUnitalStarAlgHom.ext fun X => by ext i j; simp)

@[simp]
theorem submatrixStarAlgEquiv_apply (f : α' ≃ α) (X : Matrix α α R) :
    submatrixStarAlgEquiv f X = X.submatrix f f := rfl

@[simp]
theorem submatrixStarAlgEquiv_symm_apply (f : α' ≃ α) (X : Matrix α' α' R) :
    (submatrixStarAlgEquiv f).symm X = X.submatrix f.symm f.symm := rfl

variable [DecidableEq α]

/-- **A `⋆`-algebra isomorphism, applied entrywise to square matrices.** -/
def mapMatrixStarAlgEquiv (f : R ≃⋆ₐ[ℂ] S) : Matrix α α R ≃⋆ₐ[ℂ] Matrix α α S :=
  StarAlgEquiv.ofAlgEquiv f.toAlgEquiv.mapMatrix fun X => by
    show (star X).map f = star (X.map f)
    simp only [star_eq_conjTranspose]
    exact conjTranspose_map _ fun a => map_star f a

@[simp]
theorem mapMatrixStarAlgEquiv_apply (f : R ≃⋆ₐ[ℂ] S) (X : Matrix α α R) :
    mapMatrixStarAlgEquiv f X = X.map f := rfl

@[simp]
theorem mapMatrixStarAlgEquiv_symm_apply (f : R ≃⋆ₐ[ℂ] S) (X : Matrix α α S) :
    (mapMatrixStarAlgEquiv f).symm X = X.map f.symm := rfl

end StarAlgEquiv

/-! ## Isomorphisms -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ 𝒞' 𝒜' ℬ' 𝒞'' 𝒜'' ℬ'' : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]
  [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
  [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜'] [Algebra ℂ 𝒜']
  [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']
  [Ring 𝒞''] [StarRing 𝒞''] [Algebra ℂ 𝒞''] [Ring 𝒜''] [StarRing 𝒜''] [Algebra ℂ 𝒜'']
  [Ring ℬ''] [StarRing ℬ''] [Algebra ℂ ℬ'']

/-- **An isomorphism of bipartite models**: a unitary of the Hilbert spaces carrying the state of
`M` to the state of `M'`, and a `⋆`-algebra isomorphism for each player, the two representations
intertwined by the unitary. Everything a model computes from its state and its players' operators
--- Born probabilities, state norms, values, inconsistencies --- is carried across unchanged. -/
structure Iso (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) (M' : BipartiteModel.{u'} 𝒞' 𝒜' ℬ') where
  /-- The unitary of the Hilbert spaces. -/
  W : M.H ≃ₗᵢ[ℂ] M'.H
  /-- The first player's algebras. -/
  ΦA : 𝒜 ≃⋆ₐ[ℂ] 𝒜'
  /-- The second player's algebras. -/
  ΦB : ℬ ≃⋆ₐ[ℂ] ℬ'
  /-- The unitary intertwines the first player's operators with their images. -/
  intertwineA : ∀ (a : 𝒜) (v : M.H), M'.π (M'.πA (ΦA a)) (W v) = W (M.π (M.πA a) v)
  /-- The unitary intertwines the second player's operators with their images. -/
  intertwineB : ∀ (b : ℬ) (v : M.H), M'.π (M'.πB (ΦB b)) (W v) = W (M.π (M.πB b) v)
  /-- The unitary carries the state to the state. -/
  W_ψ : W M.ψ = M'.ψ

namespace Iso

variable {M : BipartiteModel.{u} 𝒞 𝒜 ℬ} {M' : BipartiteModel.{u'} 𝒞' 𝒜' ℬ'}
  {M'' : BipartiteModel.{u''} 𝒞'' 𝒜'' ℬ''}

/-- **The identity isomorphism.** -/
def refl (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) : Iso M M where
  W := LinearIsometryEquiv.refl ℂ M.H
  ΦA := StarAlgEquiv.refl ℂ 𝒜
  ΦB := StarAlgEquiv.refl ℂ ℬ
  intertwineA _ _ := rfl
  intertwineB _ _ := rfl
  W_ψ := rfl

/-- **The inverse isomorphism.** -/
def symm (Φ : Iso M M') : Iso M' M where
  W := Φ.W.symm
  ΦA := Φ.ΦA.symm
  ΦB := Φ.ΦB.symm
  intertwineA a v := Φ.W.injective (by
    rw [← Φ.intertwineA]
    simp only [StarAlgEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply])
  intertwineB b v := Φ.W.injective (by
    rw [← Φ.intertwineB]
    simp only [StarAlgEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply])
  W_ψ := by rw [← Φ.W_ψ, LinearIsometryEquiv.symm_apply_apply]

/-- **Isomorphisms compose**, the first applied first. -/
def trans (Φ : Iso M M') (Φ' : Iso M' M'') : Iso M M'' where
  W := Φ.W.trans Φ'.W
  ΦA := Φ.ΦA.trans Φ'.ΦA
  ΦB := Φ.ΦB.trans Φ'.ΦB
  intertwineA a v := by
    simp only [LinearIsometryEquiv.trans_apply, StarAlgEquiv.trans_apply]
    rw [Φ'.intertwineA, Φ.intertwineA]
  intertwineB b v := by
    simp only [LinearIsometryEquiv.trans_apply, StarAlgEquiv.trans_apply]
    rw [Φ'.intertwineB, Φ.intertwineB]
  W_ψ := by rw [LinearIsometryEquiv.trans_apply, Φ.W_ψ, Φ'.W_ψ]

/-- **The isomorphism with the players exchanged.** -/
def swap (Φ : Iso M M') : Iso M.swap M'.swap where
  W := Φ.W
  ΦA := Φ.ΦB
  ΦB := Φ.ΦA
  intertwineA := Φ.intertwineB
  intertwineB := Φ.intertwineA
  W_ψ := Φ.W_ψ

@[simp]
theorem refl_ΦA (a : 𝒜) : (refl M).ΦA a = a := rfl

@[simp]
theorem refl_ΦB (b : ℬ) : (refl M).ΦB b = b := rfl

@[simp]
theorem symm_W (Φ : Iso M M') : Φ.symm.W = Φ.W.symm := rfl

@[simp]
theorem symm_ΦA (Φ : Iso M M') : Φ.symm.ΦA = Φ.ΦA.symm := rfl

@[simp]
theorem symm_ΦB (Φ : Iso M M') : Φ.symm.ΦB = Φ.ΦB.symm := rfl

@[simp]
theorem trans_W (Φ : Iso M M') (Φ' : Iso M' M'') (v : M.H) :
    (Φ.trans Φ').W v = Φ'.W (Φ.W v) := rfl

@[simp]
theorem trans_ΦA (Φ : Iso M M') (Φ' : Iso M' M'') (a : 𝒜) :
    (Φ.trans Φ').ΦA a = Φ'.ΦA (Φ.ΦA a) := rfl

@[simp]
theorem trans_ΦB (Φ : Iso M M') (Φ' : Iso M' M'') (b : ℬ) :
    (Φ.trans Φ').ΦB b = Φ'.ΦB (Φ.ΦB b) := rfl

@[simp]
theorem swap_W (Φ : Iso M M') : Φ.swap.W = Φ.W := rfl

@[simp]
theorem swap_ΦA (Φ : Iso M M') : Φ.swap.ΦA = Φ.ΦB := rfl

@[simp]
theorem swap_ΦB (Φ : Iso M M') : Φ.swap.ΦB = Φ.ΦA := rfl

@[simp]
theorem symm_symm (Φ : Iso M M') : Φ.symm.symm = Φ := rfl

@[simp]
theorem swap_swap (Φ : Iso M M') : Φ.swap.swap = Φ := rfl

/-- **An isomorphism is a local isometry**, its homomorphisms unital and its isometry carrying the
state to the state (`toLocalIsometry_W_ψ`). -/
def toLocalIsometry (Φ : Iso M M') : LocalIsometry M M' where
  W := Φ.W.toLinearIsometry
  ΦA := Φ.ΦA.toNonUnitalStarAlgHom
  ΦB := Φ.ΦB.toNonUnitalStarAlgHom
  intertwineA := Φ.intertwineA
  intertwineB := Φ.intertwineB

@[simp]
theorem toLocalIsometry_W (Φ : Iso M M') (v : M.H) : Φ.toLocalIsometry.W v = Φ.W v := rfl

@[simp]
theorem toLocalIsometry_ΦA (Φ : Iso M M') (a : 𝒜) : Φ.toLocalIsometry.ΦA a = Φ.ΦA a := rfl

@[simp]
theorem toLocalIsometry_ΦB (Φ : Iso M M') (b : ℬ) : Φ.toLocalIsometry.ΦB b = Φ.ΦB b := rfl

theorem toLocalIsometry_W_ψ (Φ : Iso M M') : Φ.toLocalIsometry.W M.ψ = M'.ψ := Φ.W_ψ

theorem toLocalIsometry_ΦA_one (Φ : Iso M M') : Φ.toLocalIsometry.ΦA 1 = 1 := map_one Φ.ΦA

theorem toLocalIsometry_ΦB_one (Φ : Iso M M') : Φ.toLocalIsometry.ΦB 1 = 1 := map_one Φ.ΦB

@[simp]
theorem swap_toLocalIsometry (Φ : Iso M M') : Φ.swap.toLocalIsometry = Φ.toLocalIsometry.swap :=
  rfl

/-- **A local isometry with inverses is an isomorphism**: an isometry with a right inverse, and
homomorphisms with two-sided inverses, carrying the state to the state. -/
def ofLocalIsometry (Φ : LocalIsometry M M') (hψ : Φ.W M.ψ = M'.ψ) (W' : M'.H → M.H)
    (hW : ∀ v, Φ.W (W' v) = v) (ΨA : 𝒜' → 𝒜) (hA₁ : ∀ a, ΨA (Φ.ΦA a) = a)
    (hA₂ : ∀ a, Φ.ΦA (ΨA a) = a) (ΨB : ℬ' → ℬ) (hB₁ : ∀ b, ΨB (Φ.ΦB b) = b)
    (hB₂ : ∀ b, Φ.ΦB (ΨB b) = b) : Iso M M' where
  W :=
    { toFun := Φ.W
      invFun := W'
      left_inv v := Φ.W.injective (hW (Φ.W v))
      right_inv := hW
      map_add' := Φ.W.map_add
      map_smul' := Φ.W.map_smul
      norm_map' := Φ.W.norm_map }
  ΦA :=
    { toFun := Φ.ΦA
      invFun := ΨA
      left_inv := hA₁
      right_inv := hA₂
      map_mul' := map_mul Φ.ΦA
      map_add' := map_add Φ.ΦA
      map_star' := map_star Φ.ΦA
      map_smul' := map_smul Φ.ΦA }
  ΦB :=
    { toFun := Φ.ΦB
      invFun := ΨB
      left_inv := hB₁
      right_inv := hB₂
      map_mul' := map_mul Φ.ΦB
      map_add' := map_add Φ.ΦB
      map_star' := map_star Φ.ΦB
      map_smul' := map_smul Φ.ΦB }
  intertwineA := Φ.intertwineA
  intertwineB := Φ.intertwineB
  W_ψ := hψ

/-! ### What an isomorphism carries over -/

section Transfer

variable (Φ : Iso M M')

/-- **Born probabilities are carried over.** -/
theorem bornProb_eq (a : 𝒜) (b : ℬ) : M'.bornProb (Φ.ΦA a) (Φ.ΦB b) = M.bornProb a b :=
  LocalIsometry.bornProb_of_W_ψ (Φ := Φ.toLocalIsometry) Φ.W_ψ a b

/-- **The first player's state norms are carried over.** -/
theorem stateSqNorm_eq (a : 𝒜) : M'.stateSqNorm (Φ.ΦA a) = M.stateSqNorm a :=
  LocalIsometry.stateSqNorm_of_W_ψ (Φ := Φ.toLocalIsometry) Φ.W_ψ a

/-- **The second player's state norms are carried over.** -/
theorem swap_stateSqNorm_eq (b : ℬ) : M'.swap.stateSqNorm (Φ.ΦB b) = M.swap.stateSqNorm b :=
  Φ.swap.stateSqNorm_eq b

/-- **The cross norms are carried over.** -/
theorem xSqNorm_eq (a : 𝒜) (b : ℬ) : M'.xSqNorm (Φ.ΦA a) (Φ.ΦB b) = M.xSqNorm a b :=
  LocalIsometry.xSqNorm_of_W_ψ (Φ := Φ.toLocalIsometry) Φ.W_ψ a b

/-- **The state has the norm of the state.** -/
theorem norm_ψ_eq (Φ : Iso M M') : ‖M'.ψ‖ = ‖M.ψ‖ := by
  rw [← Φ.W_ψ, LinearIsometryEquiv.norm_map]

end Transfer

/-! ### Measurements and strategies moved along an isomorphism -/

section PushA

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  (Φ : Iso M M') {X : Type*} [Fintype X]

/-- **A POVM of the first player, moved along the isomorphism.** -/
def pushA (P : POVMIn X 𝒜) : POVMIn X 𝒜' :=
  P.pushforward Φ.toLocalIsometry.ΦA Φ.toLocalIsometry_ΦA_one

@[simp]
theorem pushA_op (P : POVMIn X 𝒜) (x : X) : (Φ.pushA P).op x = Φ.ΦA (P.op x) := rfl

theorem isPVMIn_pushA {P : POVMIn X 𝒜} (hP : IsPVMIn P.op) : IsPVMIn (Φ.pushA P).op :=
  POVMIn.isPVMIn_pushforward _ _ hP

theorem symm_pushA_pushA (P : POVMIn X 𝒜) : Φ.symm.pushA (Φ.pushA P) = P :=
  POVMIn.ext' fun x => Φ.ΦA.symm_apply_apply (P.op x)

theorem pushA_symm_pushA (P : POVMIn X 𝒜') : Φ.pushA (Φ.symm.pushA P) = P :=
  POVMIn.ext' fun x => Φ.ΦA.apply_symm_apply (P.op x)

end PushA

section PushB

variable [PartialOrder ℬ] [StarOrderedRing ℬ] [PartialOrder ℬ'] [StarOrderedRing ℬ']
  (Φ : Iso M M') {X : Type*} [Fintype X]

/-- **A POVM of the second player, moved along the isomorphism.** -/
def pushB (Q : POVMIn X ℬ) : POVMIn X ℬ' :=
  Q.pushforward Φ.toLocalIsometry.ΦB Φ.toLocalIsometry_ΦB_one

@[simp]
theorem pushB_op (Q : POVMIn X ℬ) (x : X) : (Φ.pushB Q).op x = Φ.ΦB (Q.op x) := rfl

theorem isPVMIn_pushB {Q : POVMIn X ℬ} (hQ : IsPVMIn Q.op) : IsPVMIn (Φ.pushB Q).op :=
  POVMIn.isPVMIn_pushforward _ _ hQ

theorem symm_pushB_pushB (Q : POVMIn X ℬ) : Φ.symm.pushB (Φ.pushB Q) = Q :=
  POVMIn.ext' fun x => Φ.ΦB.symm_apply_apply (Q.op x)

theorem pushB_symm_pushB (Q : POVMIn X ℬ') : Φ.pushB (Φ.symm.pushB Q) = Q :=
  POVMIn.ext' fun x => Φ.ΦB.apply_symm_apply (Q.op x)

end PushB

section Value

variable [PartialOrder 𝒜] [PartialOrder ℬ] [PartialOrder 𝒜'] [PartialOrder ℬ'] (Φ : Iso M M')

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- **Two families of measurements whose operators correspond have the same value.** -/
theorem povmValue_eq (G : Game X Y A B) {PA : X → POVMIn A 𝒜} {PB : Y → POVMIn B ℬ}
    {PA' : X → POVMIn A 𝒜'} {PB' : Y → POVMIn B ℬ'}
    (hA : ∀ x a, (PA' x).op a = Φ.ΦA ((PA x).op a))
    (hB : ∀ y b, (PB' y).op b = Φ.ΦB ((PB y).op b)) :
    M'.povmValue G PA' PB' = M.povmValue G PA PB := by
  unfold povmValue condWin
  simp only [hA, hB, Φ.bornProb_eq]

variable [StarOrderedRing 𝒜] [StarOrderedRing ℬ] [StarOrderedRing 𝒜'] [StarOrderedRing ℬ']

/-- **A family of measurements moved along the isomorphism has its value.** -/
theorem povmValue_push (G : Game X Y A B) (PA : X → POVMIn A 𝒜) (PB : Y → POVMIn B ℬ) :
    M'.povmValue G (fun x => Φ.pushA (PA x)) (fun y => Φ.pushB (PB y)) = M.povmValue G PA PB :=
  Φ.povmValue_eq G (fun _ _ => rfl) fun _ _ => rfl

/-- **A projective strategy moved along the isomorphism**: each measurement pushed forward. -/
def pushStrat {G : Game X Y A B} (S : M.ProjStrat G) : M'.ProjStrat G where
  PA x := Φ.pushA (S.PA x)
  PB y := Φ.pushB (S.PB y)
  projA x := Φ.isPVMIn_pushA (S.projA x)
  projB y := Φ.isPVMIn_pushB (S.projB y)
  ψ_unit := Φ.norm_ψ_eq.trans S.ψ_unit

@[simp]
theorem pushStrat_PA {G : Game X Y A B} (S : M.ProjStrat G) (x : X) :
    (Φ.pushStrat S).PA x = Φ.pushA (S.PA x) := rfl

@[simp]
theorem pushStrat_PB {G : Game X Y A B} (S : M.ProjStrat G) (y : Y) :
    (Φ.pushStrat S).PB y = Φ.pushB (S.PB y) := rfl

/-- **A projective strategy moved along the isomorphism has its value.** -/
theorem value_pushStrat {G : Game X Y A B} (S : M.ProjStrat G) :
    (Φ.pushStrat S).value = S.value :=
  Φ.povmValue_push G S.PA S.PB

/-- **A value model dominating a model dominates every model isomorphic to it**: a projective
strategy moves along the isomorphism with its value. -/
theorem dominates (Φ : Iso M M') {ω : ValueModel} (h : ω.Dominates M') : ω.Dominates M :=
  fun G S => (Φ.value_pushStrat S).symm.le.trans (h G (Φ.pushStrat S))

end Value

section Inconsistency

variable [PartialOrder 𝒜] [PartialOrder ℬ] [PartialOrder 𝒜'] [PartialOrder ℬ'] (Φ : Iso M M')
  {Λ X : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype X]

/-- **Two pairs of families whose operators correspond have the same inconsistency.** -/
theorem inconsistency_eq (μ : X → ℝ) {P : X → POVMIn Λ 𝒜} {Q : X → POVMIn Λ ℬ}
    {P' : X → POVMIn Λ 𝒜'} {Q' : X → POVMIn Λ ℬ'} (hP : ∀ x a, (P' x).op a = Φ.ΦA ((P x).op a))
    (hQ : ∀ x b, (Q' x).op b = Φ.ΦB ((Q x).op b)) :
    M'.inconsistency μ P' Q' = M.inconsistency μ P Q := by
  unfold inconsistency
  simp only [hP, hQ, Φ.bornProb_eq]

variable [StarOrderedRing 𝒜] [StarOrderedRing ℬ] [StarOrderedRing 𝒜'] [StarOrderedRing ℬ']

/-- **Two families moved along the isomorphism have their inconsistency.** -/
theorem inconsistency_push (μ : X → ℝ) (P : X → POVMIn Λ 𝒜) (Q : X → POVMIn Λ ℬ) :
    M'.inconsistency μ (fun x => Φ.pushA (P x)) (fun x => Φ.pushB (Q x)) =
      M.inconsistency μ P Q :=
  Φ.inconsistency_eq μ (fun _ _ => rfl) fun _ _ => rfl

end Inconsistency

end Iso

/-! ## Exchanging the players in a strategy and in an inconsistency -/

section Swap

variable [PartialOrder 𝒜] [PartialOrder ℬ] {M : BipartiteModel.{u} 𝒞 𝒜 ℬ}

namespace ProjStrat

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] {G : Game X Y A B}

/-- **A projective strategy with the players exchanged**, as a strategy of the swapped model for
any game `G'` of the exchanged shape: the first player's measurements are the second's. -/
def swap (S : M.ProjStrat G) (G' : Game Y X B A) : M.swap.ProjStrat G' where
  PA := S.PB
  PB := S.PA
  projA := S.projB
  projB := S.projA
  ψ_unit := S.ψ_unit

@[simp]
theorem swap_PA (S : M.ProjStrat G) (G' : Game Y X B A) : (S.swap G').PA = S.PB := rfl

@[simp]
theorem swap_PB (S : M.ProjStrat G) (G' : Game Y X B A) : (S.swap G').PB = S.PA := rfl

/-- **The exchanged strategy has the value of the strategy**, for a game `G'` that is `G` with the
players exchanged: the question pair `(y, x)` weighed as `(x, y)`, and the answers `(b, a)`
accepted as `(a, b)`. For a game symmetric in the players, `G'` is `G` itself. -/
theorem value_swap (S : M.ProjStrat G) {G' : Game Y X B A} (hμ : ∀ x y, G'.μ y x = G.μ x y)
    (hD : ∀ x y a b, G'.D y x b a = G.D x y a b) : (S.swap G').value = S.value := by
  unfold value povmValue condWin
  rw [Finset.sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [hμ]
  congr 1
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [hD, swap_PA, swap_PB, bornProb_swap]

end ProjStrat

/-- **The inconsistency is symmetric in the players**: with the players exchanged, the second
player's family is measured first. -/
theorem inconsistency_swap {Λ X : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype X] (μ : X → ℝ)
    (P : X → POVMIn Λ 𝒜) (Q : X → POVMIn Λ ℬ) :
    M.swap.inconsistency μ Q P = M.inconsistency μ P Q := by
  unfold inconsistency
  refine sum_congr rfl fun x _ => ?_
  congr 1
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  by_cases hab : a = b
  · rw [ite_eq_left hab.symm, ite_eq_left hab]
  · rw [ite_eq_right (Ne.symm hab), ite_eq_right hab, bornProb_swap]

end Swap

/-! ## Isomorphisms between ancilla extensions -/

section Ancilla

variable (M : BipartiteModel.{u} 𝒞 𝒜 ℬ)
variable {α β α' β' : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β']

/-- **An extension by one-point registers in the state `1` is the model itself**: the one-by-one
matrices over each player's algebra are that algebra. -/
def expandUnit : Iso (M.expand fun _ : Unit × Unit => (1 : ℂ)) M where
  W := (M.ampl _).trans (amplSubsingleton ((), ()))
  ΦA := matrixUnitStarAlgEquiv 𝒜
  ΦB := matrixUnitStarAlgEquiv ℬ
  intertwineA X v := by
    simp only [LinearIsometryEquiv.trans_apply, amplSubsingleton_apply,
      matrixUnitStarAlgEquiv_apply]
    rw [expand_π_πA_apply, Fintype.sum_unique]
  intertwineB Y v := by
    simp only [LinearIsometryEquiv.trans_apply, amplSubsingleton_apply,
      matrixUnitStarAlgEquiv_apply]
    rw [expand_π_πB_apply, Fintype.sum_unique]
  W_ψ := by
    rw [LinearIsometryEquiv.trans_apply, amplSubsingleton_apply, expand_ψ_apply, one_smul]

@[simp]
theorem expandUnit_ΦA (X : Matrix Unit Unit 𝒜) : (M.expandUnit).ΦA X = X () () := rfl

@[simp]
theorem expandUnit_ΦB (Y : Matrix Unit Unit ℬ) : (M.expandUnit).ΦB Y = Y () () := rfl

/-- **Associativity, as an isomorphism**: the extension in `e'` of the extension in `e` is the
extension by the product registers, in the product vector `e''` (`BipartiteModel.assoc`). -/
def assocIso (e : α × β → ℂ) (e' : α' × β' → ℂ) (e'' : (α' × α) × (β' × β) → ℂ)
    (he : ∀ q, e'' q = e' (q.1.1, q.2.1) * e (q.1.2, q.2.2)) :
    Iso ((M.expand e).expand e') (M.expand e'') :=
  Iso.ofLocalIsometry (M.assoc e e' e'') (M.assoc_W_ψ e e' e'' he)
    (fun w => ((M.expand e).ampl e').symm (WithLp.toLp 2 fun p' => (M.ampl e).symm
      (WithLp.toLp 2 fun p => M.ampl e'' w ((p'.1, p.1), (p'.2, p.2)))))
    (fun _ => M.expand_ext e'' fun _ => rfl)
    uncompHom uncompHom_compHom compHom_uncompHom uncompHom uncompHom_compHom compHom_uncompHom

@[simp]
theorem assocIso_ΦA (e : α × β → ℂ) (e' : α' × β' → ℂ) (e'' : (α' × α) × (β' × β) → ℂ)
    (he : ∀ q, e'' q = e' (q.1.1, q.2.1) * e (q.1.2, q.2.2)) (a : Matrix α' α' (Matrix α α 𝒜)) :
    (M.assocIso e e' e'' he).ΦA a = compHom a := rfl

@[simp]
theorem assocIso_ΦB (e : α × β → ℂ) (e' : α' × β' → ℂ) (e'' : (α' × α) × (β' × β) → ℂ)
    (he : ∀ q, e'' q = e' (q.1.1, q.2.1) * e (q.1.2, q.2.2)) (b : Matrix β' β' (Matrix β β ℬ)) :
    (M.assocIso e e' e'' he).ΦB b = compHom b := rfl

/-- **The exchange of the players, as an isomorphism**: the exchanged extension in `e` is the
extension of the exchanged model in the exchanged vector (`BipartiteModel.swapExpand`). -/
def swapExpandIso (e : α × β → ℂ) : Iso (M.expand e).swap (M.swap.expand (e ∘ Prod.swap)) :=
  Iso.ofLocalIsometry (M.swapExpand e (e ∘ Prod.swap)) (M.swapExpand_W_ψ e _ fun _ => rfl)
    (fun w => (M.ampl e).symm (WithLp.toLp 2 fun p => M.swap.ampl (e ∘ Prod.swap) w p.swap))
    (fun _ => M.swap.expand_ext _ fun _ => rfl)
    id (fun _ => rfl) (fun _ => rfl) id (fun _ => rfl) (fun _ => rfl)

@[simp]
theorem swapExpandIso_ΦA (e : α × β → ℂ) (b : Matrix β β ℬ) : (M.swapExpandIso e).ΦA b = b :=
  rfl

@[simp]
theorem swapExpandIso_ΦB (e : α × β → ℂ) (a : Matrix α α 𝒜) : (M.swapExpandIso e).ΦB a = a :=
  rfl

/-- **A relabelling of the registers, as an isomorphism**, along bijections `f` and `g`, from the
extension in `e` to the extension in the relabelled vector `e'` (`BipartiteModel.relabel`). -/
def relabelIso (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β)
    (he : ∀ p, e' p = e (f p.1, g p.2)) : Iso (M.expand e) (M.expand e') :=
  Iso.ofLocalIsometry (M.relabel e e' f g) (M.relabel_W_ψ e e' f g he)
    (M.relabelIsometry e' e f.symm g.symm)
    (fun w => M.expand_ext e' fun p => by
      show M.ampl e' (M.relabelIsometry e e' f g (M.relabelIsometry e' e f.symm g.symm w)) p = _
      rw [ampl_relabelIsometry, ampl_relabelIsometry, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply])
    (submatrixHom f.symm) (fun X => by ext i j; simp) (fun X => by ext i j; simp)
    (submatrixHom g.symm) (fun Y => by ext i j; simp) (fun Y => by ext i j; simp)

@[simp]
theorem relabelIso_ΦA (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β)
    (he : ∀ p, e' p = e (f p.1, g p.2)) (a : Matrix α α 𝒜) :
    (M.relabelIso e e' f g he).ΦA a = a.submatrix f f := rfl

@[simp]
theorem relabelIso_ΦB (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β)
    (he : ∀ p, e' p = e (f p.1, g p.2)) (b : Matrix β β ℬ) :
    (M.relabelIso e e' f g he).ΦB b = b.submatrix g g := rfl

end Ancilla

namespace Iso

variable {M : BipartiteModel.{u} 𝒞 𝒜 ℬ} {M' : BipartiteModel.{u'} 𝒞' 𝒜' ℬ'}
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The unitary of an isomorphism, acting on each component of an `ℓ²` sum. -/
def expandCongrW (Φ : Iso M M') (e : α × β → ℂ) : (M.expand e).H ≃ₗᵢ[ℂ] (M'.expand e).H :=
  (M.ampl e).trans ((LinearIsometryEquiv.piLpCongrRight 2 fun _ : α × β => Φ.W).trans
    (M'.ampl e).symm)

theorem ampl_expandCongrW (Φ : Iso M M') (e : α × β → ℂ) (v : (M.expand e).H) (p : α × β) :
    M'.ampl e (Φ.expandCongrW e v) p = Φ.W (M.ampl e v p) := rfl

/-- **An isomorphism extends to the extensions by the same registers in the same state**: the
unitary acts on each component, and each player's isomorphism entrywise. -/
def expandCongr (Φ : Iso M M') (e : α × β → ℂ) : Iso (M.expand e) (M'.expand e) where
  W := Φ.expandCongrW e
  ΦA := mapMatrixStarAlgEquiv Φ.ΦA
  ΦB := mapMatrixStarAlgEquiv Φ.ΦB
  intertwineA X v := M'.expand_ext e fun p => by
    simp only [expand_π_πA_apply, ampl_expandCongrW, map_sum, mapMatrixStarAlgEquiv_apply,
      Matrix.map_apply, Φ.intertwineA]
  intertwineB Y v := M'.expand_ext e fun p => by
    simp only [expand_π_πB_apply, ampl_expandCongrW, map_sum, mapMatrixStarAlgEquiv_apply,
      Matrix.map_apply, Φ.intertwineB]
  W_ψ := M'.expand_ext e fun p => by
    simp only [ampl_expandCongrW, expand_ψ_apply, map_smul, Φ.W_ψ]

@[simp]
theorem expandCongr_ΦA (Φ : Iso M M') (e : α × β → ℂ) (X : Matrix α α 𝒜) :
    (Φ.expandCongr e).ΦA X = X.map Φ.ΦA := rfl

@[simp]
theorem expandCongr_ΦB (Φ : Iso M M') (e : α × β → ℂ) (Y : Matrix β β ℬ) :
    (Φ.expandCongr e).ΦB Y = Y.map Φ.ΦB := rfl

end Iso

/-! ## Isomorphisms of tensor-product models -/

section Tensor

variable {dA dB dA' dB' α β : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype dA'] [DecidableEq dA'] [Fintype dB'] [DecidableEq dB'] [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- **The extension of a tensor-product model is the tensor-product model of the expanded vector**,
as an isomorphism (`BipartiteModel.tensorExpand`, inverted by `tensorUnexpand`). -/
def tensorExpandIso (ξ : dA × dB → ℂ) (e : α × β → ℂ) :
    Iso ((tensor ξ).expand e) (tensor (expVec e ξ)) :=
  Iso.ofLocalIsometry (tensorExpand ξ e) (tensorExpand_W_ψ ξ e) (unflattenIsometry ξ e)
    (flattenIsometry_unflattenIsometry ξ e) compSymmHom (fun _ => by ext; rfl)
    compHom_compSymmHom compSymmHom (fun _ => by ext; rfl) compHom_compSymmHom

@[simp]
theorem tensorExpandIso_ΦA (ξ : dA × dB → ℂ) (e : α × β → ℂ) (X : Matrix α α (Matrix dA dA ℂ)) :
    (tensorExpandIso ξ e).ΦA X = compHom X := rfl

@[simp]
theorem tensorExpandIso_ΦB (ξ : dA × dB → ℂ) (e : α × β → ℂ) (Y : Matrix β β (Matrix dB dB ℂ)) :
    (tensorExpandIso ξ e).ΦB Y = compHom Y := rfl

/-- The unitary of `ℂ^{dA × dB}` onto `ℂ^{dA' × dB'}` relabelling the two factors. -/
def tensorReindexW (f : dA ≃ dA') (g : dB ≃ dB') (ψ : dA × dB → ℂ) :
    (tensor ψ).H ≃ₗᵢ[ℂ] (tensor (ψ ∘ Prod.map f.symm g.symm)).H :=
  (euclid ψ).trans ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (f.prodCongr g)).trans
    (euclid (ψ ∘ Prod.map f.symm g.symm)).symm)

theorem tensorReindexW_apply (f : dA ≃ dA') (g : dB ≃ dB') (ψ : dA × dB → ℂ)
    (v : (tensor ψ).H) (q : dA' × dB') :
    WithLp.ofLp (tensorReindexW f g ψ v) q = WithLp.ofLp v (f.symm q.1, g.symm q.2) :=
  rfl

/-- **A tensor-product model is unchanged by relabelling its two factors**: along bijections
`f : dA ≃ dA'` and `g : dB ≃ dB'`, the model of `ψ` is the model of `ψ` relabelled, each player's
matrices relabelled along their factor. -/
def tensorReindexIso (f : dA ≃ dA') (g : dB ≃ dB') (ψ : dA × dB → ℂ) :
    Iso (tensor ψ) (tensor (ψ ∘ Prod.map f.symm g.symm)) where
  W := tensorReindexW f g ψ
  ΦA := submatrixStarAlgEquiv f.symm
  ΦB := submatrixStarAlgEquiv g.symm
  intertwineA X v := by
    refine PiLp.ext fun q => ?_
    show WithLp.ofLp ((tensor (ψ ∘ Prod.map f.symm g.symm)).π (aOp (X.submatrix f.symm f.symm))
      (tensorReindexW f g ψ v)) q = WithLp.ofLp (tensorReindexW f g ψ ((tensor ψ).π (aOp X) v)) q
    rw [tensor_π_apply, tensorReindexW_apply, tensor_π_apply]
    refine Fintype.sum_equiv ((f.prodCongr g).symm) _ _ fun ⟨j₁, j₂⟩ => ?_
    rw [tensorReindexW_apply]
    simp [aOp, Matrix.one_apply, g.symm.injective.eq_iff]
  intertwineB Y v := by
    refine PiLp.ext fun q => ?_
    show WithLp.ofLp ((tensor (ψ ∘ Prod.map f.symm g.symm)).π (bOp (Y.submatrix g.symm g.symm))
      (tensorReindexW f g ψ v)) q = WithLp.ofLp (tensorReindexW f g ψ ((tensor ψ).π (bOp Y) v)) q
    rw [tensor_π_apply, tensorReindexW_apply, tensor_π_apply]
    refine Fintype.sum_equiv ((f.prodCongr g).symm) _ _ fun ⟨j₁, j₂⟩ => ?_
    rw [tensorReindexW_apply]
    simp [bOp, Matrix.one_apply, f.symm.injective.eq_iff]
  W_ψ := by
    refine PiLp.ext fun q => ?_
    rw [tensorReindexW_apply]
    rfl

@[simp]
theorem tensorReindexIso_ΦA (f : dA ≃ dA') (g : dB ≃ dB') (ψ : dA × dB → ℂ)
    (X : Matrix dA dA ℂ) : (tensorReindexIso f g ψ).ΦA X = X.submatrix f.symm f.symm := rfl

@[simp]
theorem tensorReindexIso_ΦB (f : dA ≃ dA') (g : dB ≃ dB') (ψ : dA × dB → ℂ)
    (Y : Matrix dB dB ℂ) : (tensorReindexIso f g ψ).ΦB Y = Y.submatrix g.symm g.symm := rfl

end Tensor

end BipartiteModel

end MIPRE

end

end
