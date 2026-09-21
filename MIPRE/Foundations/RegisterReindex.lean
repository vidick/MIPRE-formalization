/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.POVMValue
import MIPRE.Foundations.Distances
import MIPRE.Foundations.PVM

/-!
# Reindexing the registers of a bipartite strategy

`TensorProductStrategy` (blueprint `def:tensor-strategy`) fixes the two players' registers to be
`Fin dA` and `Fin dB`, and every soundness theorem proved through the vendored developments ---
`MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL` in particular --- takes and returns its
strategies in that form. The rigidity arguments of `MIPRE.QLD`, on the other hand, build their
states and measurements on *structured* registers: a strategy's own space tensored with ancillas
such as `(dA × Anc F m) × (F × F)`, where the block structure is what the proofs compute with. A
strategy in that form has a value (`povmValue`), but it is not a `TensorProductStrategy`, and
nothing in the repository turned one into the other. This file is that bridge.

Everything transports along an equivalence `e : d ≃ d'` of a register:

* `reindexStarAlgEquiv e` is `Matrix.reindex e e` as a star-algebra equivalence, so that
  `ProjectiveMeasurement.map` moves projective measurement families across it;
* `POVM.reindex e` moves POVMs, and commutes with the relabelling `POVM.map`
  (`POVM.map_reindex`) and with `ProjectiveMeasurement.toPOVM`
  (`ProjectiveMeasurement.toPOVM_map_reindex`);
* `reindexVec eA eB` moves a bipartite state, and the Born rule is invariant
  (`quadForm_reindex`, `bornProb_reindex`), hence so are `povmValue` (`povmValue_reindex`) and
  `inconsistency` (`inconsistency_reindex`).

`TensorProductStrategy.ofProjective` then packages a projective strategy on arbitrary finite
registers as a `TensorProductStrategy` on `Fin (card dA) × Fin (card dB)`, with
`TensorProductStrategy.value_ofProjective` identifying its value with the `povmValue` of the
original; `TensorProductStrategy.ofPVM` is the same for measurements given as POVM families with
`IsPVM` proofs, the form the rigidity arguments produce. A consumer applies a soundness theorem to
the packaged strategy and reads the conclusion back through `inconsistency_reindex` and the
`reindex` lemmas: `MIPRE.Background.LIDT.Adapter.Registers` does exactly that for the seeded
low individual degree test.
-/

namespace MIPRE

open Matrix Kronecker
open scoped ComplexOrder MatrixOrder

/-! ## The matrix algebra of a reindexed register -/

section StarAlgEquiv

variable {d d' : Type*} [Fintype d] [Fintype d'] [DecidableEq d] [DecidableEq d']

/-- `Matrix.reindex e e` as a star-algebra equivalence of the two matrix algebras. -/
def reindexStarAlgEquiv (e : d ≃ d') : Matrix d d ℂ ≃⋆ₐ[ℂ] Matrix d' d' ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ e) fun M => by
    simp [Matrix.star_eq_conjTranspose]

@[simp] theorem reindexStarAlgEquiv_apply (e : d ≃ d') (M : Matrix d d ℂ) :
    reindexStarAlgEquiv e M = Matrix.reindex e e M := rfl

end StarAlgEquiv

/-! ## Reindexing POVMs and projective measurement families -/

section POVM

variable {A : Type*} [Fintype A]
variable {d d' : Type*} [Fintype d] [Fintype d'] [DecidableEq d] [DecidableEq d']

/-- Reindex a POVM along an equivalence of its register. -/
def POVM.reindex (e : d ≃ d') (M : POVM A d) : POVM A d' where
  mats a := ⟨Matrix.reindex e e (M.mats a).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
      ← Matrix.star_eq_conjTranspose, selfAdjoint.mem_iff.mp (M.mats a).prop]⟩
  nonneg a := by
    have h : (Matrix.reindex e e (M.mats a).val).PosSemidef := by
      rw [Matrix.reindex_apply]
      exact (M.posSemidef a).submatrix _
    exact Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr h)
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, Matrix.reindex e e (M.mats a).val = 1
    have h : ∑ a, Matrix.reindex e e (M.mats a).val
        = Matrix.reindex e e (∑ a, (M.mats a).val) :=
      (map_sum (Matrix.reindexLinearEquiv ℂ ℂ e e) _ _).symm
    rw [h, POVM.sum_val, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

@[simp] theorem POVM.reindex_mats (e : d ≃ d') (M : POVM A d) (a : A) :
    ((M.reindex e).mats a).val = Matrix.reindex e e (M.mats a).val := rfl

/-- Reindexing there and back is the identity. -/
theorem POVM.reindex_reindex_symm (e : d ≃ d') (M : POVM A d) :
    (M.reindex e).reindex e.symm = M :=
  POVM.ext' fun a => by
    rw [POVM.reindex_mats, POVM.reindex_mats, ← Matrix.reindex_symm, Equiv.symm_apply_apply]

/-- Reindexing back and forth is the identity, in the other order. -/
theorem POVM.reindex_symm_reindex (e : d ≃ d') (M : POVM A d') :
    (M.reindex e.symm).reindex e = M :=
  POVM.ext' fun a => by
    rw [POVM.reindex_mats, POVM.reindex_mats, ← Matrix.reindex_symm, Equiv.apply_symm_apply]

/-- Reindexing the register commutes with relabelling the outcomes. -/
theorem POVM.map_reindex {B : Type*} [Fintype B] [DecidableEq B] (e : d ≃ d') (f : A → B)
    (M : POVM A d) : (M.map f).reindex e = (M.reindex e).map f :=
  POVM.ext' fun b => by
    rw [POVM.reindex_mats, POVM.map_mats, POVM.map_mats]
    simp only [POVM.reindex_mats]
    exact map_sum (Matrix.reindexLinearEquiv ℂ ℂ e e) _ _

/-- The POVM of a projective measurement family transported along `reindexStarAlgEquiv e`
is the reindexed POVM. -/
theorem ProjectiveMeasurement.toPOVM_map_reindex {X : Type*} [Fintype X] (e : d ≃ d')
    (P : ProjectiveMeasurement X A (Matrix d d ℂ)) (x : X) :
    (P.map (reindexStarAlgEquiv e)).toPOVM x = (P.toPOVM x).reindex e :=
  POVM.ext' fun _ => rfl

/-- A family of POVMs whose elements are projective, as a `ProjectiveMeasurement`. This is the
form the rigidity arguments produce their measurements in (`IsPVM` on the bare matrices), and
`TensorProductStrategy` consumes the bundled form. -/
def ProjectiveMeasurement.ofIsPVM {X : Type*} (M : X → POVM A d)
    (h : ∀ x, IsPVM fun a => ((M x).mats a).val) :
    ProjectiveMeasurement X A (Matrix d d ℂ) where
  M x a := ((M x).mats a).val
  selfAdjoint x a := by rw [Matrix.star_eq_conjTranspose]; exact (h x).isSelfAdjoint a
  projective x a := (h x).idem a
  normalized x := (h x).sum_eq_one

@[simp] theorem ProjectiveMeasurement.toPOVM_ofIsPVM {X : Type*} [Fintype X] (M : X → POVM A d)
    (h : ∀ x, IsPVM fun a => ((M x).mats a).val) (x : X) :
    (ProjectiveMeasurement.ofIsPVM M h).toPOVM x = M x :=
  POVM.ext' fun _ => rfl

end POVM

/-! ## Reindexing a bipartite state, and the invariance of the Born rule -/

section State

variable {dA dB dA' dB' : Type*}

/-- Reindex a bipartite state along equivalences of the two registers. -/
def reindexVec (eA : dA ≃ dA') (eB : dB ≃ dB') (ψ : dA × dB → ℂ) : dA' × dB' → ℂ :=
  ψ ∘ (Equiv.prodCongr eA eB).symm

theorem reindexVec_apply (eA : dA ≃ dA') (eB : dB ≃ dB') (ψ : dA × dB → ℂ)
    (p : dA' × dB') : reindexVec eA eB ψ p = ψ (eA.symm p.1, eB.symm p.2) := rfl

/-- The Kronecker product of two reindexed matrices is the reindexing of the Kronecker product
along the product equivalence. -/
theorem reindex_kronecker_reindex (eA : dA ≃ dA') (eB : dB ≃ dB') (M : Matrix dA dA ℂ)
    (N : Matrix dB dB ℂ) :
    Matrix.reindex eA eA M ⊗ₖ Matrix.reindex eB eB N
      = Matrix.reindex (Equiv.prodCongr eA eB) (Equiv.prodCongr eA eB) (M ⊗ₖ N) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, kroneckerMap_apply]

variable [Fintype dA] [Fintype dB] [Fintype dA'] [Fintype dB']

/-- **The Born rule is invariant under reindexing.** -/
theorem quadForm_reindex (eA : dA ≃ dA') (eB : dB ≃ dB') (ψ : dA × dB → ℂ)
    (M : Matrix dA dA ℂ) (N : Matrix dB dB ℂ) :
    star (reindexVec eA eB ψ) ⬝ᵥ
        ((Matrix.reindex eA eA M ⊗ₖ Matrix.reindex eB eB N) *ᵥ reindexVec eA eB ψ)
      = star ψ ⬝ᵥ ((M ⊗ₖ N) *ᵥ ψ) := by
  set E := Equiv.prodCongr eA eB with hE
  rw [reindex_kronecker_reindex, reindexVec, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  have hcomp : (ψ ∘ E.symm) ∘ E.symm.symm = ψ := by
    rw [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  rw [hcomp]
  show ∑ p, star ψ (E.symm p) * ((M ⊗ₖ N) *ᵥ ψ) (E.symm p)
    = ∑ p, star ψ p * ((M ⊗ₖ N) *ᵥ ψ) p
  exact Equiv.sum_comp E.symm fun p => star ψ p * ((M ⊗ₖ N) *ᵥ ψ) p

/-- A reindexed unit vector is a unit vector. -/
theorem reindexVec_unit (eA : dA ≃ dA') (eB : dB ≃ dB') {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) : star (reindexVec eA eB ψ) ⬝ᵥ reindexVec eA eB ψ = 1 := by
  rw [← hψ]
  exact Equiv.sum_comp (Equiv.prodCongr eA eB).symm fun p => star ψ p * ψ p

theorem bornProb_reindex (eA : dA ≃ dA') (eB : dB ≃ dB') (ψ : dA × dB → ℂ)
    (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) :
    bornProb (reindexVec eA eB ψ) (Matrix.reindex eA eA EA) (Matrix.reindex eB eB EB)
      = bornProb ψ EA EB := by
  rw [bornProb, bornProb, quadForm_reindex]

variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dA'] [DecidableEq dB']
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- **The value of a strategy is invariant under reindexing its registers.** -/
theorem povmValue_reindex (eA : dA ≃ dA') (eB : dB ≃ dB') (G : Game X Y A B)
    (ψ : dA × dB → ℂ) (MA : X → POVM A dA) (MB : Y → POVM B dB) :
    povmValue G (reindexVec eA eB ψ) (fun x => (MA x).reindex eA) (fun y => (MB y).reindex eB)
      = povmValue G ψ MA MB := by
  unfold povmValue condWin
  simp only [POVM.reindex_mats, bornProb_reindex]

/-- **Inconsistency is invariant under reindexing the registers.** -/
theorem inconsistency_reindex [DecidableEq A] (eA : dA ≃ dA') (eB : dB ≃ dB') (μ : X → ℝ)
    (ψ : dA × dB → ℂ) (M : X → POVM A dA) (N : X → POVM A dB) :
    inconsistency μ (reindexVec eA eB ψ) (fun x => (M x).reindex eA) (fun x => (N x).reindex eB)
      = inconsistency μ ψ M N := by
  unfold inconsistency
  simp only [POVM.reindex_mats, quadForm_reindex]

end State

/-! ## A projective strategy on arbitrary registers, as a `TensorProductStrategy` -/

section Strategy

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **`TensorProductStrategy.value` is the `povmValue` of the strategy's own measurements**, read
as POVMs. -/
theorem TensorProductStrategy.value_eq_povmValue {G : Game X Y A B}
    (S : TensorProductStrategy G) :
    S.value = povmValue G S.ψ (fun x => S.PA.toPOVM x) (fun y => S.PB.toPOVM y) := by
  unfold TensorProductStrategy.value povmValue condWin bornProb
  simp only [Finset.mul_sum, mul_assoc]
  rfl

/-- A projective strategy on arbitrary finite registers `dA`, `dB`, packaged as a
`TensorProductStrategy` on `Fin (card dA) × Fin (card dB)` along `Fintype.equivFin`. -/
noncomputable def TensorProductStrategy.ofProjective (G : Game X Y A B) (ψ : dA × dB → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (PA : ProjectiveMeasurement X A (Matrix dA dA ℂ))
    (PB : ProjectiveMeasurement Y B (Matrix dB dB ℂ)) : TensorProductStrategy G where
  dA := Fintype.card dA
  dB := Fintype.card dB
  ψ := reindexVec (Fintype.equivFin dA) (Fintype.equivFin dB) ψ
  ψ_unit := reindexVec_unit _ _ hψ
  PA := PA.map (reindexStarAlgEquiv (Fintype.equivFin dA))
  PB := PB.map (reindexStarAlgEquiv (Fintype.equivFin dB))

/-- **The packaged strategy has the value of the original.** The two sides agree definitionally
once `TensorProductStrategy.value` is read as a `povmValue`: the packaged state is the reindexed
state and the packaged measurements are the reindexed POVMs. -/
theorem TensorProductStrategy.value_ofProjective (G : Game X Y A B) (ψ : dA × dB → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (PA : ProjectiveMeasurement X A (Matrix dA dA ℂ))
    (PB : ProjectiveMeasurement Y B (Matrix dB dB ℂ)) :
    (TensorProductStrategy.ofProjective G ψ hψ PA PB).value
      = povmValue G ψ (fun x => PA.toPOVM x) (fun y => PB.toPOVM y) := by
  rw [TensorProductStrategy.value_eq_povmValue]
  exact povmValue_reindex (Fintype.equivFin dA) (Fintype.equivFin dB) G ψ
    (fun x => PA.toPOVM x) (fun y => PB.toPOVM y)

/-- A strategy given by POVM families with projective elements, packaged as a
`TensorProductStrategy`. -/
noncomputable def TensorProductStrategy.ofPVM (G : Game X Y A B) (ψ : dA × dB → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (MA : X → POVM A dA) (MB : Y → POVM B dB)
    (hA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hB : ∀ y, IsPVM fun b => ((MB y).mats b).val) : TensorProductStrategy G :=
  TensorProductStrategy.ofProjective G ψ hψ (ProjectiveMeasurement.ofIsPVM MA hA)
    (ProjectiveMeasurement.ofIsPVM MB hB)

theorem TensorProductStrategy.value_ofPVM (G : Game X Y A B) (ψ : dA × dB → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (MA : X → POVM A dA) (MB : Y → POVM B dB)
    (hA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hB : ∀ y, IsPVM fun b => ((MB y).mats b).val) :
    (TensorProductStrategy.ofPVM G ψ hψ MA MB hA hB).value = povmValue G ψ MA MB := by
  rw [TensorProductStrategy.ofPVM, TensorProductStrategy.value_ofProjective]
  simp only [ProjectiveMeasurement.toPOVM_ofIsPVM]

end Strategy

end MIPRE
