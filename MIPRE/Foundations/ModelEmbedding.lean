/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.ModelReading

@[expose] public section

/-!
# Embeddings of bipartite models

A local isometry (`BipartiteModel.LocalIsometry`) that carries the state to the state and keeps
both players' units is an **embedding** of bipartite models (`BipartiteModel.Embedding`): the model
form of "adjoin ancilla registers in fixed vectors", and of the reduced isometry of the soundness
analysis of the Pauli basis test. New in Phase 5 of `planning/mipco-track.md`, where that analysis
is stated in a bipartite model; there the matrix statements that a quantity is unchanged when
registers in fixed vectors are adjoined, regrouped or read across the cut become transfers along
an embedding.

* An embedding carries every quantity computed from the state and the players' operators: Born
  probabilities (`Embedding.bornProb`), the players' state norms (`Embedding.stateSqNorm`,
  `Embedding.swap_stateSqNorm`), cross norms (`Embedding.xSqNorm`), and, being unital, the value
  and the inconsistency of families of measurements pushed forward
  (`Embedding.povmValue_pushforward`, `Embedding.inconsistency_pushforward`). A sum of products of
  the two players' operators keeps its state norm and quadratic form along any local isometry
  carrying the state to the state (`LocalIsometry.snorm_sum_mul_of_W_ψ`,
  `LocalIsometry.qform_sum_mul_of_W_ψ`).
* Embeddings compose (`Embedding.comp`), exchange with the players (`Embedding.swap`), and every
  isomorphism is one (`Iso.toEmbedding`). The local isometries between extensions of
  `MIPRE/Foundations/AncillaIsometry.lean` are embeddings once their state conditions hold
  (`inertEmb`, `assocEmb`, `relabelEmb`, `swapExpandEmb`), and so is the change of cut of
  `MIPRE/Foundations/ModelReading.lean` (`recutEmb`).
* Two local isometries with no state condition: the same maps into the target with its state
  replaced (`LocalIsometry.toWithState`), and the conjugation of a model by a unitary of each
  player (`LocalIsometry.ofUnitary`), a local isometry because the two players' operators
  commute.
* Relabelling the outcomes of both families along one bijection keeps their inconsistency
  (`BipartiteModel.inconsistency_map_equiv`), and pushing a POVM forward along a composite is
  pushing it forward twice (`POVMIn.pushforward_comp`).
-/

noncomputable section

namespace MIPRE

open Finset Matrix OperatorMatrix
open scoped InnerProductSpace

universe u u' u''

/-! ## Pushing a POVM forward along a composite -/

section Pushforward

variable {R S T : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [PartialOrder R] [StarOrderedRing R]
  [Ring S] [StarRing S] [Algebra ℂ S] [PartialOrder S] [StarOrderedRing S]
  [Ring T] [StarRing T] [Algebra ℂ T] [PartialOrder T] [StarOrderedRing T] {X : Type*} [Fintype X]

/-- **Pushing a POVM forward along a composite is pushing it forward twice.** -/
theorem POVMIn.pushforward_comp (g : S →⋆ₙₐ[ℂ] T) (hg : g 1 = 1) (f : R →⋆ₙₐ[ℂ] S)
    (hf : f 1 = 1) (P : POVMIn X R) :
    P.pushforward (g.comp f) (by rw [NonUnitalStarAlgHom.comp_apply, hf, hg]) =
      (P.pushforward f hf).pushforward g hg :=
  POVMIn.ext' fun _ => rfl

end Pushforward

namespace BipartiteModel

variable {𝒞 𝒜 ℬ 𝒞' 𝒜' ℬ' 𝒞'' 𝒜'' ℬ'' : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]
  [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
  [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜'] [Algebra ℂ 𝒜']
  [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']
  [Ring 𝒞''] [StarRing 𝒞''] [Algebra ℂ 𝒞''] [Ring 𝒜''] [StarRing 𝒜''] [Algebra ℂ 𝒜'']
  [Ring ℬ''] [StarRing ℬ''] [Algebra ℂ ℬ'']

/-! ## Relabelling the outcomes of two families along one bijection -/

section Relabel

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- The effect of an outcome of a POVM relabelled along a bijection is the effect of its
preimage. -/
private theorem map_equiv_op' {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] {Λ Λ' : Type*} [Fintype Λ] [Fintype Λ'] [DecidableEq Λ'] (e : Λ ≃ Λ')
    (P : POVMIn Λ R) (c : Λ') : (P.map e).op c = P.op (e.symm c) := by
  have h : Finset.univ.filter (fun a => e a = c) = {e.symm c} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Equiv.eq_symm_apply]
  rw [POVMIn.map_op, h, Finset.sum_singleton]

/-- **Relabelling the outcomes of both families along one bijection keeps their
inconsistency.** -/
theorem inconsistency_map_equiv (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) {Λ Λ' X : Type*} [Fintype Λ]
    [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ'] [Fintype X] (e : Λ ≃ Λ') (μ : X → ℝ)
    (P : X → POVMIn Λ 𝒜) (Q : X → POVMIn Λ ℬ) :
    M.inconsistency μ (fun x => (P x).map e) (fun x => (Q x).map e) = M.inconsistency μ P Q := by
  unfold inconsistency
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp only [map_equiv_op']
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Equiv.symm_apply_apply, e.injective.eq_iff]

end Relabel

/-- The product of a unitary of each player is represented by an isometry: `(U V)* (U V) = 1`
needs only `U* U = 1` and `V* V = 1`. -/
theorem star_πA_mul_πB_mul_self (N : BipartiteModel.{u} 𝒞 𝒜 ℬ) {U : 𝒜} {V : ℬ}
    (hU : star U * U = 1) (hV : star V * V = 1) :
    star (N.πA U * N.πB V) * (N.πA U * N.πB V) = 1 := by
  rw [star_mul, ← map_star, ← map_star, mul_assoc, ← mul_assoc (N.πA (star U)), ← map_mul, hU,
    map_one, one_mul, ← map_mul, hV, map_one]

/-! ## Three facts about local isometries -/

namespace LocalIsometry

variable {M : BipartiteModel.{u} 𝒞 𝒜 ℬ} {M' : BipartiteModel.{u'} 𝒞' 𝒜' ℬ'}

/-- **A local isometry into a model with its state replaced**: the same isometry and
homomorphisms, the target's state playing no part in a local isometry. -/
def toWithState (Φ : LocalIsometry M M') (φ : M'.H) : LocalIsometry M (M'.withState φ) where
  W := Φ.W
  ΦA := Φ.ΦA
  ΦB := Φ.ΦB
  intertwineA := Φ.intertwineA
  intertwineB := Φ.intertwineB

@[simp]
theorem toWithState_W (Φ : LocalIsometry M M') (φ : M'.H) (v : M.H) :
    (Φ.toWithState φ).W v = Φ.W v := rfl

@[simp]
theorem toWithState_ΦA (Φ : LocalIsometry M M') (φ : M'.H) (a : 𝒜) :
    (Φ.toWithState φ).ΦA a = Φ.ΦA a := rfl

@[simp]
theorem toWithState_ΦB (Φ : LocalIsometry M M') (φ : M'.H) (b : ℬ) :
    (Φ.toWithState φ).ΦB b = Φ.ΦB b := rfl

variable (Φ : LocalIsometry M M')

/-- The isometry intertwines a sum of products of the two players' operators with the sum of the
products of their images. -/
theorem intertwine_sum {κ : Type*} (s : Finset κ) (X : κ → 𝒜) (Y : κ → ℬ) (v : M.H) :
    M'.π (∑ i ∈ s, M'.πA (Φ.ΦA (X i)) * M'.πB (Φ.ΦB (Y i))) (Φ.W v) =
      Φ.W (M.π (∑ i ∈ s, M.πA (X i) * M.πB (Y i)) v) := by
  rw [map_sum, map_sum, _root_.sum_apply, _root_.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => Φ.intertwine (X i) (Y i) v

/-- **A sum of products of the two players' operators keeps its state norm** along a local
isometry carrying the state to the state. -/
theorem snorm_sum_mul_of_W_ψ (h : Φ.W M.ψ = M'.ψ) {κ : Type*} (s : Finset κ) (X : κ → 𝒜)
    (Y : κ → ℬ) :
    M'.snorm (∑ i ∈ s, M'.πA (Φ.ΦA (X i)) * M'.πB (Φ.ΦB (Y i))) =
      M.snorm (∑ i ∈ s, M.πA (X i) * M.πB (Y i)) := by
  show ‖M'.π _ M'.ψ‖ = ‖M.π _ M.ψ‖
  rw [← h, Φ.intertwine_sum, LinearIsometry.norm_map]

/-- **A sum of products of the two players' operators keeps its quadratic form** along a local
isometry carrying the state to the state. -/
theorem qform_sum_mul_of_W_ψ (h : Φ.W M.ψ = M'.ψ) {κ : Type*} (s : Finset κ) (X : κ → 𝒜)
    (Y : κ → ℬ) :
    M'.qform (∑ i ∈ s, M'.πA (Φ.ΦA (X i)) * M'.πB (Φ.ΦB (Y i))) =
      M.qform (∑ i ∈ s, M.πA (X i) * M.πB (Y i)) := by
  show (⟪M'.ψ, M'.π _ M'.ψ⟫_ℂ).re = (⟪M.ψ, M.π _ M.ψ⟫_ℂ).re
  rw [← h, Φ.intertwine_sum, LinearIsometry.inner_map_map]

/-! ### Conjugation by a unitary of each player -/

section OfUnitary

variable (N : BipartiteModel.{u} 𝒞 𝒜 ℬ) (U : 𝒜) (V : ℬ) (hU : star U * U = 1)
  (hU' : U * star U = 1) (hV : star V * V = 1) (hV' : V * star V = 1)

/-- **Conjugation by a unitary of each player**: the isometry is the product `πA U πB V` of the
two unitaries, and each player's operators are conjugated by the player's unitary,
`X ↦ U X U*` and `Y ↦ V Y V*`. It is an isometry by `U* U = 1` and `V* V = 1`, and it intertwines
because the two players' operators commute; `U U* = 1` and `V V* = 1` make the two
homomorphisms unital (`ofUnitary_ΦA_one`, `ofUnitary_ΦB_one`). The state is carried to the state
only when `πA U πB V` fixes it, which is not asked. -/
def ofUnitary : LocalIsometry N N where
  W :=
    { toLinearMap := (N.π (N.πA U * N.πB V)).toLinearMap
      norm_map' := Op.norm_apply_of_isometry
        (N.star_π_mul_self (N.star_πA_mul_πB_mul_self hU hV)) }
  ΦA := (Unitary.conjStarAlgAut ℂ 𝒜 ⟨U, Unitary.mem_iff.2 ⟨hU, hU'⟩⟩).toNonUnitalStarAlgHom
  ΦB := (Unitary.conjStarAlgAut ℂ ℬ ⟨V, Unitary.mem_iff.2 ⟨hV, hV'⟩⟩).toNonUnitalStarAlgHom
  intertwineA X v := by
    show N.π (N.πA (U * X * star U)) (N.π (N.πA U * N.πB V) v) =
      N.π (N.πA U * N.πB V) (N.π (N.πA X) v)
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul]
    congr 2
    have h : N.πA (star U) * N.πA U = 1 := by rw [← map_mul, hU, map_one]
    calc N.πA (U * X * star U) * (N.πA U * N.πB V)
        = N.πA U * N.πA X * (N.πA (star U) * N.πA U) * N.πB V := by
          simp only [map_mul, mul_assoc]
      _ = N.πA U * (N.πA X * N.πB V) := by rw [h, mul_one, mul_assoc]
      _ = N.πA U * N.πB V * N.πA X := by rw [(N.commute X V).eq, mul_assoc]
  intertwineB Y v := by
    show N.π (N.πB (V * Y * star V)) (N.π (N.πA U * N.πB V) v) =
      N.π (N.πA U * N.πB V) (N.π (N.πB Y) v)
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul]
    congr 2
    have h : N.πB (star V) * N.πB V = 1 := by rw [← map_mul, hV, map_one]
    calc N.πB (V * Y * star V) * (N.πA U * N.πB V)
        = N.πA U * N.πB (V * Y * star V) * N.πB V := by
          rw [← mul_assoc, ← (N.commute U (V * Y * star V)).eq]
      _ = N.πA U * (N.πB V * N.πB Y * (N.πB (star V) * N.πB V)) := by
          simp only [map_mul, mul_assoc]
      _ = N.πA U * N.πB V * N.πB Y := by rw [h, mul_one, mul_assoc]

@[simp]
theorem ofUnitary_W (v : N.H) :
    (ofUnitary N U V hU hU' hV hV').W v = N.π (N.πA U * N.πB V) v := rfl

@[simp]
theorem ofUnitary_ΦA (X : 𝒜) : (ofUnitary N U V hU hU' hV hV').ΦA X = U * X * star U := rfl

@[simp]
theorem ofUnitary_ΦB (Y : ℬ) : (ofUnitary N U V hU hU' hV hV').ΦB Y = V * Y * star V := rfl

/-- The conjugation of the first player's operators is unital. -/
theorem ofUnitary_ΦA_one : (ofUnitary N U V hU hU' hV hV').ΦA 1 = 1 := by
  rw [ofUnitary_ΦA, mul_one, hU']

/-- The conjugation of the second player's operators is unital. -/
theorem ofUnitary_ΦB_one : (ofUnitary N U V hU hU' hV hV').ΦB 1 = 1 := by
  rw [ofUnitary_ΦB, mul_one, hV']

end OfUnitary

end LocalIsometry

/-! ## Embeddings -/

/-- **An embedding of bipartite models**: a local isometry carrying the state to the state and
preserving both players' units. It is the model form of an extension by ancilla registers in fixed
vectors, and of the reduced isometry of the soundness analysis of the Pauli basis test; everything
a model computes from its state and its players' operators is carried along it unchanged. -/
structure Embedding (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) (M' : BipartiteModel.{u'} 𝒞' 𝒜' ℬ')
    extends LocalIsometry M M' where
  /-- The isometry carries the state to the state. -/
  W_ψ : W M.ψ = M'.ψ
  /-- The first player's unit goes to the unit. -/
  ΦA_one : ΦA 1 = 1
  /-- The second player's unit goes to the unit. -/
  ΦB_one : ΦB 1 = 1

namespace Embedding

variable {M : BipartiteModel.{u} 𝒞 𝒜 ℬ} {M' : BipartiteModel.{u'} 𝒞' 𝒜' ℬ'}
  {M'' : BipartiteModel.{u''} 𝒞'' 𝒜'' ℬ''}

/-- **The identity embedding.** -/
def id (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) : M.Embedding M where
  W := LinearIsometry.id
  ΦA := NonUnitalStarAlgHom.id ℂ 𝒜
  ΦB := NonUnitalStarAlgHom.id ℂ ℬ
  intertwineA _ _ := rfl
  intertwineB _ _ := rfl
  W_ψ := rfl
  ΦA_one := rfl
  ΦB_one := rfl

/-- **Embeddings compose**, the second argument applied first (as `LocalIsometry.comp`). -/
def comp (ι' : M'.Embedding M'') (ι : M.Embedding M') : M.Embedding M'' where
  toLocalIsometry := ι'.toLocalIsometry.comp ι.toLocalIsometry
  W_ψ := LocalIsometry.comp_W_ψ ι.W_ψ ι'.W_ψ
  ΦA_one := by
    show ι'.ΦA (ι.ΦA 1) = 1
    rw [ι.ΦA_one, ι'.ΦA_one]
  ΦB_one := by
    show ι'.ΦB (ι.ΦB 1) = 1
    rw [ι.ΦB_one, ι'.ΦB_one]

/-- **The embedding with the players exchanged.** -/
def swap (ι : M.Embedding M') : M.swap.Embedding M'.swap where
  toLocalIsometry := ι.toLocalIsometry.swap
  W_ψ := ι.W_ψ
  ΦA_one := ι.ΦB_one
  ΦB_one := ι.ΦA_one

@[simp]
theorem id_W (v : M.H) : (Embedding.id M).W v = v := rfl

@[simp]
theorem id_ΦA (a : 𝒜) : (Embedding.id M).ΦA a = a := rfl

@[simp]
theorem id_ΦB (b : ℬ) : (Embedding.id M).ΦB b = b := rfl

theorem comp_toLocalIsometry (ι' : M'.Embedding M'') (ι : M.Embedding M') :
    (ι'.comp ι).toLocalIsometry = ι'.toLocalIsometry.comp ι.toLocalIsometry := rfl

@[simp]
theorem comp_W (ι' : M'.Embedding M'') (ι : M.Embedding M') (v : M.H) :
    (ι'.comp ι).W v = ι'.W (ι.W v) := rfl

@[simp]
theorem comp_ΦA (ι' : M'.Embedding M'') (ι : M.Embedding M') (a : 𝒜) :
    (ι'.comp ι).ΦA a = ι'.ΦA (ι.ΦA a) := rfl

@[simp]
theorem comp_ΦB (ι' : M'.Embedding M'') (ι : M.Embedding M') (b : ℬ) :
    (ι'.comp ι).ΦB b = ι'.ΦB (ι.ΦB b) := rfl

theorem swap_toLocalIsometry (ι : M.Embedding M') :
    ι.swap.toLocalIsometry = ι.toLocalIsometry.swap := rfl

@[simp]
theorem swap_W (ι : M.Embedding M') : ι.swap.W = ι.W := rfl

@[simp]
theorem swap_ΦA (ι : M.Embedding M') : ι.swap.ΦA = ι.ΦB := rfl

@[simp]
theorem swap_ΦB (ι : M.Embedding M') : ι.swap.ΦB = ι.ΦA := rfl

@[simp]
theorem swap_swap (ι : M.Embedding M') : ι.swap.swap = ι := rfl

/-! ### What an embedding carries over -/

section Transfer

variable (ι : M.Embedding M')

/-- **Born probabilities are carried over.** -/
theorem bornProb (a : 𝒜) (b : ℬ) : M'.bornProb (ι.ΦA a) (ι.ΦB b) = M.bornProb a b :=
  LocalIsometry.bornProb_of_W_ψ ι.W_ψ a b

/-- **The first player's state norms are carried over.** -/
theorem stateSqNorm (a : 𝒜) : M'.stateSqNorm (ι.ΦA a) = M.stateSqNorm a :=
  LocalIsometry.stateSqNorm_of_W_ψ ι.W_ψ a

/-- **The second player's state norms are carried over.** -/
theorem swap_stateSqNorm (b : ℬ) : M'.swap.stateSqNorm (ι.ΦB b) = M.swap.stateSqNorm b :=
  LocalIsometry.swap_stateSqNorm_of_W_ψ ι.W_ψ b

/-- **The cross norms are carried over.** -/
theorem xSqNorm (a : 𝒜) (b : ℬ) : M'.xSqNorm (ι.ΦA a) (ι.ΦB b) = M.xSqNorm a b :=
  LocalIsometry.xSqNorm_of_W_ψ ι.W_ψ a b

end Transfer

/-- **The state has the norm of the state.** -/
theorem norm_ψ (ι : M.Embedding M') : ‖M'.ψ‖ = ‖M.ψ‖ :=
  LocalIsometry.norm_ψ_of_W_ψ ι.W_ψ

section Measurements

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [PartialOrder 𝒜'] [StarOrderedRing 𝒜'] [PartialOrder ℬ'] [StarOrderedRing ℬ']
  (ι : M.Embedding M')

/-- **Two families of measurements pushed forward along an embedding have their
inconsistency.** -/
theorem inconsistency_pushforward {Λ X : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype X]
    (μ : X → ℝ) (P : X → POVMIn Λ 𝒜) (Q : X → POVMIn Λ ℬ) :
    M'.inconsistency μ (fun x => (P x).pushforward ι.ΦA ι.ΦA_one)
      (fun x => (Q x).pushforward ι.ΦB ι.ΦB_one) = M.inconsistency μ P Q := by
  unfold BipartiteModel.inconsistency
  simp only [POVMIn.pushforward_op, ι.bornProb]

/-- **A family of measurements pushed forward along an embedding has its value.** -/
theorem povmValue_pushforward {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (PA : X → POVMIn A 𝒜) (PB : Y → POVMIn B ℬ) :
    M'.povmValue G (fun x => (PA x).pushforward ι.ΦA ι.ΦA_one)
      (fun y => (PB y).pushforward ι.ΦB ι.ΦB_one) = M.povmValue G PA PB :=
  LocalIsometry.povmValue_pushforward ι.W_ψ ι.ΦA_one ι.ΦB_one G PA PB

end Measurements

end Embedding

/-- **Every isomorphism of models is an embedding.** -/
def Iso.toEmbedding {M : BipartiteModel.{u} 𝒞 𝒜 ℬ} {M' : BipartiteModel.{u'} 𝒞' 𝒜' ℬ'}
    (Φ : Iso M M') : M.Embedding M' where
  toLocalIsometry := Φ.toLocalIsometry
  W_ψ := Φ.W_ψ
  ΦA_one := map_one Φ.ΦA
  ΦB_one := map_one Φ.ΦB

theorem Iso.toEmbedding_toLocalIsometry {M : BipartiteModel.{u} 𝒞 𝒜 ℬ}
    {M' : BipartiteModel.{u'} 𝒞' 𝒜' ℬ'} (Φ : Iso M M') :
    Φ.toEmbedding.toLocalIsometry = Φ.toLocalIsometry := rfl

@[simp]
theorem Iso.toEmbedding_W {M : BipartiteModel.{u} 𝒞 𝒜 ℬ} {M' : BipartiteModel.{u'} 𝒞' 𝒜' ℬ'}
    (Φ : Iso M M') (v : M.H) : Φ.toEmbedding.W v = Φ.W v := rfl

@[simp]
theorem Iso.toEmbedding_ΦA {M : BipartiteModel.{u} 𝒞 𝒜 ℬ} {M' : BipartiteModel.{u'} 𝒞' 𝒜' ℬ'}
    (Φ : Iso M M') (a : 𝒜) : Φ.toEmbedding.ΦA a = Φ.ΦA a := rfl

@[simp]
theorem Iso.toEmbedding_ΦB {M : BipartiteModel.{u} 𝒞 𝒜 ℬ} {M' : BipartiteModel.{u'} 𝒞' 𝒜' ℬ'}
    (Φ : Iso M M') (b : ℬ) : Φ.toEmbedding.ΦB b = Φ.ΦB b := rfl

/-! ## The embeddings between extensions -/

section Extensions

variable (M : BipartiteModel.{u} 𝒞 𝒜 ℬ)
variable {α β α' β' : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β']

/-- **An inert ancilla in a unit vector, as an embedding** (`BipartiteModel.inert`). -/
def inertEmb (e : α × β → ℂ) (he : ‖evec e‖ = 1) : M.Embedding (M.expand e) where
  toLocalIsometry := M.inert e he
  W_ψ := M.inert_W_ψ e he
  ΦA_one := diagHom_one
  ΦB_one := diagHom_one

theorem inertEmb_toLocalIsometry (e : α × β → ℂ) (he : ‖evec e‖ = 1) :
    (M.inertEmb e he).toLocalIsometry = M.inert e he := rfl

@[simp]
theorem inertEmb_ΦA (e : α × β → ℂ) (he : ‖evec e‖ = 1) (a : 𝒜) :
    (M.inertEmb e he).ΦA a = diagonal fun _ => a := rfl

@[simp]
theorem inertEmb_ΦB (e : α × β → ℂ) (he : ‖evec e‖ = 1) (b : ℬ) :
    (M.inertEmb e he).ΦB b = diagonal fun _ => b := rfl

/-- **Associativity of extensions, as an embedding** (`BipartiteModel.assoc`), in a vector `e''`
that is the product of the two. -/
def assocEmb (e : α × β → ℂ) (e' : α' × β' → ℂ) (e'' : (α' × α) × (β' × β) → ℂ)
    (he : ∀ q, e'' q = e' (q.1.1, q.2.1) * e (q.1.2, q.2.2)) :
    ((M.expand e).expand e').Embedding (M.expand e'') where
  toLocalIsometry := M.assoc e e' e''
  W_ψ := M.assoc_W_ψ e e' e'' he
  ΦA_one := compHom_one
  ΦB_one := compHom_one

theorem assocEmb_toLocalIsometry (e : α × β → ℂ) (e' : α' × β' → ℂ)
    (e'' : (α' × α) × (β' × β) → ℂ) (he : ∀ q, e'' q = e' (q.1.1, q.2.1) * e (q.1.2, q.2.2)) :
    (M.assocEmb e e' e'' he).toLocalIsometry = M.assoc e e' e'' := rfl

@[simp]
theorem assocEmb_ΦA (e : α × β → ℂ) (e' : α' × β' → ℂ) (e'' : (α' × α) × (β' × β) → ℂ)
    (he : ∀ q, e'' q = e' (q.1.1, q.2.1) * e (q.1.2, q.2.2)) (a : Matrix α' α' (Matrix α α 𝒜)) :
    (M.assocEmb e e' e'' he).ΦA a = compHom a := rfl

@[simp]
theorem assocEmb_ΦB (e : α × β → ℂ) (e' : α' × β' → ℂ) (e'' : (α' × α) × (β' × β) → ℂ)
    (he : ∀ q, e'' q = e' (q.1.1, q.2.1) * e (q.1.2, q.2.2)) (b : Matrix β' β' (Matrix β β ℬ)) :
    (M.assocEmb e e' e'' he).ΦB b = compHom b := rfl

/-- **A relabelling of the registers, as an embedding** (`BipartiteModel.relabel`), to the
relabelled vector. -/
def relabelEmb (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β)
    (he : ∀ p, e' p = e (f p.1, g p.2)) : (M.expand e).Embedding (M.expand e') where
  toLocalIsometry := M.relabel e e' f g
  W_ψ := M.relabel_W_ψ e e' f g he
  ΦA_one := submatrixHom_one f
  ΦB_one := submatrixHom_one g

theorem relabelEmb_toLocalIsometry (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β)
    (he : ∀ p, e' p = e (f p.1, g p.2)) :
    (M.relabelEmb e e' f g he).toLocalIsometry = M.relabel e e' f g := rfl

@[simp]
theorem relabelEmb_ΦA (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β)
    (he : ∀ p, e' p = e (f p.1, g p.2)) (a : Matrix α α 𝒜) :
    (M.relabelEmb e e' f g he).ΦA a = a.submatrix f f := rfl

@[simp]
theorem relabelEmb_ΦB (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β)
    (he : ∀ p, e' p = e (f p.1, g p.2)) (b : Matrix β β ℬ) :
    (M.relabelEmb e e' f g he).ΦB b = b.submatrix g g := rfl

/-- **The exchange of the players in an extension, as an embedding**
(`BipartiteModel.swapExpand`), to the exchanged vector. -/
def swapExpandEmb (e : α × β → ℂ) (e' : β × α → ℂ) (he : ∀ p, e' p = e p.swap) :
    (M.expand e).swap.Embedding (M.swap.expand e') where
  toLocalIsometry := M.swapExpand e e'
  W_ψ := M.swapExpand_W_ψ e e' he
  ΦA_one := rfl
  ΦB_one := rfl

theorem swapExpandEmb_toLocalIsometry (e : α × β → ℂ) (e' : β × α → ℂ)
    (he : ∀ p, e' p = e p.swap) :
    (M.swapExpandEmb e e' he).toLocalIsometry = M.swapExpand e e' := rfl

@[simp]
theorem swapExpandEmb_ΦA (e : α × β → ℂ) (e' : β × α → ℂ) (he : ∀ p, e' p = e p.swap)
    (b : Matrix β β ℬ) : (M.swapExpandEmb e e' he).ΦA b = b := rfl

@[simp]
theorem swapExpandEmb_ΦB (e : α × β → ℂ) (e' : β × α → ℂ) (he : ∀ p, e' p = e p.swap)
    (a : Matrix α α 𝒜) : (M.swapExpandEmb e e' he).ΦB a = a := rfl

/-- **The change of cut, as an embedding** (`BipartiteModel.recutIsom`): the extension along the
regrouped registers into the reading of the original extension. -/
def recutEmb (e : α × β → ℂ) (σ : α × β ≃ α' × β') :
    (M.expand (e ∘ σ.symm)).Embedding (M.recut e σ) where
  toLocalIsometry := M.recutIsom e σ
  W_ψ := M.recutIsom_W_ψ e σ
  ΦA_one := rfl
  ΦB_one := rfl

theorem recutEmb_toLocalIsometry (e : α × β → ℂ) (σ : α × β ≃ α' × β') :
    (M.recutEmb e σ).toLocalIsometry = M.recutIsom e σ := rfl

@[simp]
theorem recutEmb_ΦA (e : α × β → ℂ) (σ : α × β ≃ α' × β') (X : Matrix α' α' 𝒜) :
    (M.recutEmb e σ).ΦA X = X := rfl

@[simp]
theorem recutEmb_ΦB (e : α × β → ℂ) (σ : α × β ≃ α' × β') (Y : Matrix β' β' ℬ) :
    (M.recutEmb e σ).ΦB Y = Y := rfl

end Extensions

end BipartiteModel

end MIPRE

end

end
