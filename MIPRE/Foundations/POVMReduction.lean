/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.POVMDomination
public import MIPRE.Foundations.AncillaDilation
public import MIPRE.Foundations.LocalIsometry
public import MIPRE.Foundations.BlockOrder

@[expose] public section

/-! # Reducing the POVM strategies of one bipartite model to another's

Introspection extracts its strategy in a model built from the ancilla of the Pauli basis test by
adjoining, stage by stage, an ancilla register to one player (`BipartiteModel.expandA`, and its
second-player form on the swapped model), and the value model has to dominate the model the
strategy ends up in. Every POVM strategy of an extended model has the value of a POVM strategy of
the original one — its compression to the ancilla's reference state (`POVMIn.compress`), which is
a POVM because the diagonal blocks of a nonnegative block matrix are nonnegative
(`MatrixStar.diag_nonneg`) — so domination passes to the extension for **every** value model
(`ValueModel.DominatesPOVM.of_povmReduces`), with no hypothesis on the value model. A local
isometry carrying the state to the state reduces its source to its target the same way, by the
pushforward (`BipartiteModel.LocalIsometry.povmReduces`).

Phase 4 of `planning/mipco-track.md`.
-/

noncomputable section

namespace MIPRE

open Finset Matrix

set_option linter.unusedSectionVars false

/-! ## Compressing a POVM of block matrices -/

namespace POVMIn

variable {A T R : Type*} [Fintype A] [Fintype T] [DecidableEq T] [Ring R] [StarRing R]
  [PartialOrder R] [StarOrderedRing R] [StarProper R]

/-- **The compression of a POVM of block matrices to one diagonal block**: a POVM, since the
diagonal blocks of a nonnegative block matrix are nonnegative and those of `1` are `1`. -/
def compress (t₀ : T) (P : POVMIn A (Matrix T T R)) : POVMIn A R where
  mats a := ⟨P.op a t₀ t₀, by
    have h := congrFun (congrFun (P.star_op a) t₀) t₀
    rw [Matrix.star_apply] at h
    exact h⟩
  nonneg a := Subtype.coe_le_coe.mp (MatrixStar.diag_nonneg (P.op_nonneg a) t₀)
  normalized := Subtype.ext (by
    rw [AddSubmonoidClass.coe_finsetSum]
    change ∑ a, P.op a t₀ t₀ = 1
    rw [← Matrix.sum_apply, P.sum_op, Matrix.one_apply_eq])

@[simp]
theorem compress_op (t₀ : T) (P : POVMIn A (Matrix T T R)) (a : A) :
    (P.compress t₀).op a = P.op a t₀ t₀ := rfl

end POVMIn

/-! ## The reduction -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]
variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ']

/-- **The POVM strategies of `M'` reduce to those of `M`**: each, for any game on `Type`, has value
at most that of a POVM strategy of `M`. -/
def POVMReduces (M' : BipartiteModel 𝒞' 𝒜' ℬ') (M : BipartiteModel 𝒞 𝒜 ℬ) : Prop :=
  ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] (G : Game X Y A B)
    (PA : X → POVMIn A 𝒜') (PB : Y → POVMIn B ℬ'),
    ∃ (QA : X → POVMIn A 𝒜) (QB : Y → POVMIn B ℬ), M'.povmValue G PA PB ≤ M.povmValue G QA QB

theorem POVMReduces.refl (M : BipartiteModel 𝒞 𝒜 ℬ) : M.POVMReduces M :=
  fun _ PA PB => ⟨PA, PB, le_rfl⟩

theorem POVMReduces.trans {𝒞'' 𝒜'' ℬ'' : Type*} [Ring 𝒞''] [StarRing 𝒞''] [Algebra ℂ 𝒞'']
    [Ring 𝒜''] [StarRing 𝒜''] [Algebra ℂ 𝒜''] [Ring ℬ''] [StarRing ℬ''] [Algebra ℂ ℬ'']
    [PartialOrder 𝒜''] [StarOrderedRing 𝒜''] [PartialOrder ℬ''] [StarOrderedRing ℬ'']
    {M'' : BipartiteModel 𝒞'' 𝒜'' ℬ''} {M' : BipartiteModel 𝒞' 𝒜' ℬ'}
    {M : BipartiteModel 𝒞 𝒜 ℬ} (h₁ : M''.POVMReduces M') (h₂ : M'.POVMReduces M) :
    M''.POVMReduces M := fun G PA PB => by
  obtain ⟨QA, QB, hQ⟩ := h₁ G PA PB
  obtain ⟨RA, RB, hR⟩ := h₂ G QA QB
  exact ⟨RA, RB, hQ.trans hR⟩

/-- **A local isometry carrying the state to the state reduces its source to its target**: a
strategy moves by the pushforward, with its value (`LocalIsometry.povmValue_pushforward`). -/
theorem LocalIsometry.povmReduces {M : BipartiteModel 𝒞 𝒜 ℬ} {M' : BipartiteModel 𝒞' 𝒜' ℬ'}
    (Φ : LocalIsometry M M') (h : Φ.W M.ψ = M'.ψ) (hA : Φ.ΦA 1 = 1) (hB : Φ.ΦB 1 = 1) :
    M.POVMReduces M' := fun G PA PB =>
  ⟨fun x => (PA x).pushforward Φ.ΦA hA, fun y => (PB y).pushforward Φ.ΦB hB,
    (Φ.povmValue_pushforward h hA hB G PA PB).ge⟩

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- **Adjoining an ancilla register to the first player reduces to the original model**: a
strategy's value is that of its compression to the reference state (`bornProb_expandA`). -/
theorem povmReduces_expandA [StarProper 𝒜] (M : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T) :
    (M.expandA t₀).POVMReduces M := fun G PA PB =>
  ⟨fun x => (PA x).compress t₀, PB, le_of_eq (by
    simp only [povmValue, condWin, bornProb_expandA, POVMIn.compress_op])⟩

/-- **Adjoining an ancilla register to the second player reduces to the original model**: the
extension of the first player of the swapped model, swapped back. -/
theorem povmReduces_expandB [StarProper ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ) (t₀ : T) :
    ((M.swap.expandA t₀).swap).POVMReduces M := fun G PA PB =>
  ⟨PA, fun y => (PB y).compress t₀, le_of_eq (by
    simp only [povmValue, condWin, POVMIn.compress_op]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    congr 1
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [bornProb_swap, bornProb_expandA, bornProb_swap])⟩

end BipartiteModel

/-- **Domination passes along a reduction**: a value model dominating the POVM strategies of `M`
dominates those of every model reducing to `M`. -/
theorem ValueModel.DominatesPOVM.of_povmReduces {𝒞 𝒜 ℬ 𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞] [StarRing 𝒞]
    [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
    [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] [Ring 𝒞']
    [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜'] [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ']
    [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜'] [PartialOrder ℬ'] [StarOrderedRing ℬ']
    {ω : ValueModel} {M : BipartiteModel 𝒞 𝒜 ℬ} {M' : BipartiteModel 𝒞' 𝒜' ℬ'}
    (h : M'.POVMReduces M) (hM : ω.DominatesPOVM M) : ω.DominatesPOVM M' := fun G PA PB => by
  obtain ⟨QA, QB, hQ⟩ := h G PA PB
  exact hQ.trans (hM G QA QB)

end MIPRE

end
