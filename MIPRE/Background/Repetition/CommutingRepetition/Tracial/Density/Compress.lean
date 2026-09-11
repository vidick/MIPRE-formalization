/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Tracial/Density/Compress.lean
-/
/-
# Compression of a commuting strategy to its separable cyclic subspace (stage E1)

The closed span `K` of the vectors `w ψ`, `w` a word in the finitely many effects
of a commuting strategy, is separable, invariant under every effect, and contains
`ψ`; compressing the strategy to `K` does not change its correlation. This
replaces Lin's appeal to Fritz's separability reduction (Lin §3.2, first
paragraph of the proof of Theorem 3.2). Proof-side infrastructure.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Game.Strategy

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Density

open scoped InnerProductSpace
open TopologicalSpace

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable (S : CommutingStrategy.{0} X Y A B)

/-- The letters: Alice's and Bob's effects. -/
noncomputable def letterOp : (X × A) ⊕ (Y × B) → S.H →L[ℂ] S.H
  | Sum.inl ⟨x, a⟩ => S.E x a
  | Sum.inr ⟨y, b⟩ => S.F y b

/-- A word in the effects, as an operator. -/
noncomputable def wordOp (l : List ((X × A) ⊕ (Y × B))) : S.H →L[ℂ] S.H :=
  (l.map (letterOp S)).prod

theorem wordOp_nil : wordOp S [] = 1 := rfl

theorem wordOp_cons (i : (X × A) ⊕ (Y × B)) (l : List ((X × A) ⊕ (Y × B))) :
    wordOp S (i :: l) = letterOp S i * wordOp S l := by
  rw [wordOp, List.map_cons, List.prod_cons]
  rfl

/-- The vectors `w ψ`. -/
noncomputable def wordVec (l : List ((X × A) ⊕ (Y × B))) : S.H := wordOp S l S.ψ

theorem countable_range_wordVec : (Set.range (wordVec S)).Countable :=
  Set.countable_range _

/-- The cyclic subspace: the closed span of the `w ψ`. -/
noncomputable def cyclic : Submodule ℂ S.H :=
  (Submodule.span ℂ (Set.range (wordVec S))).topologicalClosure

theorem isClosed_cyclic : IsClosed (cyclic S : Set S.H) :=
  Submodule.isClosed_topologicalClosure _

theorem ψ_mem_cyclic : S.ψ ∈ cyclic S :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨[], by rw [wordVec, wordOp_nil]; rfl⟩)

theorem letterOp_wordVec (i : (X × A) ⊕ (Y × B)) (l : List ((X × A) ⊕ (Y × B))) :
    letterOp S i (wordVec S l) = wordVec S (i :: l) := by
  rw [wordVec, wordVec, wordOp_cons, mul_apply_eq_comp]

theorem letterOp_mem_cyclic (i : (X × A) ⊕ (Y × B)) {v : S.H} (hv : v ∈ cyclic S) :
    letterOp S i v ∈ cyclic S := by
  have hspan : ∀ w ∈ Submodule.span ℂ (Set.range (wordVec S)),
      letterOp S i w ∈ Submodule.span ℂ (Set.range (wordVec S)) := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => letterOp S i w ∈
      Submodule.span ℂ (Set.range (wordVec S))) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨l, rfl⟩
      exact Submodule.subset_span ⟨i :: l, (letterOp_wordVec S i l).symm⟩
    · simp
    · intro u v _ _ hu hv
      rw [map_add]
      exact Submodule.add_mem _ hu hv
    · intro c u _ hu
      rw [map_smul]
      exact Submodule.smul_mem _ c hu
  have hv' : v ∈ closure (Submodule.span ℂ (Set.range (wordVec S)) : Set S.H) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hv
  have := map_mem_closure (letterOp S i).continuous hv' hspan
  rw [← Submodule.topologicalClosure_coe] at this
  exact this

theorem E_mem_cyclic (x : X) (a : A) {v : S.H} (hv : v ∈ cyclic S) : S.E x a v ∈ cyclic S :=
  letterOp_mem_cyclic S (Sum.inl ⟨x, a⟩) hv

theorem F_mem_cyclic (y : Y) (b : B) {v : S.H} (hv : v ∈ cyclic S) : S.F y b v ∈ cyclic S :=
  letterOp_mem_cyclic S (Sum.inr ⟨y, b⟩) hv

theorem isSeparable_cyclic : IsSeparable (cyclic S : Set S.H) := by
  rw [cyclic, Submodule.topologicalClosure_coe]
  exact (countable_range_wordVec S).isSeparable.span.closure

instance separableSpace_cyclic : SeparableSpace (cyclic S) :=
  (isSeparable_cyclic S).separableSpace

instance completeSpace_cyclic : CompleteSpace (cyclic S) :=
  (isClosed_cyclic S).completeSpace_coe

/-! ### Compression -/

/-- Compression of an operator leaving `cyclic S` invariant. -/
noncomputable def compressOp (T : S.H →L[ℂ] S.H) (hT : ∀ v ∈ cyclic S, T v ∈ cyclic S) :
    cyclic S →L[ℂ] cyclic S :=
  (T.comp (cyclic S).subtypeL).codRestrict (cyclic S) fun v => hT v v.2

theorem compressOp_apply (T : S.H →L[ℂ] S.H) (hT : ∀ v ∈ cyclic S, T v ∈ cyclic S)
    (v : cyclic S) : (compressOp S T hT v : S.H) = T v := rfl

theorem compressOp_isPositive {T : S.H →L[ℂ] S.H} (hT : ∀ v ∈ cyclic S, T v ∈ cyclic S)
    (hpos : T.IsPositive) : (compressOp S T hT).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff] at hpos ⊢
  refine ⟨fun v w => ?_, fun v => ?_⟩
  · have := hpos.1 v w
    simpa [Submodule.coe_inner, compressOp_apply] using this
  · have := hpos.2 v
    simpa [Submodule.coe_inner, compressOp_apply] using this

theorem compressOp_mul {T U : S.H →L[ℂ] S.H} (hT : ∀ v ∈ cyclic S, T v ∈ cyclic S)
    (hU : ∀ v ∈ cyclic S, U v ∈ cyclic S) :
    compressOp S (T * U) (fun v hv => hT _ (hU v hv)) = compressOp S T hT * compressOp S U hU := by
  ext v
  rfl

theorem compressOp_one : compressOp S 1 (fun _ hv => hv) = 1 := by
  ext v
  rfl

theorem compressOp_sum {ι : Type*} (s : Finset ι) (T : ι → S.H →L[ℂ] S.H)
    (hT : ∀ i, ∀ v ∈ cyclic S, T i v ∈ cyclic S) :
    compressOp S (∑ i ∈ s, T i) (fun v hv => by
      rw [ContinuousLinearMap.sum_apply]; exact Submodule.sum_mem _ fun i _ => hT i v hv) =
      ∑ i ∈ s, compressOp S (T i) (hT i) := by
  ext v
  simp [compressOp_apply, ContinuousLinearMap.sum_apply, Submodule.coe_sum]

/-- **The compressed strategy** on the separable cyclic subspace. -/
noncomputable def compress : CommutingStrategy.{0} X Y A B where
  H := cyclic S
  ψ := ⟨S.ψ, ψ_mem_cyclic S⟩
  ψ_norm := by
    show ‖S.ψ‖ = 1
    exact S.ψ_norm
  E x a := compressOp S (S.E x a) (fun v hv => E_mem_cyclic S x a hv)
  F y b := compressOp S (S.F y b) (fun v hv => F_mem_cyclic S y b hv)
  E_pos x a := compressOp_isPositive S _ (S.E_pos x a)
  F_pos y b := compressOp_isPositive S _ (S.F_pos y b)
  E_sum x := by
    rw [← compressOp_sum S Finset.univ (fun a => S.E x a) (fun a v hv => E_mem_cyclic S x a hv)]
    have h := S.E_sum x
    simp only [h]
    exact compressOp_one S
  F_sum y := by
    rw [← compressOp_sum S Finset.univ (fun b => S.F y b) (fun b v hv => F_mem_cyclic S y b hv)]
    have h := S.F_sum y
    simp only [h]
    exact compressOp_one S
  commutes x y a b := by
    rw [Commute, SemiconjBy, ← compressOp_mul, ← compressOp_mul]
    congr 1
    exact S.commutes x y a b

theorem compress_correlation : (compress S).correlation = S.correlation := by
  funext x y a b
  rfl

instance separableSpace_compress : SeparableSpace (compress S).H := separableSpace_cyclic S

end Density

end CommutingRepetition
