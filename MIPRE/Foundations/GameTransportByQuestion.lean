/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.ModelStrategy
public import MIPRE.Foundations.PerfectStrategy

@[expose] public section

/-! # Merging strategy answers separately at each question

Deterministic answer decoding can depend on the question. Merging the fibers
of these maps preserves projectivity, register dimensions and the shared
state. Acceptance implication gives monotonicity of the resulting value.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): for a projective strategy
of a model (`BipartiteModel.ProjStrat`) the merge is the coarse-graining of each measurement
along its own question's decoder, `fun x => (S'.PA x).map (rA x)`, which is the adapter
`ProjStrat.adapt` along the identity of the questions
(`BipartiteModel.ProjStrat.mergeAnswersByQuestion`). The merged strategy is a strategy of the
same model, so there is no state or register dimension to preserve, and a question whose decoder
is the identity keeps its measurement (`mergeByQuestionPAEq`, `mergeByQuestionPBEq`, equalities of
POVMs). The value bound is `BipartiteModel.povmValue_le_postprocess`; the tensor-product
statements are its instances in the tensor-product model of a strategy
(`TensorProductStrategy.value_mergeAnswersByQuestion`, through
`ProjectiveMeasurement.mergeByQuestion_toIn`).
-/

noncomputable section
namespace MIPRE
open Matrix Kronecker Finset Classical
open scoped ComplexOrder MatrixOrder

namespace ProjectiveMeasurement
variable {X A A' H : Type*} [Fintype A] [Fintype A'] [DecidableEq A]
  [Fintype H] [DecidableEq H]

/-- Merge each question's effects along its own answer map. -/
def mergeByQuestion (P : ProjectiveMeasurement X A' (Matrix H H ℂ)) (r : X → A' → A) :
    ProjectiveMeasurement X A (Matrix H H ℂ) where
  M x a := (P.merge (r x)).M x a
  selfAdjoint x a := (P.merge (r x)).selfAdjoint x a
  projective x a := (P.merge (r x)).projective x a
  normalized x := (P.merge (r x)).normalized x

/-- A merged effect is the sum over the decoding fiber at that question. -/
@[simp] theorem mergeByQuestion_M
    (P : ProjectiveMeasurement X A' (Matrix H H ℂ)) (r : X → A' → A) (x : X) (a : A) :
    (P.mergeByQuestion r).M x a = ∑ a' ∈ univ.filter (fun a' => r x a' = a), P.M x a' := rfl

/-- Questions whose decoder is the identity have exactly the original effects. -/
theorem mergeByQuestion_M_of_id (P : ProjectiveMeasurement X A (Matrix H H ℂ))
    (r : X → A → A) (x : X) (hr : ∀ a, r x a = a) (a : A) :
    (P.mergeByQuestion r).M x a = P.M x a := by
  simp [mergeByQuestion_M, hr, Finset.sum_filter]

/-- **The merged measurement is a coarse-graining in the matrix algebra**: at each question, the
fiber sums of the original POVM along that question's decoder (`POVMIn.map`). -/
theorem mergeByQuestion_toIn (P : ProjectiveMeasurement X A' (Matrix H H ℂ)) (r : X → A' → A)
    (x : X) : ((P.mergeByQuestion r).toPOVM x).toIn = (P.toPOVM x).toIn.map (r x) :=
  POVMIn.ext' fun a => by
    rw [POVMIn.map_op]
    rfl
end ProjectiveMeasurement

/-! ## In a bipartite model -/

namespace BipartiteModel.ProjStrat

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
variable {X Y A B A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B]

/-- **Decode answers by a question-dependent function**: at each question, the measurement of
`S'` with its outcomes merged along that question's decoder. It is the adapter along the
identity of the questions, a strategy of the same model. -/
def mergeAnswersByQuestion {G' : Game X Y A' B'} (S' : M.ProjStrat G') (G : Game X Y A B)
    (rA : X → A' → A) (rB : Y → B' → B) : M.ProjStrat G :=
  S'.adapt G (fun x => x) (fun y => y) rA rB

/-- A merged first-player measurement is the coarse-graining along the question's decoder. -/
@[simp] theorem mergeAnswersByQuestion_PA {G' : Game X Y A' B'} (S' : M.ProjStrat G')
    (G : Game X Y A B) (rA : X → A' → A) (rB : Y → B' → B) (x : X) :
    (S'.mergeAnswersByQuestion G rA rB).PA x = (S'.PA x).map (rA x) := rfl

/-- A merged second-player measurement is the coarse-graining along the question's decoder. -/
@[simp] theorem mergeAnswersByQuestion_PB {G' : Game X Y A' B'} (S' : M.ProjStrat G')
    (G : Game X Y A B) (rA : X → A' → A) (rB : Y → B' → B) (y : Y) :
    (S'.mergeAnswersByQuestion G rA rB).PB y = (S'.PB y).map (rB y) := rfl

/-- **Acceptance-preserving answer decoding can only increase the value**, on the same question
law (`BipartiteModel.povmValue_le_postprocess`). -/
theorem value_le_mergeAnswersByQuestion {G' : Game X Y A' B'} (S' : M.ProjStrat G')
    (G : Game X Y A B) (rA : X → A' → A) (rB : Y → B' → B) (hμ : ∀ x y, G.μ x y = G'.μ x y)
    (hD : ∀ x y a' b', G'.D x y a' b' = true → G.D x y (rA x a') (rB y b') = true) :
    S'.value ≤ (S'.mergeAnswersByQuestion G rA rB).value :=
  M.povmValue_le_postprocess G' G S'.PA S'.PB rA rB hμ hD

/-- **Identity decoding at a first-player question keeps its measurement**, under a
same-alphabet answer merge. -/
theorem mergeByQuestionPAEq {G' : Game X Y A B} (S' : M.ProjStrat G') (G : Game X Y A B)
    (rA : X → A → A) (rB : Y → B → B) (x : X) (hr : ∀ a, rA x a = a) :
    (S'.mergeAnswersByQuestion G rA rB).PA x = S'.PA x := by
  rw [mergeAnswersByQuestion_PA, show rA x = fun a => a from funext hr, POVMIn.map_id]

/-- **Identity decoding at a second-player question keeps its measurement**, under a
same-alphabet answer merge. -/
theorem mergeByQuestionPBEq {G' : Game X Y A B} (S' : M.ProjStrat G') (G : Game X Y A B)
    (rA : X → A → A) (rB : Y → B → B) (y : Y) (hr : ∀ b, rB y b = b) :
    (S'.mergeAnswersByQuestion G rA rB).PB y = S'.PB y := by
  rw [mergeAnswersByQuestion_PB, show rB y = fun b => b from funext hr, POVMIn.map_id]

/-- Identity decoding at a first-player question keeps each of its effects. -/
theorem mergeByQuestionPAEq_op {G' : Game X Y A B} (S' : M.ProjStrat G') (G : Game X Y A B)
    (rA : X → A → A) (rB : Y → B → B) (x : X) (a : A) (hr : ∀ a, rA x a = a) :
    ((S'.mergeAnswersByQuestion G rA rB).PA x).op a = (S'.PA x).op a := by
  rw [S'.mergeByQuestionPAEq G rA rB x hr]

/-- Identity decoding at a second-player question keeps each of its effects. -/
theorem mergeByQuestionPBEq_op {G' : Game X Y A B} (S' : M.ProjStrat G') (G : Game X Y A B)
    (rA : X → A → A) (rB : Y → B → B) (y : Y) (b : B) (hr : ∀ b, rB y b = b) :
    ((S'.mergeAnswersByQuestion G rA rB).PB y).op b = (S'.PB y).op b := by
  rw [S'.mergeByQuestionPBEq G rA rB y hr]

end BipartiteModel.ProjStrat

namespace TensorProductStrategy
variable {X Y A B A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B]

/-- Decode answers by a question-dependent function, preserving registers and state. -/
def mergeAnswersByQuestion {G' : Game X Y A' B'} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A' → A) (rB : Y → B' → B) : TensorProductStrategy G :=
  ⟨S'.dA, S'.dB, S'.ψ, S'.ψ_unit, S'.PA.mergeByQuestion rA, S'.PB.mergeByQuestion rB⟩

/-- **The merged strategy is the model's merged strategy**: its value is that of the projective
strategy of `S'` in its tensor-product model (`toModel`), merged question by question. -/
theorem value_mergeAnswersByQuestion {G' : Game X Y A' B'} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A' → A) (rB : Y → B' → B) :
    (S'.mergeAnswersByQuestion G rA rB).value
      = (S'.toModel.mergeAnswersByQuestion G rA rB).value := by
  rw [value_eq_tensor_povmValue]
  exact congrArg₂ ((BipartiteModel.tensor S'.ψ).povmValue G)
    (funext (S'.PA.mergeByQuestion_toIn rA)) (funext (S'.PB.mergeByQuestion_toIn rB))

/-- Acceptance-preserving answer decoding can only increase the strategy value: the
tensor-product instance of `BipartiteModel.ProjStrat.value_le_mergeAnswersByQuestion`. -/
theorem value_le_mergeAnswersByQuestion {G' : Game X Y A' B'}
    (S' : TensorProductStrategy G') (G : Game X Y A B)
    (rA : X → A' → A) (rB : Y → B' → B) (hμ : ∀ x y, G.μ x y = G'.μ x y)
    (hD : ∀ x y a' b', G'.D x y a' b' = true → G.D x y (rA x a') (rB y b') = true) :
    S'.value ≤ (S'.mergeAnswersByQuestion G rA rB).value := by
  rw [value_mergeAnswersByQuestion, ← S'.value_toModel]
  exact S'.toModel.value_le_mergeAnswersByQuestion G rA rB hμ hD

/-- Exact state equality for a question-dependent answer merge. The named
proposition avoids comparing concrete game definitions in dependent registers. -/
def MergeByQuestionStateEq {G' : Game X Y A' B'} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A' → A) (rB : Y → B' → B) : Prop :=
  (S'.mergeAnswersByQuestion G rA rB).ψ = S'.ψ

/-- Question-dependent answer merging preserves the original state. -/
theorem mergeByQuestionStateEq {G' : Game X Y A' B'} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A' → A) (rB : Y → B' → B) :
    S'.MergeByQuestionStateEq G rA rB := rfl

/-- Both finite register dimensions are unchanged by answer merging. -/
theorem mergeAnswersByQuestion_dimensions {G' : Game X Y A' B'} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A' → A) (rB : Y → B' → B) :
    (S'.mergeAnswersByQuestion G rA rB).dA = S'.dA ∧
      (S'.mergeAnswersByQuestion G rA rB).dB = S'.dB := ⟨rfl, rfl⟩

/-- Exact equality of an Alice effect under a same-alphabet answer merge. -/
def MergeByQuestionPAEq {G' : Game X Y A B} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A → A) (rB : Y → B → B) (x : X) (a : A) : Prop :=
  (S'.mergeAnswersByQuestion G rA rB).PA.M x a = S'.PA.M x a

/-- Identity decoding at an Alice question preserves its effects literally. -/
theorem mergeByQuestionPAEq {G' : Game X Y A B} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A → A) (rB : Y → B → B) (x : X) (a : A)
    (hr : ∀ a, rA x a = a) : S'.MergeByQuestionPAEq G rA rB x a :=
  S'.PA.mergeByQuestion_M_of_id rA x hr a

/-- Exact equality of a Bob effect under a same-alphabet answer merge. -/
def MergeByQuestionPBEq {G' : Game X Y A B} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A → A) (rB : Y → B → B) (y : Y) (b : B) : Prop :=
  (S'.mergeAnswersByQuestion G rA rB).PB.M y b = S'.PB.M y b

/-- Identity decoding at a Bob question preserves its effects literally. -/
theorem mergeByQuestionPBEq {G' : Game X Y A B} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A → A) (rB : Y → B → B) (y : Y) (b : B)
    (hr : ∀ b, rB y b = b) : S'.MergeByQuestionPBEq G rA rB y b :=
  S'.PB.mergeByQuestion_M_of_id rB y hr b

end TensorProductStrategy

namespace SyncStrategy
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  {G : SynchronousGame X A}

/-- Relaxing a predicate with the same question law can only increase a copied
synchronous strategy's value. -/
theorem value_le_copy (S : SyncStrategy G) (G' : SynchronousGame X A)
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    S.value ≤ (S.copy G').value := by
  rw [value_eq_ntr, value_eq_ntr]
  change (∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      ntr (S.P.M x a * S.P.M y b)) ≤
    ∑ x, ∑ y, ∑ a, ∑ b, G'.μ x y * (if G'.D x y a b then 1 else 0) *
      ntr (S.P.M x a * S.P.M y b)
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  rw [hμ]
  apply mul_le_mul_of_nonneg_right _ (S.ntr_mul_nonneg x y a b)
  apply mul_le_mul_of_nonneg_left _ (G.μ_nonneg x y)
  cases h : G.D x y a b with
  | false => cases G'.D x y a b <;> norm_num
  | true => rw [hD x y a b h]

/-- Copying to a relaxed game preserves perfect success. -/
theorem copy_value_eq_one (S : SyncStrategy G) (G' : SynchronousGame X A)
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true)
    (hS : S.value = 1) : (S.copy G').value = 1 :=
  le_antisymm (S.copy G').value_le_one (hS ▸ S.value_le_copy G' hμ hD)

/-- Copying a synchronous strategy keeps its dimension. -/
@[simp] theorem copy_d (S : SyncStrategy G) (G' : SynchronousGame X A) :
    (S.copy G').d = S.d := rfl
end SyncStrategy
end MIPRE

end
