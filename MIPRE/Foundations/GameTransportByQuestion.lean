/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.GameTransport
import MIPRE.Foundations.PerfectStrategy

/-! # Merging strategy answers separately at each question

Deterministic answer decoding can depend on the question. Merging the fibers
of these maps preserves projectivity, register dimensions and the shared
state. Acceptance implication gives monotonicity of the resulting value.
-/

noncomputable section
namespace MIPRE
open Matrix Kronecker Finset Classical

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
end ProjectiveMeasurement

namespace TensorProductStrategy
variable {X Y A B A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B]

/-- Decode answers by a question-dependent function, preserving registers and state. -/
def mergeAnswersByQuestion {G' : Game X Y A' B'} (S' : TensorProductStrategy G')
    (G : Game X Y A B) (rA : X → A' → A) (rB : Y → B' → B) : TensorProductStrategy G :=
  ⟨S'.dA, S'.dB, S'.ψ, S'.ψ_unit, S'.PA.mergeByQuestion rA, S'.PB.mergeByQuestion rB⟩

/-- Acceptance-preserving answer decoding can only increase the strategy value. -/
theorem value_le_mergeAnswersByQuestion {G' : Game X Y A' B'}
    (S' : TensorProductStrategy G') (G : Game X Y A B)
    (rA : X → A' → A) (rB : Y → B' → B) (hμ : ∀ x y, G.μ x y = G'.μ x y)
    (hD : ∀ x y a' b', G'.D x y a' b' = true → G.D x y (rA x a') (rB y b') = true) :
    S'.value ≤ (S'.mergeAnswersByQuestion G rA rB).value := by
  unfold value
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  set w : A' → B' → ℝ :=
    fun a' b' => (star S'.ψ ⬝ᵥ ((S'.PA.M x a' ⊗ₖ S'.PB.M y b') *ᵥ S'.ψ)).re with hw
  have hw0 : ∀ a' b', 0 ≤ w a' b' := fun a' b' => S'.re_dotProduct_nonneg x y a' b'
  -- the merged Born-rule weight of `(a, b)` is the sum of the weights over the fibers
  have hbil : ∀ a b, (star S'.ψ ⬝ᵥ (((S'.PA.mergeByQuestion rA).M x a ⊗ₖ (S'.PB.mergeByQuestion rB).M y b) *ᵥ
      S'.ψ)).re = ∑ a' ∈ Finset.univ.filter (fun a' => rA x a' = a),
        ∑ b' ∈ Finset.univ.filter (fun b' => rB y b' = b), w a' b' := by
    intro a b
    have hsplit : (S'.PA.mergeByQuestion rA).M x a ⊗ₖ (S'.PB.mergeByQuestion rB).M y b =
        ∑ a' ∈ Finset.univ.filter (fun a' => rA x a' = a),
          ∑ b' ∈ Finset.univ.filter (fun b' => rB y b' = b), S'.PA.M x a' ⊗ₖ S'.PB.M y b' := by
      ext p q
      simp only [ProjectiveMeasurement.mergeByQuestion_M, Matrix.sum_apply, kroneckerMap_apply,
        Finset.sum_mul_sum]
    rw [hsplit, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  show ∑ a', ∑ b', G'.μ x y * (if G'.D x y a' b' then 1 else 0) * w a' b' ≤
    ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S'.ψ ⬝ᵥ (((S'.PA.mergeByQuestion rA).M x a ⊗ₖ (S'.PB.mergeByQuestion rB).M y b) *ᵥ S'.ψ)).re
  simp_rw [hbil]
  calc ∑ a', ∑ b', G'.μ x y * (if G'.D x y a' b' then 1 else 0) * w a' b'
      ≤ ∑ a', ∑ b', G.μ x y * (if G.D x y (rA x a') (rB y b') then 1 else 0) * w a' b' := by
        refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
        rw [hμ]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (G'.μ_nonneg x y))
          (hw0 a' b')
        cases h : G'.D x y a' b' with
        | false => by_cases h' : G.D x y (rA x a') (rB y b') = true <;> simp [h']
        | true => rw [hD x y a' b' h]
    _ = ∑ a, ∑ a' ∈ Finset.univ.filter (fun a' => rA x a' = a), ∑ b,
          ∑ b' ∈ Finset.univ.filter (fun b' => rB y b' = b),
            G.μ x y * (if G.D x y (rA x a') (rB y b') then 1 else 0) * w a' b' := by
        rw [Finset.sum_fiberwise Finset.univ (rA x)]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_fiberwise Finset.univ (rB y)]
    _ = ∑ a, ∑ a' ∈ Finset.univ.filter (fun a' => rA x a' = a), ∑ b,
          ∑ b' ∈ Finset.univ.filter (fun b' => rB y b' = b),
            G.μ x y * (if G.D x y a b then 1 else 0) * w a' b' := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' ha' =>
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' hb' => ?_
        rw [(Finset.mem_filter.1 ha').2, (Finset.mem_filter.1 hb').2]
    _ = ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
          ∑ a' ∈ Finset.univ.filter (fun a' => rA x a' = a),
            ∑ b' ∈ Finset.univ.filter (fun b' => rB y b' = b), w a' b' := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]

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
