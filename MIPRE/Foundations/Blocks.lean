/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Logic.Equiv.Basic

/-!
# Summing over assignments to a block-decomposed index type

A construction that reads only some coordinates of a uniformly random point needs to know that
those coordinates are themselves uniform, and independent of the rest. In the form a sum identity
takes, that is: when the index type is a sum, summing a function of the blocks' assignments over all
assignments to the whole gives the iterated sum over the blocks --- once per assignment of whatever
block the function ignores.

* `sum_arrow_pair` --- both blocks, which is the product measure written as an iterated sum;
* `sum_arrow_inl` --- the left block alone, at the cost of one factor of the right block's count.

Nothing here is about fields, lines or games. The only reason the file exists is that the padded
space of the combining stage (`MIPRE/Background/QLD/Padded.lean`) is `F_q^{4m}` with its coordinates
split into blocks, and every distributional statement about that splitting reduces to these two.
-/

noncomputable section

namespace MIPRE

open Finset

variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]

/-- An assignment to a sum index type is a pair of assignments to the summands. Spelled out rather
than taken from `Equiv.sumArrowEquivProdArrow` so that both directions compute by `rfl`. -/
def sumArrow (α β F : Type*) : (α ⊕ β → F) ≃ (α → F) × (β → F) where
  toFun u := (fun a => u (.inl a), fun b => u (.inr b))
  invFun p := Sum.elim p.1 p.2
  left_inv u := by funext j; cases j <;> rfl
  right_inv _ := rfl

/-- **Both blocks of a uniform assignment are uniform and independent.** -/
theorem sum_arrow_pair (g : (α → F) → (β → F) → M) :
    ∑ u : α ⊕ β → F, g (fun a => u (.inl a)) (fun b => u (.inr b))
      = ∑ wa : α → F, ∑ wb : β → F, g wa wb := by
  classical
  rw [← Equiv.sum_comp (sumArrow α β F).symm
    (fun u : α ⊕ β → F => g (fun a => u (.inl a)) (fun b => u (.inr b)))]
  exact Fintype.sum_prod_type _

/-- **The left block of a uniform assignment is uniform**, each value counted once per assignment
to the right block. -/
theorem sum_arrow_inl (g : (α → F) → M) :
    ∑ u : α ⊕ β → F, g (fun a => u (.inl a))
      = Fintype.card (β → F) • ∑ wa : α → F, g wa := by
  classical
  rw [show (∑ u : α ⊕ β → F, g (fun a => u (.inl a)))
      = ∑ u : α ⊕ β → F, (fun wa (_ : β → F) => g wa) (fun a => u (.inl a))
        (fun b => u (.inr b)) from rfl,
    sum_arrow_pair (fun wa (_ : β → F) => g wa),
    Finset.sum_congr rfl fun wa _ => Finset.sum_const (g wa), Finset.card_univ,
    Finset.sum_nsmul]

/-! ## Rewriting, reordering and scaling nested sums

A block decomposition turns one sum into two, and the new sums appear where the old one was. Getting
from there to a statement about each block's own law is bookkeeping: rewrite a sum that sits under
others, move one sum past its neighbours, and pull a constant multiplier out. These are the three
moves, stated at the arities the padded space needs, so that a proof can name the step it is taking
instead of rebuilding a `Finset.sum_congr` tower each time.
-/

section Bookkeeping

variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]

theorem sum_congr1 {f g : A → M} (h : ∀ a, f a = g a) : ∑ a : A, f a = ∑ a : A, g a :=
  Finset.sum_congr rfl fun a _ => h a

theorem sum_congr2 {f g : A → B → M} (h : ∀ a b, f a b = g a b) :
    ∑ a : A, ∑ b : B, f a b = ∑ a : A, ∑ b : B, g a b :=
  sum_congr1 fun a => sum_congr1 fun b => h a b

theorem sum_congr3 {f g : A → B → C → M} (h : ∀ a b c, f a b c = g a b c) :
    ∑ a : A, ∑ b : B, ∑ c : C, f a b c = ∑ a : A, ∑ b : B, ∑ c : C, g a b c :=
  sum_congr1 fun a => sum_congr2 fun b c => h a b c

theorem sum_congr4 {f g : A → B → C → D → M} (h : ∀ a b c d, f a b c d = g a b c d) :
    ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, f a b c d
      = ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, g a b c d :=
  sum_congr1 fun a => sum_congr3 fun b c d => h a b c d

theorem sum_nsmul1 (n : ℕ) (f : A → M) : ∑ a : A, n • f a = n • ∑ a : A, f a :=
  Finset.sum_nsmul _ _ _

theorem sum_nsmul2 (n : ℕ) (f : A → B → M) :
    ∑ a : A, ∑ b : B, n • f a b = n • ∑ a : A, ∑ b : B, f a b := by
  rw [sum_congr1 fun a => sum_nsmul1 n (f a), sum_nsmul1]

theorem sum_nsmul3 (n : ℕ) (f : A → B → C → M) :
    ∑ a : A, ∑ b : B, ∑ c : C, n • f a b c = n • ∑ a : A, ∑ b : B, ∑ c : C, f a b c := by
  rw [sum_congr1 fun a => sum_nsmul2 n (f a), sum_nsmul1]

theorem sum_nsmul4 (n : ℕ) (f : A → B → C → D → M) :
    ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, n • f a b c d
      = n • ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, f a b c d := by
  rw [sum_congr1 fun a => sum_nsmul3 n (f a), sum_nsmul1]

/-- Moving the second of four nested sums inwards to last place. -/
theorem sum_comm_four_in (f : A → B → C → D → M) :
    ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, f a b c d
      = ∑ a : A, ∑ c : C, ∑ d : D, ∑ b : B, f a b c d := by
  refine sum_congr1 fun a => ?_
  rw [Finset.sum_comm]
  exact sum_congr1 fun c => Finset.sum_comm

/-- Swapping the second and third of four nested sums. -/
theorem sum_comm_four_mid (f : A → B → C → D → M) :
    ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, f a b c d
      = ∑ a : A, ∑ c : C, ∑ b : B, ∑ d : D, f a b c d :=
  sum_congr1 fun a => Finset.sum_comm

/-- Moving the second of six nested sums inwards past the next two. A block decomposition produces
the two sides' data interleaved, and this is what puts each side's data back together. -/
theorem sum_comm_six (f : A → B → C → D → E → G → M) :
    ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, ∑ e : E, ∑ x : G, f a b c d e x
      = ∑ a : A, ∑ c : C, ∑ d : D, ∑ b : B, ∑ e : E, ∑ x : G, f a b c d e x := by
  refine sum_congr1 fun a => ?_
  rw [Finset.sum_comm]
  exact sum_congr1 fun c => Finset.sum_comm

/-- Swapping the fourth and fifth of six nested sums. -/
theorem sum_comm_six_swap (f : A → B → C → D → E → G → M) :
    ∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, ∑ e : E, ∑ x : G, f a b c d e x
      = ∑ a : A, ∑ b : B, ∑ c : C, ∑ e : E, ∑ d : D, ∑ x : G, f a b c d e x :=
  sum_congr3 fun a b c => Finset.sum_comm

/-- Only the first component of a pair is read. -/
theorem sum_prod_fst [DecidableEq A] (h : A → M) :
    ∑ p : A × B, h p.1 = Fintype.card B • ∑ a : A, h a := by
  classical
  rw [← Finset.univ_product_univ, Finset.sum_product]
  exact (sum_congr1 fun a => Finset.sum_const (h a)).trans
    (by rw [Finset.card_univ, sum_nsmul1])

end Bookkeeping

/-! ## Marginals of a uniform average

A uniform average of a quantity that depends on only part of the sample is the uniform average over
that part. Stated once, for an arbitrary splitting of the sample space given as an equivalence with a
product, it is what relates the Pauli basis test's single content --- which carries both sides' points
but *one* seed and *one* raw direction --- to a product of two independent line-point laws: each
side's own data has the same marginal under both.
-/

section Marginal

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Nonempty α] [Nonempty γ]

/-- **A uniform average of a function of one factor is the uniform average over that factor.** -/
theorem avg_comp_equiv_fst (e : α ≃ β × γ) (f : β → ℝ) :
    ∑ a : α, (Fintype.card α : ℝ)⁻¹ * f (e a).1 = ∑ b : β, (Fintype.card β : ℝ)⁻¹ * f b := by
  classical
  have : Nonempty β := ⟨(e (Classical.arbitrary α)).1⟩
  have hcard : Fintype.card α = Fintype.card β * Fintype.card γ := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  have hγ : (Fintype.card γ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Equiv.sum_comp e (fun p : β × γ => (Fintype.card α : ℝ)⁻¹ * f p.1),
    Fintype.sum_prod_type]
  refine sum_congr1 fun b => ?_
  have hb : ∀ c : γ, (Fintype.card α : ℝ)⁻¹ * f ((b, c) : β × γ).1
      = (Fintype.card α : ℝ)⁻¹ * f b := fun _ => rfl
  rw [sum_congr1 hb, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, Nat.cast_mul]
  field_simp


end Marginal

end MIPRE
