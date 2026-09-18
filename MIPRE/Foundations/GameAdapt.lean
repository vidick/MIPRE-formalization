/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.GameTransport

/-!
# Playing a strategy for one game as a strategy for another

`MIPRE.Foundations.GameTransport` compares games that share their question alphabets and their
distribution. This file drops both assumptions, which is what a *reduction* between two
genuinely different games needs: given a strategy `S` for `G`, a map `qA` of the target game's
questions into `G`'s and a coarse-graining `rA` of `G`'s answers into the target's, `S.adapt`
plays `S` through them.

## The conditional success probability

Everything is organized around `succAt S x y`, the probability that `S` is accepted *given* the
question pair `(x, y)`, and its complement `failAt`. The value is the `μ`-average of `succAt`
(`value_eq_sum_succAt`), so

`1 - S.value = ∑ x y, μ x y * failAt S x y`  (`one_sub_value_eq_sum_failAt`),

which is the form a reduction compares across two games: an inequality between failure
probabilities, each weighted by its own game's distribution.

## What the adapter costs

`failAt_adapt_le` says the adapted strategy fails no more often at `(x', y')` than `S` does at
`(qA x', qB y')`, provided every tuple `G` accepts is still accepted after coarse-graining
(`hD`). The summed statements ask `hD` only where `G'.μ` is nonzero, and that is not a
convenience: a question pair outside the target's support may well be one the target *rejects*
and the source accepts --- for the seeded CL test, a pair of two line questions, which the
canonical-line test has no subtest for --- so the unrestricted hypothesis would be false. Summing, the price is entirely in the distributions: `one_sub_value_adapt_le` asks that
the push-forward of `G'`'s distribution along `(qA, qB)` be dominated by `C` times `G`'s, and
concludes `1 - (S.adapt …).value ≤ C * (1 - S.value)`.

## Derandomization

A reduction usually cannot choose the question map canonically: the target's question is
typically a *coarser* object than `G`'s — a line rather than a seeded description of a line —
so one has to pick a preimage, and for any fixed choice the push-forward bound is off by the
size of the fibre. `exists_one_sub_value_adapt_le` is the averaged form. It asks only that the
push-forward bound hold on average over a finite family of question maps, and returns one
member of the family achieving the conclusion. That is the "choose the best seed" step, and the
averaging is exactly where the fibre size is paid back.
-/

namespace MIPRE

open Matrix Kronecker Finset

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']

/-- A double sum over the fibres of two coarse-grainings is the double sum. -/
theorem sum_sum_fiberwise₂ {M : Type*} [AddCommMonoid M] [DecidableEq A'] [DecidableEq B']
    (rA : A → A') (rB : B → B') (f : A → B → M) :
    ∑ a', ∑ b', ∑ a ∈ Finset.univ.filter (fun a => rA a = a'),
        ∑ b ∈ Finset.univ.filter (fun b => rB b = b'), f a b
      = ∑ a, ∑ b, f a b := by
  rw [← Finset.sum_fiberwise (Finset.univ : Finset A) rA (fun a => ∑ b, f a b)]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_fiberwise (Finset.univ : Finset B) rB (fun b => f a b)]

/-! ## Question-dependent merging of outcomes -/

namespace ProjectiveMeasurement

/-- Merge the outcomes of `P` along a coarse-graining that may depend on the question, while
reindexing the questions. `GameTransport`'s `merge` is the case of a coarse-graining that does
not depend on the question; a reduction generally needs the dependence, because how an answer
must be converted can depend on which question was asked --- the reparametrization of a line
answer depends on the line. -/
def mergeAt {X X' A A' : Type*} [Fintype A] [Fintype A'] [DecidableEq A'] {n : Type*}
    [Fintype n] [DecidableEq n] (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (qX : X' → X)
    (r : X' → A → A') : ProjectiveMeasurement X' A' (Matrix n n ℂ) where
  M x' a' := ∑ a ∈ Finset.univ.filter (fun a => r x' a = a'), P.M (qX x') a
  selfAdjoint x' a' := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun a _ => P.selfAdjoint _ a
  projective x' a' := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_eq_single a (fun b _ hb => P.mul_eq_zero_of_ne _ (Ne.symm hb))
      (fun h => absurd ha h)]
    exact P.projective _ a
  normalized x' := by
    rw [Finset.sum_fiberwise]
    exact P.normalized _

@[simp] theorem mergeAt_M {X X' A A' : Type*} [Fintype A] [Fintype A'] [DecidableEq A']
    {n : Type*} [Fintype n] [DecidableEq n] (P : ProjectiveMeasurement X A (Matrix n n ℂ))
    (qX : X' → X) (r : X' → A → A') (x' : X') (a' : A') :
    (P.mergeAt qX r).M x' a'
      = ∑ a ∈ Finset.univ.filter (fun a => r x' a = a'), P.M (qX x') a := rfl

end ProjectiveMeasurement

namespace TensorProductStrategy

variable {G : Game X Y A B}

/-! ## Born-rule probabilities and the conditional success probability -/

/-- The Born-rule probability that `S` answers `(a, b)` to the question pair `(x, y)`. -/
noncomputable def born (S : TensorProductStrategy G) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re

theorem born_nonneg (S : TensorProductStrategy G) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.born x y a b :=
  S.re_dotProduct_nonneg x y a b

theorem sum_born (S : TensorProductStrategy G) (x : X) (y : Y) :
    ∑ a, ∑ b, S.born x y a b = 1 := by
  simpa [born, Complex.re_sum] using congrArg Complex.re (S.sum_dotProduct_kronecker x y)

/-- The probability that `S` is accepted, given the question pair `(x, y)`. -/
noncomputable def succAt (S : TensorProductStrategy G) (x : X) (y : Y) : ℝ :=
  ∑ a, ∑ b, (if G.D x y a b then 1 else 0) * S.born x y a b

/-- The probability that `S` is rejected, given the question pair `(x, y)`. -/
noncomputable def failAt (S : TensorProductStrategy G) (x : X) (y : Y) : ℝ :=
  1 - S.succAt x y

theorem succAt_nonneg (S : TensorProductStrategy G) (x : X) (y : Y) : 0 ≤ S.succAt x y :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    mul_nonneg (by split_ifs <;> norm_num) (S.born_nonneg x y a b)

theorem succAt_le_one (S : TensorProductStrategy G) (x : X) (y : Y) : S.succAt x y ≤ 1 := by
  rw [← S.sum_born x y]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  cases h : G.D x y a b with
  | false => simpa [h] using S.born_nonneg x y a b
  | true => simp

theorem failAt_nonneg (S : TensorProductStrategy G) (x : X) (y : Y) : 0 ≤ S.failAt x y :=
  sub_nonneg.mpr (S.succAt_le_one x y)

theorem failAt_le_one (S : TensorProductStrategy G) (x : X) (y : Y) : S.failAt x y ≤ 1 := by
  have := S.succAt_nonneg x y
  simp only [failAt]
  linarith

/-- The value is the `μ`-average of the conditional success probability. -/
theorem value_eq_sum_succAt (S : TensorProductStrategy G) :
    S.value = ∑ x, ∑ y, G.μ x y * S.succAt x y := by
  unfold value succAt
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [born]; ring

/-- **The failure probability, decomposed by question pair.** -/
theorem one_sub_value_eq_sum_failAt (S : TensorProductStrategy G) :
    1 - S.value = ∑ x, ∑ y, G.μ x y * S.failAt x y := by
  have hsplit : ∑ x, ∑ y, G.μ x y * S.failAt x y
      = (∑ x, ∑ y, G.μ x y) - ∑ x, ∑ y, G.μ x y * S.succAt x y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by simp only [failAt]; ring
  rw [hsplit, G.μ_sum_one, value_eq_sum_succAt]

/-! ## The adapted strategy -/

section Adapt

variable [DecidableEq A'] [DecidableEq B']

/-- **Play `S` on `G'`**, through a map `qA`, `qB` of `G'`'s questions into `G`'s and a
coarse-graining `rA`, `rB` of `G`'s answers into `G'`'s that may depend on the question: the
measurement at a question `x'` of `G'` is the one `S` uses at `qA x'`, with its outcomes merged
along `rA x'`. -/
noncomputable def adapt (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') :
    TensorProductStrategy G' :=
  ⟨S.dA, S.dB, S.ψ, S.ψ_unit, S.PA.mergeAt qA rA, S.PB.mergeAt qB rB⟩

/-- The adapted Born-rule probability is the sum over the fibres of the coarse-graining. -/
theorem born_adapt (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (a' : A') (b' : B') :
    (S.adapt G' qA qB rA rB).born x' y' a' b'
      = ∑ a ∈ Finset.univ.filter (fun a => rA x' a = a'),
          ∑ b ∈ Finset.univ.filter (fun b => rB y' b = b'), S.born (qA x') (qB y') a b := by
  have hsplit : ((S.PA.mergeAt qA rA).M x' a' ⊗ₖ (S.PB.mergeAt qB rB).M y' b')
      = ∑ a ∈ Finset.univ.filter (fun a => rA x' a = a'),
          ∑ b ∈ Finset.univ.filter (fun b => rB y' b = b'),
            S.PA.M (qA x') a ⊗ₖ S.PB.M (qB y') b := by
    ext p q
    simp only [ProjectiveMeasurement.mergeAt_M, Matrix.sum_apply, kroneckerMap_apply,
      Finset.sum_mul_sum]
  show (star S.ψ ⬝ᵥ (((S.PA.mergeAt qA rA).M x' a' ⊗ₖ
    (S.PB.mergeAt qB rB).M y' b') *ᵥ S.ψ)).re = _
  rw [hsplit, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  rfl

/-- The adapted conditional success probability, as a sum over `G`'s answers: the
coarse-graining disappears into the decision predicate. -/
theorem succAt_adapt_eq (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y') :
    (S.adapt G' qA qB rA rB).succAt x' y'
      = ∑ a, ∑ b, (if G'.D x' y' (rA x' a) (rB y' b) then 1 else 0)
          * S.born (qA x') (qB y') a b := by
  unfold succAt
  simp_rw [born_adapt]
  rw [← sum_sum_fiberwise₂ (rA x') (rB y')
    (fun a b => (if G'.D x' y' (rA x' a) (rB y' b) then 1 else 0)
      * S.born (qA x') (qB y') a b)]
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2]

/-- **The adapter does not lose acceptance.** If every tuple `G` accepts at `(qA x', qB y')` is
still accepted by `G'` at `(x', y')` after coarse-graining, the adapted strategy succeeds at
least as often there. -/
theorem succAt_le_succAt_adapt (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (hD : ∀ a b, G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    S.succAt (qA x') (qB y') ≤ (S.adapt G' qA qB rA rB).succAt x' y' := by
  rw [succAt_adapt_eq]
  unfold succAt
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (S.born_nonneg _ _ a b)
  by_cases h : G.D (qA x') (qB y') a b = true
  · rw [if_pos h, if_pos (hD a b h)]
  · rw [if_neg h]
    split_ifs <;> norm_num

/-- Equivalently: the adapted strategy fails no more often. -/
theorem failAt_adapt_le (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (hD : ∀ a b, G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    (S.adapt G' qA qB rA rB).failAt x' y' ≤ S.failAt (qA x') (qB y') := by
  simp only [failAt]
  linarith [succAt_le_succAt_adapt S G' qA qB rA rB x' y' hD]

/-! ## The cost of the adapter is the push-forward of the distribution -/

variable [DecidableEq X] [DecidableEq Y]

/-- The failure of the adapted strategy, bounded by `G`'s failure weighted by the push-forward
of `G'`'s distribution. -/
theorem one_sub_value_adapt_le_sum (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B')
    (hD : ∀ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    1 - (S.adapt G' qA qB rA rB).value
      ≤ ∑ x, ∑ y, (∑ x' ∈ Finset.univ.filter (fun x' => qA x' = x),
          ∑ y' ∈ Finset.univ.filter (fun y' => qB y' = y), G'.μ x' y') * S.failAt x y := by
  rw [one_sub_value_eq_sum_failAt]
  calc ∑ x', ∑ y', G'.μ x' y' * (S.adapt G' qA qB rA rB).failAt x' y'
      ≤ ∑ x', ∑ y', G'.μ x' y' * S.failAt (qA x') (qB y') := by
        refine Finset.sum_le_sum fun x' _ => Finset.sum_le_sum fun y' _ => ?_
        by_cases hz : G'.μ x' y' = 0
        · rw [hz, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left
            (failAt_adapt_le S G' qA qB rA rB x' y' (fun a b => hD x' y' a b hz))
            (G'.μ_nonneg x' y')
    _ = ∑ x, ∑ y, (∑ x' ∈ Finset.univ.filter (fun x' => qA x' = x),
          ∑ y' ∈ Finset.univ.filter (fun y' => qB y' = y), G'.μ x' y') * S.failAt x y := by
        rw [← sum_sum_fiberwise₂ qA qB (fun x' y' => G'.μ x' y' * S.failAt (qA x') (qB y'))]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x' hx' => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun y' hy' => ?_
        rw [(Finset.mem_filter.1 hx').2, (Finset.mem_filter.1 hy').2]

/-- **The cost of the adapter.** If the push-forward of `G'`'s question distribution along
`(qA, qB)` is dominated by `C` times `G`'s, the adapted strategy's failure is at most `C` times
`S`'s. -/
theorem one_sub_value_adapt_le (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (C : ℝ)
    (hD : ∀ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true)
    (hμ : ∀ x y, (∑ x' ∈ Finset.univ.filter (fun x' => qA x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qB y' = y), G'.μ x' y') ≤ C * G.μ x y) :
    1 - (S.adapt G' qA qB rA rB).value ≤ C * (1 - S.value) := by
  refine (one_sub_value_adapt_le_sum S G' qA qB rA rB hD).trans ?_
  rw [one_sub_value_eq_sum_failAt, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hμ x y) (S.failAt_nonneg x y)

/-! ## Derandomization -/

/-- **The averaged form of `one_sub_value_adapt_le`.** The push-forward bound need only hold on
average over a finite family of question maps; some member of the family then achieves the
conclusion. This is how a reduction that must *choose* a preimage of each target question pays
back the size of the fibre. -/
theorem exists_one_sub_value_adapt_le {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : Seed → X' → X) (qB : Seed → Y' → Y) (rA : Seed → X' → A → A')
    (rB : Seed → Y' → B → B') (C : ℝ)
    (hD : ∀ σ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA σ x') (qB σ y') a b = true → G'.D x' y' (rA σ x' a) (rB σ y' b) = true)
    (hμ : ∀ x y, (∑ σ, ∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y')
      ≤ (Fintype.card Seed : ℝ) * (C * G.μ x y)) :
    ∃ σ : Seed,
      1 - (S.adapt G' (qA σ) (qB σ) (rA σ) (rB σ)).value ≤ C * (1 - S.value) := by
  classical
  have hsum : ∑ σ : Seed, (1 - (S.adapt G' (qA σ) (qB σ) (rA σ) (rB σ)).value)
      ≤ ∑ _σ : Seed, C * (1 - S.value) := by
    calc ∑ σ : Seed, (1 - (S.adapt G' (qA σ) (qB σ) (rA σ) (rB σ)).value)
        ≤ ∑ σ : Seed, ∑ x, ∑ y, (∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
            ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y') * S.failAt x y :=
          Finset.sum_le_sum fun σ _ =>
            one_sub_value_adapt_le_sum S G' (qA σ) (qB σ) (rA σ) (rB σ) (hD σ)
      _ = ∑ x, ∑ y, (∑ σ : Seed, ∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
            ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y') * S.failAt x y := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_mul]
      _ ≤ ∑ x, ∑ y, ((Fintype.card Seed : ℝ) * (C * G.μ x y)) * S.failAt x y := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
          exact mul_le_mul_of_nonneg_right (hμ x y) (S.failAt_nonneg x y)
      _ = (Fintype.card Seed : ℝ) * (C * (1 - S.value)) := by
          rw [one_sub_value_eq_sum_failAt, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ _σ : Seed, C * (1 - S.value) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  obtain ⟨σ, _, hσ⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty (α := Seed)) hsum
  exact ⟨σ, hσ⟩

end Adapt

end TensorProductStrategy

end MIPRE
