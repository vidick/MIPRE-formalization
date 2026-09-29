/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.CrossConsistency
public import MIPRE.Foundations.GameTransport

@[expose] public section

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

## In a bipartite model

A strategy in a bipartite model is a POVM family in each player's algebra and its value is
`BipartiteModel.povmValue`; the adapted strategy is `fun x' => (MA (qA x')).map (rA x')`, and every
statement above is proved once for it (`BipartiteModel.condWin_adapt`,
`BipartiteModel.one_sub_povmValue_adapt_le`, ...). A tensor-product strategy is the strategy of its
measurements in its tensor-product model (`TensorProductStrategy.value_eq_tensor_povmValue`), and
its adapted strategy the model's (`TensorProductStrategy.value_adapt`), so the statements about
`TensorProductStrategy.adapt` are instances.
-/

namespace MIPRE

open Matrix Kronecker Finset
open scoped ComplexOrder MatrixOrder

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

omit [Fintype X] [Fintype Y] in
/-- **The push-forward of a distribution over a family of question maps, counted the other way
round.** Summing over the family and then over the fibres is the same as summing over the target
pairs weighted by *how many members of the family* send them where they need to go.

This is the form in which the push-forward bound of `exists_one_sub_value_adapt_le` is checked in
practice: the count is usually easy, because a member of the family typically constrains only a
small part of the question, while the fibres of the maps themselves are awkward to describe. -/
theorem sum_sum_fibre_eq_sum_card {Seed : Type*} [Fintype Seed] [DecidableEq X] [DecidableEq Y]
    (qA : Seed → X' → X) (qB : Seed → Y' → Y) (w : X' → Y' → ℝ) (x : X) (y : Y) :
    (∑ σ : Seed, ∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), w x' y')
      = ∑ x', ∑ y', w x' y' *
          (Finset.univ.filter (fun σ : Seed => qA σ x' = x ∧ qB σ y' = y)).card := by
  classical
  have hstep : ∀ σ : Seed, (∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
      ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), w x' y')
      = ∑ x', ∑ y', (if qA σ x' = x ∧ qB σ y' = y then w x' y' else 0) := by
    intro σ
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.sum_filter]
    by_cases hx : qA σ x' = x
    · rw [if_pos hx]
      exact Finset.sum_congr rfl fun y' _ => by
        by_cases hy : qB σ y' = y
        · rw [if_pos hy, if_pos ⟨hx, hy⟩]
        · rw [if_neg hy, if_neg (fun hc => hy hc.2)]
    · rw [if_neg hx, Finset.sum_eq_zero fun y' _ => if_neg (fun hc => hx hc.1)]
  rw [Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => hstep σ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ## Playing a strategy through maps, in a bipartite model

A strategy in a bipartite model is a family of POVMs in each player's algebra, and its value is
`BipartiteModel.povmValue` (`TensorProductStrategy.value_eq_povmValue` and
`povmValue_eq_tensor` in the tensor-product model; `CommutingOperatorStrategy.value_eq_povmValue`
in the commuting-operator model). Playing it on another game through a map of questions and a
coarse-graining of answers is `fun x' => (MA (qA x')).map (rA x')`, and everything below is
proved once for it; the statements about `TensorProductStrategy.adapt` further down are its
instances. -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  {G : Game X Y A B} (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ)

section Adapt

variable [DecidableEq A'] [DecidableEq B']

omit [Fintype X] [Fintype Y] in
/-- **The adapted conditional acceptance**, as a sum over the original answers: the
coarse-graining disappears into the decision predicate. -/
theorem condWin_adapt (G' : Game X' Y' A' B') (qA : X' → X) (qB : Y' → Y)
    (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y') :
    M.condWin G' (fun x' => (MA (qA x')).map (rA x')) (fun y' => (MB (qB y')).map (rB y')) x' y'
      = ∑ a, ∑ b, (if G'.D x' y' (rA x' a) (rB y' b) then 1 else 0)
          * M.bornProb ((MA (qA x')).op a) ((MB (qB y')).op b) :=
  M.sum_weight_bornProb_map (MA (qA x')) (MB (qB y')) (rA x') (rB y')
    fun a' b' => if G'.D x' y' a' b' then 1 else 0

/-- **The adapter does not lose acceptance** where every tuple `G` accepts is still accepted
after coarse-graining. -/
theorem condWin_le_condWin_adapt (G' : Game X' Y' A' B') (qA : X' → X) (qB : Y' → Y)
    (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (hD : ∀ a b, G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    M.condWin G MA MB (qA x') (qB y')
      ≤ M.condWin G' (fun x' => (MA (qA x')).map (rA x'))
          (fun y' => (MB (qB y')).map (rB y')) x' y' := by
  rw [M.condWin_adapt, condWin]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  refine mul_le_mul_of_nonneg_right ?_
    (M.bornProb_nonneg ((MA (qA x')).op_nonneg a) ((MB (qB y')).op_nonneg b))
  by_cases h : G.D (qA x') (qB y') a b = true
  · rw [ite_eq_left h, ite_eq_left (hD a b h)]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num

/-- Equivalently: the adapted strategy fails no more often. -/
theorem condFail_adapt_le (G' : Game X' Y' A' B') (qA : X' → X) (qB : Y' → Y)
    (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (hD : ∀ a b, G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    M.condFail G' (fun x' => (MA (qA x')).map (rA x'))
        (fun y' => (MB (qB y')).map (rB y')) x' y'
      ≤ M.condFail G MA MB (qA x') (qB y') := by
  simp only [condFail]
  linarith [M.condWin_le_condWin_adapt MA MB G' qA qB rA rB x' y' hD]

/-- **Relabeling a strategy along equivalences keeps its value**: the model form of
`TensorProductStrategy.value_relabel`, and the content of `ValueModel.eq_of_equiv` for a strategy
in a model. -/
theorem povmValue_relabel (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y) (eA : A' ≃ A)
    (eB : B' ≃ B) (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    M.povmValue G' (fun x' => (MA (eX x')).map eA.symm)
        (fun y' => (MB (eY y')).map eB.symm)
      = M.povmValue G MA MB := by
  have hcw : ∀ x' y', M.condWin G' (fun x' => (MA (eX x')).map eA.symm)
      (fun y' => (MB (eY y')).map eB.symm) x' y' = M.condWin G MA MB (eX x') (eY y') := by
    intro x' y'
    rw [M.condWin_adapt MA MB G' eX eY (fun _ => ⇑eA.symm) (fun _ => ⇑eB.symm) x' y', condWin]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hD, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  unfold povmValue
  simp only [hcw, hμ]
  rw [← eX.sum_comp fun x => ∑ y, G.μ x y * M.condWin G MA MB x y]
  exact Finset.sum_congr rfl fun x' _ =>
    eY.sum_comp fun y => G.μ (eX x') y * M.condWin G MA MB (eX x') y

variable [DecidableEq X] [DecidableEq Y]

/-- The failure of the adapted strategy, bounded by `G`'s conditional failures weighted by the
push-forward of `G'`'s distribution. -/
theorem one_sub_povmValue_adapt_le_sum (G' : Game X' Y' A' B') (qA : X' → X)
    (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B')
    (hD : ∀ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    1 - M.povmValue G' (fun x' => (MA (qA x')).map (rA x'))
        (fun y' => (MB (qB y')).map (rB y'))
      ≤ ∑ x, ∑ y, (∑ x' ∈ Finset.univ.filter (fun x' => qA x' = x),
          ∑ y' ∈ Finset.univ.filter (fun y' => qB y' = y), G'.μ x' y')
            * M.condFail G MA MB x y := by
  rw [M.one_sub_povmValue_eq]
  calc ∑ x', ∑ y', G'.μ x' y' * M.condFail G' (fun x' => (MA (qA x')).map (rA x'))
          (fun y' => (MB (qB y')).map (rB y')) x' y'
      ≤ ∑ x', ∑ y', G'.μ x' y' * M.condFail G MA MB (qA x') (qB y') := by
        refine Finset.sum_le_sum fun x' _ => Finset.sum_le_sum fun y' _ => ?_
        by_cases hz : G'.μ x' y' = 0
        · rw [hz, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left
            (M.condFail_adapt_le MA MB G' qA qB rA rB x' y' (fun a b => hD x' y' a b hz))
            (G'.μ_nonneg x' y')
    _ = ∑ x, ∑ y, (∑ x' ∈ Finset.univ.filter (fun x' => qA x' = x),
          ∑ y' ∈ Finset.univ.filter (fun y' => qB y' = y), G'.μ x' y')
            * M.condFail G MA MB x y := by
        rw [← sum_sum_fiberwise₂ qA qB
          (fun x' y' => G'.μ x' y' * M.condFail G MA MB (qA x') (qB y'))]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x' hx' => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun y' hy' => ?_
        rw [(Finset.mem_filter.1 hx').2, (Finset.mem_filter.1 hy').2]

/-- **The cost of the adapter.** If the push-forward of `G'`'s question distribution along
`(qA, qB)` is dominated by `C` times `G`'s, the adapted strategy's failure is at most `C` times
the original's. -/
theorem one_sub_povmValue_adapt_le (hψ : ‖M.ψ‖ = 1) (G' : Game X' Y' A' B') (qA : X' → X)
    (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (C : ℝ)
    (hD : ∀ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true)
    (hμ : ∀ x y, (∑ x' ∈ Finset.univ.filter (fun x' => qA x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qB y' = y), G'.μ x' y') ≤ C * G.μ x y) :
    1 - M.povmValue G' (fun x' => (MA (qA x')).map (rA x'))
        (fun y' => (MB (qB y')).map (rB y'))
      ≤ C * (1 - M.povmValue G MA MB) := by
  refine (M.one_sub_povmValue_adapt_le_sum MA MB G' qA qB rA rB hD).trans ?_
  rw [M.one_sub_povmValue_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hμ x y) (M.condFail_nonneg hψ x y)

/-- **The summed form of `one_sub_povmValue_adapt_le`** over a finite family of question maps,
when the push-forward bound holds on average. -/
theorem sum_one_sub_povmValue_adapt_le {Seed : Type*} [Fintype Seed] (hψ : ‖M.ψ‖ = 1)
    (G' : Game X' Y' A' B') (qA : Seed → X' → X) (qB : Seed → Y' → Y)
    (rA : Seed → X' → A → A') (rB : Seed → Y' → B → B') (C : ℝ)
    (hD : ∀ σ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA σ x') (qB σ y') a b = true → G'.D x' y' (rA σ x' a) (rB σ y' b) = true)
    (hμ : ∀ x y, (∑ σ, ∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y')
      ≤ (Fintype.card Seed : ℝ) * (C * G.μ x y)) :
    ∑ σ : Seed, (1 - M.povmValue G' (fun x' => (MA (qA σ x')).map (rA σ x'))
        (fun y' => (MB (qB σ y')).map (rB σ y')))
      ≤ (Fintype.card Seed : ℝ) * (C * (1 - M.povmValue G MA MB)) := by
  calc ∑ σ : Seed, (1 - M.povmValue G' (fun x' => (MA (qA σ x')).map (rA σ x'))
        (fun y' => (MB (qB σ y')).map (rB σ y')))
      ≤ ∑ σ : Seed, ∑ x, ∑ y, (∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
          ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y')
            * M.condFail G MA MB x y :=
        Finset.sum_le_sum fun σ _ =>
          M.one_sub_povmValue_adapt_le_sum MA MB G' (qA σ) (qB σ) (rA σ) (rB σ) (hD σ)
    _ = ∑ x, ∑ y, (∑ σ : Seed, ∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
          ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y')
            * M.condFail G MA MB x y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
    _ ≤ ∑ x, ∑ y, ((Fintype.card Seed : ℝ) * (C * G.μ x y)) * M.condFail G MA MB x y := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        exact mul_le_mul_of_nonneg_right (hμ x y) (M.condFail_nonneg hψ x y)
    _ = (Fintype.card Seed : ℝ) * (C * (1 - M.povmValue G MA MB)) := by
        rw [M.one_sub_povmValue_eq, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring

/-- **The averaged form of `one_sub_povmValue_adapt_le`**: some member of a finite family of
question maps achieves the conclusion when the push-forward bound holds on average. -/
theorem exists_one_sub_povmValue_adapt_le {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (hψ : ‖M.ψ‖ = 1) (G' : Game X' Y' A' B') (qA : Seed → X' → X) (qB : Seed → Y' → Y)
    (rA : Seed → X' → A → A') (rB : Seed → Y' → B → B') (C : ℝ)
    (hD : ∀ σ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA σ x') (qB σ y') a b = true → G'.D x' y' (rA σ x' a) (rB σ y' b) = true)
    (hμ : ∀ x y, (∑ σ, ∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y')
      ≤ (Fintype.card Seed : ℝ) * (C * G.μ x y)) :
    ∃ σ : Seed, 1 - M.povmValue G' (fun x' => (MA (qA σ x')).map (rA σ x'))
        (fun y' => (MB (qB σ y')).map (rB σ y')) ≤ C * (1 - M.povmValue G MA MB) := by
  have hsum := M.sum_one_sub_povmValue_adapt_le MA MB hψ G' qA qB rA rB C hD hμ
  rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const] at hsum
  obtain ⟨σ, _, hσ⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty (α := Seed)) hsum
  exact ⟨σ, hσ⟩

end Adapt

end BipartiteModel

namespace TensorProductStrategy

variable {G : Game X Y A B}

/-! ## Born-rule probabilities and the conditional success probability -/

/-- The Born-rule probability that `S` answers `(a, b)` to the question pair `(x, y)`. -/
noncomputable def born (S : TensorProductStrategy G) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re

/-- **The Born probability of a strategy is that of its tensor-product model.** -/
theorem born_eq_bornProb (S : TensorProductStrategy G) (x : X) (y : Y) (a : A) (b : B) :
    S.born x y a b = (BipartiteModel.tensor S.ψ).bornProb ((S.PA.toPOVM x).toIn.op a)
      ((S.PB.toPOVM y).toIn.op b) :=
  bornProb_eq_tensor S.ψ (S.PA.M x a) (S.PB.M y b)

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

/-- **The conditional success probability is that of the tensor-product model.** -/
theorem succAt_eq_condWin (S : TensorProductStrategy G) (x : X) (y : Y) :
    S.succAt x y = (BipartiteModel.tensor S.ψ).condWin G (fun x => (S.PA.toPOVM x).toIn)
      (fun y => (S.PB.toPOVM y).toIn) x y := by
  simp only [succAt, BipartiteModel.condWin, born_eq_bornProb]

theorem failAt_eq_condFail (S : TensorProductStrategy G) (x : X) (y : Y) :
    S.failAt x y = (BipartiteModel.tensor S.ψ).condFail G (fun x => (S.PA.toPOVM x).toIn)
      (fun y => (S.PB.toPOVM y).toIn) x y := by
  rw [failAt, succAt_eq_condWin, BipartiteModel.condFail]

theorem succAt_nonneg (S : TensorProductStrategy G) (x : X) (y : Y) : 0 ≤ S.succAt x y := by
  rw [succAt_eq_condWin]
  exact (BipartiteModel.tensor S.ψ).condWin_nonneg x y

theorem succAt_le_one (S : TensorProductStrategy G) (x : X) (y : Y) : S.succAt x y ≤ 1 := by
  rw [succAt_eq_condWin]
  exact (BipartiteModel.tensor S.ψ).condWin_le_one (norm_evec_eq_one S.ψ_unit) x y

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

/-- **The value of a strategy is the value of its measurements in its tensor-product model.** -/
theorem value_eq_tensor_povmValue (S : TensorProductStrategy G) :
    S.value = (BipartiteModel.tensor S.ψ).povmValue G (fun x => (S.PA.toPOVM x).toIn)
      (fun y => (S.PB.toPOVM y).toIn) := by
  rw [value_eq_sum_succAt]
  simp only [succAt_eq_condWin]
  rfl

/-- **The failure probability, decomposed by question pair.** -/
theorem one_sub_value_eq_sum_failAt (S : TensorProductStrategy G) :
    1 - S.value = ∑ x, ∑ y, G.μ x y * S.failAt x y := by
  rw [value_eq_tensor_povmValue, (BipartiteModel.tensor S.ψ).one_sub_povmValue_eq]
  simp only [failAt_eq_condFail]

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

omit [Fintype X] [Fintype X'] [DecidableEq A'] in
/-- The merged measurement is the coarse-graining of the original, as a POVM in the matrix
algebra. -/
theorem _root_.MIPRE.ProjectiveMeasurement.mergeAt_toIn {X X' A A' : Type*} [Fintype A]
    [Fintype A'] [DecidableEq A'] {n : Type*} [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (qX : X' → X) (r : X' → A → A') :
    (fun x' => ((P.mergeAt qX r).toPOVM x').toIn) = fun x' => (P.toPOVM (qX x')).toIn.map (r x') :=
  funext fun x' => POVMIn.ext' fun a' => by
    rw [POVMIn.map_op]
    rfl

/-- **The adapted strategy is the model's adapted strategy**: its value is the value, in the
tensor-product model of `S`, of the coarse-grained measurements. -/
theorem value_adapt (S : TensorProductStrategy G) (G' : Game X' Y' A' B') (qA : X' → X)
    (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') :
    (S.adapt G' qA qB rA rB).value
      = (BipartiteModel.tensor S.ψ).povmValue G'
          (fun x' => (S.PA.toPOVM (qA x')).toIn.map (rA x'))
          (fun y' => (S.PB.toPOVM (qB y')).toIn.map (rB y')) := by
  rw [value_eq_tensor_povmValue]
  show (BipartiteModel.tensor S.ψ).povmValue G' (fun x' => ((S.PA.mergeAt qA rA).toPOVM x').toIn)
    (fun y' => ((S.PB.mergeAt qB rB).toPOVM y').toIn) = _
  rw [ProjectiveMeasurement.mergeAt_toIn, ProjectiveMeasurement.mergeAt_toIn]

theorem succAt_adapt_eq_condWin (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y') :
    (S.adapt G' qA qB rA rB).succAt x' y'
      = (BipartiteModel.tensor S.ψ).condWin G'
          (fun x' => (S.PA.toPOVM (qA x')).toIn.map (rA x'))
          (fun y' => (S.PB.toPOVM (qB y')).toIn.map (rB y')) x' y' := by
  rw [succAt_eq_condWin]
  show (BipartiteModel.tensor S.ψ).condWin G' (fun x' => ((S.PA.mergeAt qA rA).toPOVM x').toIn)
    (fun y' => ((S.PB.mergeAt qB rB).toPOVM y').toIn) x' y' = _
  rw [ProjectiveMeasurement.mergeAt_toIn, ProjectiveMeasurement.mergeAt_toIn]

/-- The adapted Born-rule probability is the sum over the fibres of the coarse-graining. -/
theorem born_adapt (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (a' : A') (b' : B') :
    (S.adapt G' qA qB rA rB).born x' y' a' b'
      = ∑ a ∈ Finset.univ.filter (fun a => rA x' a = a'),
          ∑ b ∈ Finset.univ.filter (fun b => rB y' b = b'), S.born (qA x') (qB y') a b := by
  rw [born_eq_bornProb]
  show (BipartiteModel.tensor S.ψ).bornProb (((S.PA.mergeAt qA rA).toPOVM x').toIn.op a')
    (((S.PB.mergeAt qB rB).toPOVM y').toIn.op b') = _
  rw [congrFun (ProjectiveMeasurement.mergeAt_toIn S.PA qA rA) x',
    congrFun (ProjectiveMeasurement.mergeAt_toIn S.PB qB rB) y', POVMIn.map_op, POVMIn.map_op,
    BipartiteModel.bornProb_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [BipartiteModel.bornProb_sum_right]
  exact Finset.sum_congr rfl fun b _ => (born_eq_bornProb S _ _ a b).symm

/-- The adapted conditional success probability, as a sum over `G`'s answers: the
coarse-graining disappears into the decision predicate. -/
theorem succAt_adapt_eq (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y') :
    (S.adapt G' qA qB rA rB).succAt x' y'
      = ∑ a, ∑ b, (if G'.D x' y' (rA x' a) (rB y' b) then 1 else 0)
          * S.born (qA x') (qB y') a b := by
  rw [succAt_adapt_eq_condWin, (BipartiteModel.tensor S.ψ).condWin_adapt
    (fun x => (S.PA.toPOVM x).toIn) (fun y => (S.PB.toPOVM y).toIn) G' qA qB rA rB x' y']
  simp only [born_eq_bornProb]

/-- **The adapter does not lose acceptance.** If every tuple `G` accepts at `(qA x', qB y')` is
still accepted by `G'` at `(x', y')` after coarse-graining, the adapted strategy succeeds at
least as often there. -/
theorem succAt_le_succAt_adapt (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (hD : ∀ a b, G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    S.succAt (qA x') (qB y') ≤ (S.adapt G' qA qB rA rB).succAt x' y' := by
  rw [succAt_eq_condWin, succAt_adapt_eq_condWin]
  exact (BipartiteModel.tensor S.ψ).condWin_le_condWin_adapt (fun x => (S.PA.toPOVM x).toIn) (fun y => (S.PB.toPOVM y).toIn) G' qA qB rA rB x'
    y' hD

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
  rw [value_adapt]
  simp only [failAt_eq_condFail]
  exact (BipartiteModel.tensor S.ψ).one_sub_povmValue_adapt_le_sum (fun x => (S.PA.toPOVM x).toIn) (fun y => (S.PB.toPOVM y).toIn)
    G' qA qB rA rB hD

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
  rw [value_adapt, value_eq_tensor_povmValue]
  exact (BipartiteModel.tensor S.ψ).one_sub_povmValue_adapt_le (fun x => (S.PA.toPOVM x).toIn) (fun y => (S.PB.toPOVM y).toIn)
    (norm_evec_eq_one S.ψ_unit) G' qA qB rA rB C hD hμ

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
  simp only [value_adapt, value_eq_tensor_povmValue S]
  exact (BipartiteModel.tensor S.ψ).exists_one_sub_povmValue_adapt_le (fun x => (S.PA.toPOVM x).toIn) (fun y => (S.PB.toPOVM y).toIn)
    (norm_evec_eq_one S.ψ_unit) G' qA qB rA rB C hD hμ

/-- **The summed form of `one_sub_value_adapt_le`**: over a finite family of question maps, the
adapted strategies' failures add up to at most `|Seed| · C` times `S`'s, when the push-forward
bound holds on average. Each member is a genuine strategy for `G'`, so this is the form a
per-seed argument uses: it keeps every member, not only the best one. -/
theorem sum_one_sub_value_adapt_le {Seed : Type*} [Fintype Seed]
    (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : Seed → X' → X) (qB : Seed → Y' → Y) (rA : Seed → X' → A → A')
    (rB : Seed → Y' → B → B') (C : ℝ)
    (hD : ∀ σ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA σ x') (qB σ y') a b = true → G'.D x' y' (rA σ x' a) (rB σ y' b) = true)
    (hμ : ∀ x y, (∑ σ, ∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y')
      ≤ (Fintype.card Seed : ℝ) * (C * G.μ x y)) :
    ∑ σ : Seed, (1 - (S.adapt G' (qA σ) (qB σ) (rA σ) (rB σ)).value)
      ≤ (Fintype.card Seed : ℝ) * (C * (1 - S.value)) := by
  simp only [value_adapt, value_eq_tensor_povmValue S]
  exact (BipartiteModel.tensor S.ψ).sum_one_sub_povmValue_adapt_le (fun x => (S.PA.toPOVM x).toIn) (fun y => (S.PB.toPOVM y).toIn)
    (norm_evec_eq_one S.ψ_unit) G' qA qB rA rB C hD hμ

end Adapt

end TensorProductStrategy


end MIPRE

end
