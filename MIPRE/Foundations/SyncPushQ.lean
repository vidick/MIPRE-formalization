/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.GameTransport
import MIPRE.Foundations.PerfectStrategy

/-!
# Playing a synchronous strategy through a reading of the questions

The honest strategy of a compiled game often measures an old strategy at a question computed from
the new one, and post-processes the outcome with a map that may depend on the new question. For
answer reduction (AR-4 of `planning/answer-reduction.md`) the old game is the oracularized one:
each player measures at the oracularized question its seed's oracle half determines, and answers
the low-degree encoding of the outcome that its PCP question asks for.

`SyncStrategy.pushQ` is that strategy: at a new question `x'`, the operator for `a'` is the sum
of the old operators at `g x'` over the outcomes `f x'` sends to `a'`. It is projective because
distinct old outcomes are orthogonal.

* `isPCC_pushQ` — it is PCC when the old one is, provided every new pair of positive weight is
  read as an old pair of positive weight.
* `value_pushQ_eq_one` — it has value `1` when the old strategy's operators for a rejected pair
  at a pair of positive weight multiply to zero, and every old pair accepted there (with both
  old answers accepted against themselves wherever that pair is asked) is read as an accepted
  new pair.

This generalizes `SyncStrategy.pushTo` of `MIPRE/Foundations/OracularTyped` (the case of the
identity reading and an answer map independent of the question), but proves value `1` rather
than monotonicity, which is what a question-dependent answer map allows.
-/

namespace MIPRE

open Finset

namespace SyncStrategy

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A] {G : SynchronousGame X A}

/-- The measurement played at `x'`: the old measurement at `g x'`, its outcomes pushed forward
along `f x'`. -/
noncomputable def pushQMeas (S : SyncStrategy G) {X' A' : Type*} [Fintype A'] [DecidableEq A']
    (g : X' → X) (f : X' → A → A') :
    ProjectiveMeasurement X' A' (Matrix (Fin S.d) (Fin S.d) ℂ) where
  M x' a' := ∑ u ∈ univ.filter fun u => f x' u = a', S.P.M (g x') u
  selfAdjoint x' a' := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun u _ => S.P.selfAdjoint (g x') u
  projective x' a' := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    refine Finset.sum_eq_single_of_mem u hu ?_ |>.trans (S.P.projective (g x') u)
    intro v _ hvu
    exact S.orthogonal (g x') (Ne.symm hvu)
  normalized x' := by
    rw [Finset.sum_fiberwise_of_maps_to (fun u _ => mem_univ (f x' u))]
    exact S.P.normalized (g x')

/-- **The strategy read through `g` and `f`**, on another synchronous game. -/
noncomputable def pushQ (S : SyncStrategy G) {X' A' : Type*} [Fintype X'] [Fintype A']
    [DecidableEq A'] (G' : SynchronousGame X' A') (g : X' → X) (f : X' → A → A') :
    SyncStrategy G' :=
  ⟨S.d, S.d_pos, S.pushQMeas g f⟩

theorem pushQ_M (S : SyncStrategy G) {X' A' : Type*} [Fintype X'] [Fintype A'] [DecidableEq A']
    (G' : SynchronousGame X' A') (g : X' → X) (f : X' → A → A') (x' : X') (a' : A') :
    (S.pushQ G' g f).P.M x' a' = ∑ u ∈ univ.filter fun u => f x' u = a', S.P.M (g x') u := rfl

/-- **The read strategy is PCC** when the old one is and pairs of positive weight are read as
pairs of positive weight. -/
theorem isPCC_pushQ {S : SyncStrategy G} (hS : S.IsPCC) {X' A' : Type*} [Fintype X']
    [Fintype A'] [DecidableEq A'] (G' : SynchronousGame X' A') (g : X' → X)
    (f : X' → A → A') (hμ : ∀ x' y', 0 < G'.μ x' y' → 0 < G.μ (g x') (g y')) :
    (S.pushQ G' g f).IsPCC := by
  intro x' y' hxy a' b'
  change (∑ a ∈ univ.filter fun a => f x' a = a', S.P.M (g x') a) *
      (∑ b ∈ univ.filter fun b => f y' b = b', S.P.M (g y') b)
    = (∑ b ∈ univ.filter fun b => f y' b = b', S.P.M (g y') b) *
      (∑ a ∈ univ.filter fun a => f x' a = a', S.P.M (g x') a)
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
    hS (g x') (g y') (hμ x' y' hxy) a b

/-- **The read strategy has value `1`.** The old strategy's operators for a rejected pair at a
pair of positive weight multiply to zero (`hZ`, the strong form of value `1` that a PCC
strategy of value `1` has, e.g. `SeededGame.oracleOp_mul_eq_zero`). Every new pair `(x', y')`
of positive weight is read as an old pair of positive weight, and an old answer pair accepted
there — with each answer also accepted against itself at its own question, when that pair has
positive weight — is read as an accepted new pair. -/
theorem value_pushQ_eq_one (S : SyncStrategy G) {X' A' : Type*} [Fintype X'] [Fintype A']
    [DecidableEq A'] (G' : SynchronousGame X' A') (g : X' → X) (f : X' → A → A')
    (hZ : ∀ x y, 0 < G.μ x y → ∀ a b, G.D x y a b = false → S.P.M x a * S.P.M y b = 0)
    (h : ∀ x' y', 0 < G'.μ x' y' → 0 < G.μ (g x') (g y') ∧ ∀ a b,
      (0 < G.μ (g x') (g x') → G.D (g x') (g x') a a = true) →
      (0 < G.μ (g y') (g y') → G.D (g y') (g y') b b = true) →
      G.D (g x') (g y') a b = true → G'.D x' y' (f x' a) (f y' b) = true) :
    (S.pushQ G' g f).value = 1 := by
  rw [value_eq_tracialValue]
  refine tracialValue_eq_one_of_re_eq_zero G' _ _ ?_
  intro x' y' hxy a' b' hrej
  obtain ⟨hμ, hacc⟩ := h x' y' hxy
  have hprod : (S.pushQ G' g f).P.M x' a' * (S.pushQ G' g f).P.M y' b' = 0 := by
    change (∑ a ∈ univ.filter fun a => f x' a = a', S.P.M (g x') a) *
      (∑ b ∈ univ.filter fun b => f y' b = b', S.P.M (g y') b) = 0
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    have ha' := (Finset.mem_filter.1 ha).2
    have hb' := (Finset.mem_filter.1 hb).2
    by_cases hA : 0 < G.μ (g x') (g x') ∧ G.D (g x') (g x') a a = false
    · have h0 : S.P.M (g x') a = 0 := by
        rw [← S.P.projective (g x') a]
        exact hZ _ _ hA.1 a a hA.2
      rw [h0, Matrix.zero_mul]
    by_cases hB : 0 < G.μ (g y') (g y') ∧ G.D (g y') (g y') b b = false
    · have h0 : S.P.M (g y') b = 0 := by
        rw [← S.P.projective (g y') b]
        exact hZ _ _ hB.1 b b hB.2
      rw [h0, Matrix.mul_zero]
    by_cases hD : G.D (g x') (g y') a b = true
    · have := hacc a b (fun hp => by simpa [hp] using hA) (fun hp => by simpa [hp] using hB) hD
      rw [ha', hb', hrej] at this
      exact absurd this Bool.false_ne_true
    · exact hZ _ _ hμ a b (by simpa using hD)
  rw [hprod, normalizedTrace_apply, Matrix.trace_zero, mul_zero, Complex.zero_re]

end SyncStrategy

end MIPRE
