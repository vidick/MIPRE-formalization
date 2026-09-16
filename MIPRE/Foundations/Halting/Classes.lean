/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Freeze

/-!
# The classes of the compressibility criterion, at the level of verifiers

Blueprint `rem:compression-abstract`, item 1: the classes the criterion is instantiated with
are, at level `n`, the strings whose verifier is `n`-bounded, rejects every answer longer than
the answer bound at index `n`, and has a value-`1` PCC strategy there (`A n`), and those that
are `n`-bounded, reject long answers, and have `val* ≤ 1/2` there (`B n`). This file is the
part that does not depend on how a string is read as a verifier: the two conditions themselves
(`Verifier.InClassA`, `Verifier.InClassB`), their disjointness, and the two distinguished
verifiers the criterion needs.

The rejection clause (`Verifier.RejectsLong`) is what the paper's `V^halt` has by construction
— Step 6 of its decider is an explicit length check, and the amended proof of
`lem:dhalt-values` spends it to identify the answer alphabets of `V^halt_n` and `V^compr_n`.
Over arbitrary strings it has to be asked for: without it the soundness direction of the
compressor's obligation cannot raise the answer bound from the one a class is read with to
the one `GapCompression.soundness` takes its hypothesis at (`Verifier.valStar_eq_of_rejects`
is the step, and `valStar_le_of_le` goes the wrong way). `planning/h4-assembly.md` §4 item 4
has the argument, and the choice to put the clause in the classes rather than through the
criterion.

* `Verifier.InClassA n T`, `Verifier.InClassB n T` and `not_inClassB_of_inClassA`: the classes
  are disjoint, because a perfect PCC strategy gives `val* = 1`
  (`Verifier.valStar_eq_one_of_hasPerfectPCC`).
* `Verifier.hasPerfectPCC_of_accepts_diagonal`: a decider that accepts the constant answer `a₀`
  on every question pair has a value-`1` PCC strategy there — the paper's "trivial strategy:
  for all questions the players return a fixed answer", which is where `y_yes` comes from.
  `HasPerfectPCC` lives on the doubled game, so nothing is asked of the decider on the
  diagonal; `y_yes` still accepts only the empty answers, which keeps it rejecting long ones.
* `Verifier.valStar_eq_zero_of_rejects_all` and `isSynchronousAt_of_rejects_all`: a decider that
  accepts nothing at `n` gives `val* = 0`, where `y_no` comes from.

What remains for the classes is the reading of a string as a verifier — the wrapper decider
around the string's own decider — and the two strings realizing these verifiers
(`planning/formalization-plan.md`, H4).
-/

namespace MIPRE

open Cost

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-! ## The classes -/

/-- The class `A` at level `n`, with answer-length bound `T`: the verifier is `n`-bounded, its
decider rejects every answer longer than `T` at index `n`, and its `n`-th game has a value-`1`
PCC strategy. -/
def InClassA (n T : ℕ) : Prop := V.IsBounded n ∧ V.RejectsLong n T ∧ V.HasPerfectPCC n T

/-- The class `B` at level `n`, with answer-length bound `T`: the verifier is `n`-bounded, its
decider rejects every answer longer than `T` at index `n`, and its `n`-th game has quantum
value at most `1/2`. -/
def InClassB (n T : ℕ) : Prop := V.IsBounded n ∧ V.RejectsLong n T ∧ V.valStar n T ≤ 1 / 2

/-- The two classes are disjoint: a perfect PCC strategy gives `val* = 1`. -/
theorem not_inClassB_of_inClassA {n T : ℕ} (h : V.InClassA n T) : ¬ V.InClassB n T := by
  rintro ⟨-, -, hle⟩
  rw [V.valStar_eq_one_of_hasPerfectPCC h.2.2] at hle
  norm_num at hle

/-! ## The trivially accepting verifier -/

/-- A decider that accepts the constant answer `a₀` on every question pair at index `n` has a
value-`1` PCC strategy: the players always answer `a₀`. No synchronicity is asked of the
decider: `HasPerfectPCC` lives on the doubled game, where the diagonal carries no weight. -/
theorem hasPerfectPCC_of_accepts_diagonal {n T : ℕ} (a₀ : Answers T)
    (hacc : ∀ x y : V.Questions n, V.decider.Accepts n (CL.toBits x) (CL.toBits y) a₀.1 a₀.1) :
    V.HasPerfectPCC n T := by
  classical
  refine ⟨SyncStrategy.const (V.doubledGame n T) a₀, SyncStrategy.isPCC_const _ _, ?_⟩
  rw [SyncStrategy.value_const]
  have hD : ∀ x y : V.Questions n, ((V.game n T).D x y a₀ a₀ = true) := fun x y =>
    decide_eq_true (hacc x y)
  calc ∑ p, ∑ q, (V.doubledGame n T).μ p q *
        (if (V.doubledGame n T).D p q a₀ a₀ then (1 : ℝ) else 0)
      = ∑ p, ∑ q, (V.doubledGame n T).μ p q := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        by_cases h : p.1 = false ∧ q.1 = true
        · simp [doubledGame, h, hD]
        · simp [doubledGame, h]
    _ = 1 := (V.doubledGame n T).μ_sum_one

/-! ## The trivially rejecting verifier -/

/-- A decider that accepts nothing at index `n` is synchronous there. -/
theorem isSynchronousAt_of_rejects_all {n : ℕ}
    (hrej : ∀ x y a b, ¬ V.decider.Accepts n x y a b) : V.IsSynchronousAt n :=
  fun x a b _ => hrej x x a b

/-- A decider that accepts nothing at index `n` gives quantum value `0`. -/
theorem valStar_eq_zero_of_rejects_all {n T : ℕ}
    (hrej : ∀ x y a b, ¬ V.decider.Accepts n x y a b) : V.valStar n T = 0 := by
  classical
  refine quantumValue_eq_zero_of_reject _ fun x y a b => ?_
  exact decide_eq_false (hrej _ _ _ _)

/-- A verifier that accepts nothing at index `n` and is `n`-bounded is in the class `B`. -/
theorem inClassB_of_rejects_all {n T : ℕ} (hb : V.IsBounded n)
    (hrej : ∀ x y a b, ¬ V.decider.Accepts n x y a b) : V.InClassB n T := by
  refine ⟨hb, fun x y a b _ => hrej x y a b, ?_⟩
  rw [V.valStar_eq_zero_of_rejects_all hrej]
  norm_num

/-- A verifier that is `n`-bounded, rejects long answers, and accepts a constant answer
everywhere is in the class `A`. -/
theorem inClassA_of_accepts_diagonal {n T : ℕ} (hb : V.IsBounded n) (hrej : V.RejectsLong n T)
    (a₀ : Answers T)
    (hacc : ∀ x y : V.Questions n, V.decider.Accepts n (CL.toBits x) (CL.toBits y) a₀.1 a₀.1) :
    V.InClassA n T :=
  ⟨hb, hrej, V.hasPerfectPCC_of_accepts_diagonal a₀ hacc⟩

/-! ## Transport along the frozen verifier -/

/-- The frozen verifier's class membership at any index is the original's at the frozen index,
as far as the game is concerned (boundedness is transferred separately by
`Verifier.freeze_isBounded`). -/
theorem freeze_inClassA {k n T : ℕ} (hb : (V.freeze k).IsBounded n) (hrej : V.RejectsLong k T)
    (h : V.HasPerfectPCC k T) : (V.freeze k).InClassA n T :=
  ⟨hb, (V.freeze_rejectsLong k n T).2 hrej, (V.freeze_hasPerfectPCC k n T).2 h⟩

theorem freeze_inClassB {k n T : ℕ} (hb : (V.freeze k).IsBounded n) (hrej : V.RejectsLong k T)
    (h : V.valStar k T ≤ 1 / 2) : (V.freeze k).InClassB n T :=
  ⟨hb, (V.freeze_rejectsLong k n T).2 hrej, by rw [V.freeze_valStar k n T]; exact h⟩

end Verifier

end MIPRE
