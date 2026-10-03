/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.Freeze

@[expose] public section

/-!
# The classes of the compressibility criterion, at the level of verifiers

Blueprint `rem:compression-abstract`, item 1: the classes the criterion is instantiated with
are, at level `n`, the strings whose verifier is `n`-bounded, rejects every answer longer than
the answer bound at index `n`, and has a value-`1` PCC strategy there (`A n`), and those that
are `n`-bounded, reject long answers, and have value at most `1/2` there (`B n`) — in a value
model `ω` (`ValueModel`): `val*` for the halting reduction of `MIP* = RE`, `ω_co` for the one of
`MIP^co = coRE` (`planning/mipco-track.md`). This file is the part that does not depend on how
a string is read as a verifier: the two conditions themselves (`Verifier.InClassA`,
`Verifier.InClassB`), their disjointness, and the two distinguished verifiers the criterion
needs.

The rejection clause (`Verifier.RejectsLong`) is what the paper's `V^halt` has by construction
— Step 6 of its decider is an explicit length check, and the amended proof of
`lem:dhalt-values` spends it to identify the answer alphabets of `V^halt_n` and `V^compr_n`.
Over arbitrary strings it has to be asked for: without it the soundness direction of the
compressor's obligation cannot raise the answer bound from the one a class is read with to
the one `GapCompression.soundness` takes its hypothesis at (`Verifier.val_eq_of_rejects`
is the step, and `val_le_of_le` goes the wrong way). `planning/h4-assembly.md` §4 item 4
has the argument, and the choice to put the clause in the classes rather than through the
criterion.

* `Verifier.InClassA n T`, `Verifier.InClassB ω n T` and `not_inClassB_of_inClassA`: the
  classes are disjoint in every model, because a perfect PCC strategy gives value `1`
  (`Verifier.val_eq_one_of_hasPerfectPCC`).
* `Verifier.hasPerfectPCC_of_accepts_diagonal`: a decider that accepts the constant answer `a₀`
  on every question pair has a value-`1` PCC strategy there — the paper's "trivial strategy:
  for all questions the players return a fixed answer", which is where `y_yes` comes from.
  `HasPerfectPCC` lives on the doubled game, so nothing is asked of the decider on the
  diagonal; `y_yes` still accepts only the empty answers, which keeps it rejecting long ones.
* `Verifier.valStar_eq_zero_of_rejects_all`: a decider that
  accepts nothing at `n` gives value `0` in every model, where `y_no` comes from.

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

/-- The class `B` at level `n` in the value model `ω`, with answer-length bound `T`: the verifier
is `n`-bounded, its decider rejects every answer longer than `T` at index `n`, and its `n`-th
game has value at most `1/2` in the model. -/
def InClassB (ω : ValueModel) (n T : ℕ) : Prop :=
  V.IsBounded n ∧ V.RejectsLong n T ∧ V.val ω n T ≤ 1 / 2

/-- The two classes are disjoint: a perfect PCC strategy gives value `1` in every model. -/
theorem not_inClassB_of_inClassA (ω : ValueModel) {n T : ℕ} (h : V.InClassA n T) :
    ¬ V.InClassB ω n T := by
  rintro ⟨-, -, hle⟩
  rw [V.val_eq_one_of_hasPerfectPCC ω h.2.2] at hle
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

/-- A decider that accepts nothing at index `n` gives quantum value `0`. -/
theorem valStar_eq_zero_of_rejects_all {n T : ℕ}
    (hrej : ∀ x y a b, ¬ V.decider.Accepts n x y a b) : V.valStar n T = 0 :=
  V.val_eq_zero_of_rejects_all .tensor hrej

/-- A verifier that accepts nothing at index `n` and is `n`-bounded is in the class `B` of every
model. -/
theorem inClassB_of_rejects_all (ω : ValueModel) {n T : ℕ} (hb : V.IsBounded n)
    (hrej : ∀ x y a b, ¬ V.decider.Accepts n x y a b) : V.InClassB ω n T := by
  refine ⟨hb, fun x y a b _ => hrej x y a b, ?_⟩
  rw [V.val_eq_zero_of_rejects_all ω hrej]
  norm_num

/-- A verifier that is `n`-bounded, rejects long answers, and accepts a constant answer
everywhere is in the class `A`. -/
theorem inClassA_of_accepts_diagonal {n T : ℕ} (hb : V.IsBounded n) (hrej : V.RejectsLong n T)
    (a₀ : Answers T)
    (hacc : ∀ x y : V.Questions n, V.decider.Accepts n (CL.toBits x) (CL.toBits y) a₀.1 a₀.1) :
    V.InClassA n T :=
  ⟨hb, hrej, V.hasPerfectPCC_of_accepts_diagonal a₀ hacc⟩

/-! ## Transport along the frozen verifier -/

theorem freeze_inClassB (ω : ValueModel) {k n T : ℕ} (hb : (V.freeze k).IsBounded n)
    (hrej : V.RejectsLong k T) (h : V.val ω k T ≤ 1 / 2) : (V.freeze k).InClassB ω n T :=
  ⟨hb, (V.freeze_rejectsLong k n T).2 hrej, by rw [V.freeze_val ω k n T]; exact h⟩

end Verifier

end MIPRE

end
