/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Computability.Halting
import MIPRE.Foundations.Correlations
import MIPRE.Foundations.GameDescription

/-!
# Tsirelson's problem from an upper semidecider for the commuting-operator value

The non-explicit route to the negative answer to Tsirelson's problem (blueprint
`cor:tsirelson`), with its two analytic inputs as explicit hypotheses:

* `CommutingUpperRE`: the commuting-operator value is recursively enumerable from above, in
  the threshold encoding of `MIPRE.ValueApprox.rePred_lt_quantumValue` (a pair `(p, q)` stands
  for `p / q`, and `p / 0 = 0`);
* closedness of `C_qc` in every finite scenario.

The halting reduction of `cor:main-quantum` (`MIPRE.Halting.halting_reduction_quantum`) enters
as the hypothesis `hred`, whose type is that theorem's statement: it lives in the root module
`MIPRE.MainTheorem`, which `MIPRE/Foundations/` does not import.

The argument (`exists_quantumValue_lt_commutingOperatorValue`): if the two values agreed on
every described game, a machine would fail to halt exactly when the commuting-operator value of
its game is below `3/4` (the quantum value is `1` or at most `1/2`), so non-halting would be
r.e., which it is not (`ComputablePred.halting_problem_not_re`). A game whose commuting-operator
value exceeds its quantum value has a commuting-operator strategy that beats the quantum value,
and its correlation lies outside `C_qa`, since payoffs on `C_qa` are bounded by the quantum value
(`exists_mem_Cqc_not_mem_Cqa`). With `C_qc` closed, `C_qa ⊆ C_qc`, and the inclusion is strict
(`tsirelson_of_upperRE_of_isClosed`).
-/

namespace MIPRE

open HaltingGameValue (GameData HaltsOnEmptyInput)
open Nat.Partrec (Code)

/-- The halting reduction of `cor:main-quantum`, as a proposition: a computable map from codes
to game descriptions whose quantum value is `1` on halting codes and at most `1/2` on the
others. `MIPRE.Halting.halting_reduction_quantum` proves it. -/
def HaltingReductionQuantum : Prop :=
  ∃ g : Code → GameData, Computable g ∧
    ∀ pc : Code,
      (HaltsOnEmptyInput pc → quantumValue (g pc).game = 1) ∧
      (¬ HaltsOnEmptyInput pc → quantumValue (g pc).game ≤ 1 / 2)

/-- **The commuting-operator value is r.e. from above** (blueprint `lem:valco-upper-re`): the
pairs `(d, p, q)` with `valco(G_d) < p / q` form an r.e. set. The threshold encoding is that of
the lower semidecider `MIPRE.ValueApprox.rePred_lt_quantumValue`. -/
def CommutingUpperRE : Prop :=
  REPred fun x : GameData × ℕ × ℕ => commutingOperatorValue x.1.game < (x.2.1 : ℝ) / x.2.2

/-- **The two values differ on some described game**, given the halting reduction and an upper
semidecider for the commuting-operator value. -/
theorem exists_quantumValue_lt_commutingOperatorValue (hred : HaltingReductionQuantum)
    (hU : CommutingUpperRE) :
    ∃ d : GameData, quantumValue d.game < commutingOperatorValue d.game := by
  by_contra hne
  push Not at hne
  have heq : ∀ d : GameData, commutingOperatorValue d.game = quantumValue d.game := fun d =>
    le_antisymm (hne d) (quantumValue_le_commutingOperatorValue d.game)
  obtain ⟨g, hg, hgap⟩ := hred
  -- non-halting is the pullback of the upper semidecider at the threshold `3/4`
  have hpull : REPred fun pc : Code =>
      commutingOperatorValue (g pc).game < ((3 : ℕ) : ℝ) / (4 : ℕ) :=
    Partrec.comp hU (hg.pair (Computable.const ((3, 4) : ℕ × ℕ)))
  have hiff : ∀ pc : Code,
      commutingOperatorValue (g pc).game < ((3 : ℕ) : ℝ) / (4 : ℕ) ↔ ¬ (pc.eval 0).Dom := by
    intro pc
    rw [heq]
    constructor
    · intro hlt hd
      have h1 := (hgap pc).1 hd
      rw [h1] at hlt
      norm_num at hlt
    · intro hd
      have h2 := (hgap pc).2 hd
      push_cast
      linarith
  exact ComputablePred.halting_problem_not_re 0 (hpull.of_eq hiff)

/-- **A commuting-operator correlation outside `C_qa`**, in the scenario of a described game,
given the halting reduction and an upper semidecider for the commuting-operator value. -/
theorem exists_mem_Cqc_not_mem_Cqa (hred : HaltingReductionQuantum) (hU : CommutingUpperRE) :
    ∃ nX nA : ℕ, ∃ p ∈ Cqc (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)),
      p ∉ Cqa (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) := by
  obtain ⟨d, hd⟩ := exists_quantumValue_lt_commutingOperatorValue hred hU
  have : Nonempty (CommutingOperatorStrategy (Fin (d.nX + 1)) (Fin (d.nX + 1))
      (Fin (d.nA + 1)) (Fin (d.nA + 1))) := by
    by_contra hE
    rw [not_nonempty_iff] at hE
    have h0 : commutingOperatorValue d.game = 0 := Real.iSup_of_isEmpty _
    linarith [quantumValue_nonneg d.game]
  obtain ⟨S, hS⟩ := exists_lt_of_lt_ciSup hd
  refine ⟨d.nX, d.nA, S.correlation, ⟨S, rfl⟩, fun hqa => ?_⟩
  have hle := payoff_le_quantumValue_of_mem_Cqa d.game hqa
  rw [← CommutingOperatorStrategy.value_eq_payoff] at hle
  exact absurd hS (not_lt.2 hle)

/-- **`C_qa ≠ C_qc`** in some finite scenario, given the halting reduction and an upper
semidecider for the commuting-operator value. -/
theorem exists_Cqa_ne_Cqc (hred : HaltingReductionQuantum) (hU : CommutingUpperRE) :
    ∃ nX nA : ℕ, Cqa (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) ≠
      Cqc (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) := by
  obtain ⟨nX, nA, p, hp, hnp⟩ := exists_mem_Cqc_not_mem_Cqa hred hU
  exact ⟨nX, nA, fun h => hnp (h ▸ hp)⟩

/-- **Tsirelson's problem, negative answer, conditionally** (blueprint `cor:tsirelson`):
`C_qa ⊊ C_qc` in some finite scenario, given the halting reduction, an upper semidecider for
the commuting-operator value, and closedness of `C_qc`. The scenario has equal question
alphabets `Fin (nX + 1)` and equal answer alphabets `Fin (nA + 1)` for both players. -/
theorem tsirelson_of_upperRE_of_isClosed (hred : HaltingReductionQuantum)
    (hU : CommutingUpperRE)
    (hclosed : ∀ nX nA : ℕ,
      IsClosed (Cqc (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)))) :
    ∃ nX nA : ℕ, Cqa (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) ⊂
      Cqc (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) := by
  obtain ⟨nX, nA, p, hp, hnp⟩ := exists_mem_Cqc_not_mem_Cqa hred hU
  exact ⟨nX, nA, Set.ssubset_iff_subset_ne.2
    ⟨Cqa_subset_Cqc_of_isClosed (hclosed nX nA), fun h => hnp (h ▸ hp)⟩⟩

end MIPRE
