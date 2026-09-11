/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.Repetition.TenProofs.QuantumParallelRepetition
import MIPRE.Background.Repetition.Direct

/-!
# Direct parallel repetition for entangled strategies

The uniform exponential parallel repetition theorem for finite-dimensional tensor-product
strategies (blueprint `thm:direct-repetition-q`), in the vocabulary of this repository,
transferred from the vendored module `MIPRE/Background/Repetition/TenProofs/`
(OpenAI, *Ten advances in mathematics and theoretical computer science*, 2026,
Chapter 6): there is a universal `c > 0` such that for every game `G` with nonempty answer
alphabets and `ε = 1 - val*(G) > 0`, and every `n ≥ 1`,
`val*(G^{⊗n}) ≤ exp(-c·n·ε¹³/(ε + log(|A||B|)))`.

A game of this repository is literally a game of the vendored module (same question
weights, same `Bool` predicate), and so is its direct repetition. The values differ in
their strategy classes: `MIPRE.quantumValue` ranges over pure states and projective
measurements on `ℂ^dA ⊗ ℂ^dB`, the vendored `entangledValue` over density matrices and
POVMs on arbitrary finite-dimensional spaces. That they agree (purification and Naimark
dilation) is `quantumValue_eq_entangledValue` (blueprint `lem:povm-value-eq`), the one
statement here whose proof is still open.
-/

namespace MIPRE.Repetition

section Bridge

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- A game of this repository as a game of the vendored module. -/
def toTP (G : Game X Y A B) : QuantumParallelRepetition.Game X Y A B where
  questionWeight := G.μ
  weight_nonneg := G.μ_nonneg
  weight_normalized := G.μ_sum_one
  predicate := G.D

/-- The two direct repetitions are the same construction. -/
theorem toTP_repeat (G : Game X Y A B) (n : ℕ) :
    toTP (G.repeat n) = (toTP G).repeat n :=
  rfl

/-- The quantum value of this repository (pure states, projective measurements) equals
the entangled value of the vendored module (density matrices, POVMs): purification and
Naimark dilation (blueprint `lem:povm-value-eq`). -/
theorem quantumValue_eq_entangledValue (G : Game X Y A B) :
    quantumValue G = QuantumParallelRepetition.entangledValue (toTP G) := by
  sorry

end Bridge

/-- **Uniform exponential parallel repetition for entangled strategies** (blueprint
`thm:direct-repetition-q`; OpenAI 2026, Chapter 6, Theorem 1.1, via the vendored root
`QuantumParallelRepetition.distributionUniformExponential`): there is a universal constant
`c > 0` such that for every game `G` with nonempty answer alphabets and
`ε = 1 - val*(G) > 0`, and every `n ≥ 1`,
`val*(G^{⊗n}) ≤ exp(-c·n·ε¹³/(ε + log(|A||B|)))`. -/
theorem quantumValue_repeat_le :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B), Nonempty A → Nonempty B →
        0 < 1 - quantumValue G →
        ∀ n : ℕ, 0 < n →
          quantumValue (G.repeat n) ≤
            Real.exp
              (-(c * ((1 - quantumValue G) ^ 13 /
                ((1 - quantumValue G) +
                  Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))))
                * (n : ℝ)) := by
  obtain ⟨c, hc, h⟩ := QuantumParallelRepetition.distributionUniformExponential
  refine ⟨c, hc, ?_⟩
  intro X Y A B _ _ _ _ G hA hB hε n hn
  rw [quantumValue_eq_entangledValue, quantumValue_eq_entangledValue, toTP_repeat]
  rw [quantumValue_eq_entangledValue] at hε
  exact h (toTP G) hA hB hε n hn

end MIPRE.Repetition
