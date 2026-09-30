/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Background.Introspection.RestrictedSoundness
public import MIPRE.Background.Introspection.ExplicitGame
public import MIPRE.Foundations.Introspection.RestrictedErrorBounds
public import MIPRE.Foundations.Introspection.SourcePaddingValue

@[expose] public section

/-! # The uniform profile constants of conditional soundness

The ordered-edge loss of the complete introspection type graph and the uniform coefficient after
restriction and the finite soundness argument. The numbered source theorem
(`NumberedSoundness.quantumValue_ge_of_errorProfile`) absorbs a two-term QLD error profile with
them.

Phase 4 of `planning/mipco-track.md` removed the callback forms of conditional soundness that
followed here, which had no consumer; the numbered theorem takes an extraction for its specific
restricted strategy instead.
-/

noncomputable section
namespace MIPRE.Introspection.RestrictedSoundness
open Matrix Finset Classical BinaryComplete
set_option linter.unusedSectionVars false

/-- Ordered-edge loss in the complete introspection type graph. -/
def edgeCount (ℓ : ℕ) : ℝ :=
  (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card

theorem edgeCount_one_le (ℓ : ℕ) : 1 ≤ edgeCount ℓ := by
  have h : 1 ≤ (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card :=
    (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) ℓ).card_pos
  unfold edgeCount
  exact_mod_cast h

/-- Uniform coefficient after restriction and the finite soundness argument. -/
def profileCoefficient (ℓ : ℕ) (a b : ℝ) : ℝ :=
  powerCoefficient (validSoundnessCoefficient ℓ (edgeCount ℓ) *
    (max 1 ((edgeCount ℓ) ^ b)) ^ rootExponent (6 * ℓ + 2)) a
      (rootExponent (6 * ℓ + 2))

theorem profileCoefficient_one_le (ℓ : ℕ) (a b : ℝ) :
    1 ≤ profileCoefficient ℓ a b := one_le_powerCoefficient _ _ _

end MIPRE.Introspection.RestrictedSoundness
end

end
