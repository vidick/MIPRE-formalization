/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Density.Main

/-!
# Lin's tracial density theorem

Every commuting-operator correlation on finite common alphabets is an `ℓ¹`-limit of
tracially embeddable correlations (Lin, arXiv:2304.01940, Theorem 3.2; blueprint
`thm:tracial-density`), proved by the vendored development
`MIPRE/Background/Repetition/CommutingRepetition/` as
`CommutingRepetition.Density.tracialDensity`. The statement is that of the vendored
development (`CommutingRepetition.TracialDensityHypothesis`); it is not yet restated in
the vocabulary of this repository.
-/

namespace MIPRE.Repetition

/-- **Lin's tracial density theorem** (blueprint `thm:tracial-density`), in the vocabulary
of the vendored development. -/
theorem tracialDensity : CommutingRepetition.TracialDensityHypothesis :=
  CommutingRepetition.Density.tracialDensity

end MIPRE.Repetition
