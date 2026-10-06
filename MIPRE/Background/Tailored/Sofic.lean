/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Main
public import MIPRE.Tailored.Sofic.MainII

@[expose] public section

/-!
# The sofic value is not approximable, from tailored answer reduction

Paper I's measure-free corollary (Corollary I:2144) composed with paper II's main theorem as the
repository has it: a `TailoredAnswerReduction 5` gives the halting reduction to tailored games
(`tailored_halting_reduction_of_answerReduction`), and with Main Theorem II the sofic value of
subgroup tests is not approximable (`Sofic.not_sofValueApproximable`).
-/

namespace MIPRE.Tailored

/-- **The sofic value is not approximable, from tailored answer reduction.** -/
theorem not_sofValueApproximable_of_answerReduction (A : TailoredAnswerReduction 5) :
    ¬ SubgroupTestValue.SofValueApproximable :=
  Sofic.not_sofValueApproximable (tailored_halting_reduction_of_answerReduction A)

end MIPRE.Tailored

end
