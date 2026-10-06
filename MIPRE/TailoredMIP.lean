/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.TailoredGameValue
public import MIPRE.Background.Tailored.Sofic
public import MIPRE.Background.Tailored.AnswerReduction.ArContract
public import MIPRE.Tailored.ClassVerifier

@[expose] public section

/-!
# `TMIP* = RE`, and the Aldous–Lyons conjecture is false

The main theorem of *The Aldous–Lyons Conjecture II: Undecidability* (Bowen–Chapman–Vidick,
arXiv:2501.00173, `thm:tailored_MIP*=RE`, II:1505), proved:
`TailoredGameValue.tailored_halting_reduction` is the Mathlib-only statement
`TailoredGameValue.TailoredHaltingReduction` of `MIPRE/TailoredGameValue.lean` (blueprint
`thm:tmip-re`). Tailored compression is built from question reduction
(`Intro.Inhabit.tailoredIntrospection`), answer reduction
(`AnsRed.Typed.tailoredAnswerReduction`) and parallel repetition (`tailoredRepetition`), and the
class theorems follow for both readings of `TMIP*`.

With paper I (*The Aldous–Lyons Conjecture I: Subgroup Tests*, Bowen–Chapman–Lubotzky–Vidick,
arXiv:2408.00110), the sofic value of subgroup tests is not approximable and the Aldous–Lyons
conjecture is false: `SubgroupTestValue.aldous_lyons_false` is the negation of the Mathlib-only
statement `SubgroupTestValue.AldousLyons` of `MIPRE/SubgroupTestValue.lean` (blueprint
`thm:aldous-lyons-false`).
-/

/-- **Tailored gap compression** (blueprint `thm:tailored-compression-target`), inhabited. -/
noncomputable def MIPRE.Tailored.tailoredGapCompression : MIPRE.Tailored.TailoredGapCompression 7 :=
  .ofAnswerReduction MIPRE.Tailored.AnsRed.Typed.tailoredAnswerReduction

namespace TailoredGameValue

/-- **`TMIP* = RE`** (paper II, `thm:tailored_MIP*=RE`, II:1505; blueprint `thm:tmip-re`): the
halting problem reduces to tailored games, with a perfect ZPC strategy on the machines that halt
and synchronous value at most `1/2` on the others. -/
theorem tailored_halting_reduction : TailoredHaltingReduction :=
  MIPRE.Tailored.tailored_halting_reduction_of_answerReduction
    MIPRE.Tailored.AnsRed.Typed.tailoredAnswerReduction

end TailoredGameValue

namespace MIPRE.Tailored

/-- **The halting problem reduces to tailored games, in the quantum value.** -/
theorem tailored_halting_reduction_quantum :
    ∃ g : Nat.Partrec.Code → TailoredGameValue.TailoredGameData, Computable g ∧
      ∀ c : Nat.Partrec.Code,
        (HaltingGameValue.HaltsOnEmptyInput c → (g c).HasPerfectZPC) ∧
        (¬ HaltingGameValue.HaltsOnEmptyInput c → quantumValue (g c).game ≤ 1 / 2) :=
  tailored_halting_reduction_quantum_of tailoredGapCompression

/-- **`TMIP* = RE`, computable class** (II:787, II:6997). -/
theorem tmipStarComputable_eq_re : TMIPStarComputable = IsRE :=
  tmipStarComputable_eq_re_of tailoredGapCompression

/-- **`TMIP* = RE`, the paper's polynomial-time class** (II:787). -/
theorem tmipStar_eq_re : TMIPStar = IsRE :=
  tmipStar_eq_re_of tailoredGapCompression

end MIPRE.Tailored

namespace SubgroupTestValue

/-- **The sofic value of subgroup tests is not approximable** (paper I, Corollary I:2144,
measure-free). -/
theorem not_sofValueApproximable : ¬ SofValueApproximable :=
  MIPRE.Tailored.Sofic.not_sofValueApproximable TailoredGameValue.tailored_halting_reduction

/-- **The Aldous–Lyons conjecture is false** (paper I, Corollary I:2144, with paper II's main
theorem; blueprint `thm:aldous-lyons-false`). -/
theorem aldous_lyons_false : ¬ AldousLyons :=
  MIPRE.Tailored.Sofic.aldous_lyons_false TailoredGameValue.tailored_halting_reduction

end SubgroupTestValue

end
