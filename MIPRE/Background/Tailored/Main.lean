/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Compose
public import MIPRE.Tailored.Class
public import MIPRE.Background.Tailored.Intro.Inhabit
public import MIPRE.Background.Tailored.Repetition.Stage

@[expose] public section

/-!
# `TMIP* = RE` from tailored answer reduction

Phase 5 of `planning/aldous-lyons-track.md`. Question reduction (`TailoredIntrospection 7`,
`Intro.Inhabit.tailoredIntrospection`) and parallel repetition (`TailoredRepetition 7`,
`tailoredRepetition`) are inhabited, so `TailoredGapCompression.ofTailoredPipeline` turns a
`TailoredAnswerReduction 5` into a tailored gap compression, and the halting reduction of
`MIPRE/Tailored/Halting/` and the class theorem of `MIPRE/Tailored/Class.lean` follow from it:
paper II's main theorem `thm:tailored_MIP*=RE` (II:1505) rests on answer reduction alone.
-/

namespace MIPRE.Tailored

open TailoredGameValue

/-- **Tailored compression from answer reduction**: the composition with the inhabited question
reduction and parallel repetition. -/
noncomputable def TailoredGapCompression.ofAnswerReduction (A : TailoredAnswerReduction 5) :
    TailoredGapCompression 7 :=
  .ofTailoredPipeline Intro.Inhabit.tailoredIntrospection A (tailoredRepetition 7)

/-- **`thm:tailored_MIP*=RE` from tailored answer reduction** (II:1505): a
`TailoredAnswerReduction 5` gives the halting reduction to tailored games. -/
theorem tailored_halting_reduction_of_answerReduction (A : TailoredAnswerReduction 5) :
    TailoredHaltingReduction :=
  tailored_halting_reduction_of (TailoredGapCompression.ofAnswerReduction A)

/-- **`TMIP* = RE` from tailored answer reduction** (II:787, II:6997). -/
theorem tmipStarComputable_eq_re_of_answerReduction (A : TailoredAnswerReduction 5) :
    TMIPStarComputable = IsRE :=
  tmipStarComputable_eq_re_of (TailoredGapCompression.ofAnswerReduction A)

end MIPRE.Tailored

end
