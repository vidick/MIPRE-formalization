/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Introspection.AuxiliaryDecisionCorrect
public import MIPRE.Tailored.Verifier
public import MIPRE.Tailored.Intro.Layout

@[expose] public section

/-!
# The input's question and answer split at an auxiliary answer

The introspection verifier's source decider is run on the input verifier `W` at index `2^n`, on
the questions `toBits (pull (firstEmbedding hs) y)` read off the `y`-registers of the two
Introspect answers (`AuxiliaryDecision.sourcePredicate`); the honest strategy measures the
input's strategy at the same question (`SourcePadding.strategy`, and the numbering of
`CanonicalGame` cancels on the way back). A Read answer carries the input answer of the
Introspect answer it is compared with, at the same register, and a Sample answer at the seed
`z` that of the question `L_w(z)` (`AuxiliaryChecks.sampling`).

So at an auxiliary answer the input question is `srcQuestion t y`, and the tailored layout
(`MIPRE.Tailored.Intro.enc`) splits the input's answer there by the lengths the input's
answer-length calculator gives (`srcSplitR`, `srcSplitL`): computable from the readable register
alone, as the linear-constraints processor needs.
-/

namespace MIPRE.Tailored.Intro

open Cost MIPRE.Introspection

variable (V : TailoredVerifier 7) (W : Verifier 7) {n Q : ℕ} (hs : W.sampler.dim (2 ^ n) ≤ Q)

/-- The input question of an auxiliary answer, read off its register: the register's first
`dim` bits at Introspect, Read and Hide, and those of `L_w(z)` at Sample. -/
noncomputable def srcQuestion : AuxType 7 × Bool → BitStr → BitStr
  | (.sample, w), z => CL.toBits (CL.pull (AuxiliaryProgram.firstEmbedding hs)
      ((AuxiliaryDecision.padded W hs w).eval (CL.ofBits Q z)))
  | _, y => CL.toBits (CL.pull (AuxiliaryProgram.firstEmbedding hs) (CL.ofBits Q y))

/-- The number of readable bits of the input's answer at an auxiliary answer. -/
noncomputable def srcSplitR (t : AuxType 7 × Bool) (y : BitStr) : ℕ :=
  V.lenOf (2 ^ n) (srcQuestion W hs t y) false

/-- The number of linear bits of the input's answer at an auxiliary answer. -/
noncomputable def srcSplitL (t : AuxType 7 × Bool) (y : BitStr) : ℕ :=
  V.lenOf (2 ^ n) (srcQuestion W hs t y) true

end MIPRE.Tailored.Intro

end
