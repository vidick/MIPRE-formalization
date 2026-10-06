/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.MainII
public import MIPRE.Tailored.Sofic.Measure.MainTheorem

@[expose] public section

/-!
# The Aldous–Lyons conjecture is false, from a halting reduction to tailored games

Corollary I:2144 assembled: Main Theorem II (`mainTheoremII`, gap `gapK`) and Main Theorem I
(`Measure.aldous_lyons_false_of`, through the ergodic value and its upper approximation by
pseudo-subgroup polytopes) leave a halting reduction to tailored games as the only hypothesis.
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue

/-- **The Aldous–Lyons conjecture is false** (Corollary I:2144), from a halting reduction to
tailored games. -/
theorem aldous_lyons_false (hred : TailoredHaltingReduction) : ¬ AldousLyons :=
  Measure.aldous_lyons_false_of primrec_gapK mainTheoremII hred

end MIPRE.Tailored.Sofic

end
