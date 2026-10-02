/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/LdSandwichLineOnePoint/EndpointEquivs.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.CommuteGHalfSandwich
public import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.EndpointEquivs

@[expose] public section

/-!
# Section 12 pasting: line one-point transport — endpoint equivalences

The reindexing equivalences of the line one-point transport: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/EndpointEquivs.lean`
in the port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

One declaration is about operators: `postprocessMeasurement`, which turns the postprocessing of
a measurement into a measurement. It reads no state, so it is generic over an ordered `⋆`-ring
`R` in place of the vendored matrix algebra `Op ι`: local measurements take `R = 𝔓`, joint ones
`R = K →L[ℂ] K`.

The other nine are equivalences of question and outcome types (splitting a sandwiched-line
question at a coordinate or a prefix, rotating and reversing a prefix tuple), with no operator
in them: this file imports the vendored file, and the ported files of `Pasting` name them through
explicit `open MIPStarRE.LDT.Pasting (…)` lists.

## Not ported

- `sandwichedLineQuestionSplitAtEquiv`: classical, imported.
- `sandwichedLineQuestionPrefixEquiv`: classical, imported.
- `prodPrefixReassocEquiv`: classical, imported.
- `sandwichedLineQuestionPrefixFstEquiv`: classical, imported.
- `pointTupleLastFrontEquiv`: classical, imported.
- `gHatTupleOutcomeLastFrontEquiv`: classical, imported.
- `pointTupleLastReverseEquiv`: classical, imported.
- `gHatTupleOutcomeLastReverseEquiv`: classical, imported.
- `gHatTupleOutcomePrefixLastEquiv`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPRE.LIDT.Co.Pasting

open MIPRE.LIDT.Co (Measurement postprocess)

/-- Turn a postprocessed submeasurement from a measurement into a measurement. -/
noncomputable def postprocessMeasurement
    {α β : Type*} {R : Type*}
    [Fintype α] [Fintype β] [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (B : Measurement α R) (f : α → β) : Measurement β R where
  toSubMeas := postprocess B.toSubMeas f
  total_eq_one := B.total_eq_one

end MIPRE.LIDT.Co.Pasting

end
