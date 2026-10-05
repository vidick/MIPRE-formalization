/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
ComparisonLemmas/LineInterpolation/Core.lean, to the symmetric model of `planning/c6b-plan.md`;
not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.ComparisonLemmas.Common
public import MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.Core

@[expose] public section

/-!
# Line interpolation: core API

The counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/Core.lean` in the
port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored file is classical throughout: the interpolation-support, vertical-line restriction
and completed-slice interpolation lemmas of `ld-pasting.tex` (two distinct low-degree line
polynomials differ on any `d + 1` distinct heights, a non-global tuple of slice answers
disagrees somewhere with its interpolant, the chosen interpolation support and its card, and
the interpolant restricted at a support height is that slice's answer). None of them mentions a
state, an operator or a measurement, so none is ported: this file imports the vendored file, and
the ported files of `LineInterpolation` name its declarations through explicit
`open MIPStarRE.LDT.Pasting (…)` lists.

The file mirrors the vendored module so that the ported tree keeps the vendored import graph: it
imports `Co/Pasting/ComparisonLemmas/Common.lean`, the counterpart of the vendored file's only
import, and the ported files of `LineInterpolation` import it as the vendored ones import `Core`.

## Not ported

- `axisLinePolynomial_ne_gives_support_eval_ne`: classical, imported.
- `nonglobal_gives_slice_mismatch_against_interpolant`: classical, imported.
- `interpolationSupportSubset`: classical, imported.
- `interpolationSupportSubset_subset`: classical, imported.
- `interpolationSupportSubset_card`: classical, imported.
- `restrictToAxisParallelLine_apply`: classical, imported.
- `restrictToVerticalLine_eval_eq_restrictAtHeight_eval`: classical, imported.
- `interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_of_mem`: classical,
  imported.
- `interpolateCompletedSlices_restrictAtHeight_eq_get_of_mem_supportSubset`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

end
