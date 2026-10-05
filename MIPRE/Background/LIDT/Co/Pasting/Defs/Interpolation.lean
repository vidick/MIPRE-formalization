/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Defs/
Interpolation.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Defs.Tuples
public import MIPStarRE.LDT.Pasting.Defs.Interpolation

@[expose] public section

/-!
# Section 12 — Definitions: interpolation

Interpolation helpers extracted from `Pasting.Defs`: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Defs/Interpolation.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored file is classical throughout: the tails of point and outcome tuples, the fallback
polynomial `h₀`, the extraction of a slice polynomial from a genuine completed-slice outcome,
the degree bound on Lagrange basis polynomials, the decidability of interpolation eligibility,
the `d + 1`-point interpolation support and its witness, and Lagrange interpolation of `m + 1`
variables from `d + 1` slices with its degree bound. None of them mentions a state, an operator
or a measurement, so none is ported: this file imports the vendored file, and the ported files
of `Pasting` name its declarations through explicit `open MIPStarRE.LDT.Pasting (…)` lists. The
vendored instance `interpolationEligible_decidablePred` comes with the import.

The file mirrors the vendored module so that the ported tree keeps the vendored import graph:
`Co/Pasting/Defs/Families.lean` imports it as the vendored `Families` imports `Interpolation`,
and it imports `Co/Pasting/Defs/Tuples.lean`, the counterpart of the vendored file's import. The
vendored file's other import, `LDT/Basic/LinePolynomialEmbedding.lean`, is classical and comes
with the vendored file.

## Not ported

- `pointTupleTail`: classical, imported.
- `gHatTupleOutcomeTail`: classical, imported.
- `fallbackInterpolatedPolynomial`: classical, imported.
- `extractSlicePoly`: classical, imported.
- `natDegree_lagrangeBasis_le_card_sub_one`: classical, imported.
- `interpolationEligible_decidablePred`: classical, imported.
- `InterpolationSupportWitness`: classical, imported.
- `InterpolationSupportWitness.support`: classical, imported.
- `InterpolationSupportWitness.subset_support`: classical, imported.
- `InterpolationSupportWitness.card_eq`: classical, imported.
- `interpolationSupportWitness`: classical, imported.
- `interpolateCompletedSlicesFromSupport_degree`: classical, imported.
- `interpolateCompletedSlicesFromSupport`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

end
