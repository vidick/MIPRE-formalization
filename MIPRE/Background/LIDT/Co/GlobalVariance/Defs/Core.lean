/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
GlobalVariance/Defs/Core.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.ExpansionHypercubeGraph.Defs.Core
public import MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Defs.Core

@[expose] public section

/-!
# Section 8 global variance: core definitions

The counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Defs/Core.lean` in the
port of `planning/c6b-plan.md` (milestone M6, section "Port conventions").

The vendored file is classical throughout: the question and answer types of the Section 8
global-variance construction (axis-parallel line questions, point-pair questions, the
degree-bounded answers), the incident line-point distribution and the uniform polynomial
distribution, with their probability and `PMF` lemmas. None of them mentions a state, an
operator or a measurement, so none is ported: this file imports the vendored file, and the
ported files of `GlobalVariance` name its declarations through explicit
`open MIPStarRE.LDT.GlobalVariance (…)` lists. The vendored file's two anonymous instances
(`Fintype (AxisParallelLine params)` and `Nonempty (Polynomial params)`) come with the import.

The file mirrors the vendored module so that the ported tree keeps the vendored import graph:
`Co/GlobalVariance/Defs/Operators.lean` imports it as the vendored `Operators` imports `Core`,
and it imports `Co/ExpansionHypercubeGraph/Defs/Core.lean`, the counterpart of the vendored
file's import, where the ported variances live.

## Not ported

- `AxisParallelLineQuestion`: classical, imported.
- `PointPairQuestion`: classical, imported.
- `DegreeBoundedPolynomialAnswer`: classical, imported.
- `DegreeBoundedLineAnswer`: classical, imported.
- `pointOnLine`: classical, imported.
- `axisParallelLineQuestionParameter`: classical, imported.
- `axisParallelLineQuestionParameter_pointAt`: classical, imported.
- `axisParallelLineQuestionDistribution`: classical, imported.
- `axisParallelLineQuestionDistribution_support_nonempty`: classical, imported.
- `axisParallelLineQuestionDistribution_isProbability`: classical, imported.
- `axisParallelLineQuestionDistribution_toPMF`: classical, imported.
- `polynomialDistribution`: classical, imported.
- `polynomialDistribution_isProbability`: classical, imported.
- `polynomialDistribution_toPMF`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch06_variance.tex`
-/

end
